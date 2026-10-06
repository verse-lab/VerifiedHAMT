#!/usr/bin/env python3
"""Inspect keys-only size access, proof erasure, fusion, ownership, and timed workers."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shlex
import subprocess


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_collision_size_before_insert(name, body):
    """A live alias of the old keys across insertion defeats array reuse."""
    calls = list(re.finditer(r"\w+ = \w*insertCollisionAux\w*\([^;]+;", body))
    if len(calls) != 1:
        raise RuntimeError(f"Review changed collision insertion path: {name}")
    before = body[:calls[0].start()]
    projections = list(re.finditer(r"(\w+) = lean_ctor_get\(\w+, 0\);", before))
    if not projections:
        raise RuntimeError(f"Missing old collision keys: {name}")
    projection = projections[-1]
    keys = re.escape(projection[1])
    tail = before[projection.end():]
    if not re.search(r"= lean_array_get_size\(" + keys + r"\);", tail):
        raise RuntimeError(f"Old size read moved past collision insertion: {name}")
    if re.search(r"lean_inc(?:_ref)?\(" + keys + r"\);", tail):
        raise RuntimeError(f"Old keys retained across collision insertion: {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("Benchmarks/results/without-vals-ir"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    output = root / args.output
    output.mkdir(parents=True, exist_ok=True)
    helper = load_module("c_inspection", root / "Benchmarks/inspect.py")
    reuse = load_module("set_inspection", root / "Benchmarks/inspect_set.py")
    subprocess.run(["lake", "build", "setWithoutValArrayBench",
                    "VerifiedHAMTTests.SetWithoutValArrayIR", "VerifiedHAMTTests.ReleaseIR"], cwd=root, check=True)
    for check in ("SetWithoutValArrayIR", "ReleaseIR"):
        subprocess.run(["lake", "env", "lean", f"VerifiedHAMTTests/{check}.lean"], cwd=root, check=True)
    ir = subprocess.check_output(["lake", "env", "lean", "Benchmarks/InspectSetWithoutValArrayIR.lean"],
                                 cwd=root, text=True)
    (output / "keys-only.ir.txt").write_text(ir)
    prefix = "lp_VerifiedHAMT_VerifiedHAMT_SetWithoutValArray_Raw_"
    paths = [root / ".lake/build/ir/VerifiedHAMT/SetWithoutValArray/InsertSized.c",
             root / ".lake/build/ir/Benchmarks/SetWithoutValArray.c"]
    selected, generic, specialized, timers = [], [], [], []
    for index, path in enumerate(paths):
        for name, body in helper.c_functions(path.read_text()):
            sized = (name.startswith((prefix + "insertSizedRaw___", prefix + "insertSizedNoExpand___"))
                     and "___boxed" not in name and "lean_obj_tag" in body)
            if sized:
                reuse.check_sized_reuse(name, body)
                check_collision_size_before_insert(name, body)
                if re.search(r"\w+(?:contains|keyCount|keyList)\w*\(", body):
                    raise RuntimeError(f"Separate lookup/count in worker: {name}")
                if index == 1:
                    if "lean_apply_" in body or "lean_alloc_closure" in body:
                        raise RuntimeError(f"Closure/indirect call in timed specialization: {name}")
                    specialized.append(name)
                else:
                    generic.append(name)
            timed = index == 1 and body.count("lean_io_mono_nanos_now()") == 2
            if timed:
                start = body.index("lean_io_mono_nanos_now()")
                stop = body.rindex("lean_io_mono_nanos_now()")
                if not start < body.index("lean_apply_1", start) < body.index("lean_runtime_hold", start) < stop:
                    raise RuntimeError(f"Batch escaped the clock interval: {name}")
                timers.append(name)
            if sized or timed:
                selected.append((name, body))
    if (len(generic), len(specialized), len(timers)) != (2, 4, 1):
        raise RuntimeError("Unexpected worker/timer count; review specialization")
    (output / "keys-only.c.txt").write_text("\n\n".join(body for _, body in selected) + "\n")

    # Use exactly Lake's C compiler flags, changing only -c to -S and its output.
    c_path = paths[1]
    trace = json.loads(Path(str(c_path) + ".o.export.trace").read_text())
    command = next(entry["message"][3:] for entry in trace["log"] if entry["message"].startswith(".> "))
    compile_args = shlex.split(command)
    asm_path = output / "benchmark.s"
    compile_args[compile_args.index("-c")] = "-S"
    compile_args[compile_args.index("-o") + 1] = str(asm_path)
    subprocess.run(compile_args, cwd=root, check=True)
    assembly = asm_path.read_text()
    lean = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip()
    asm_checked = []
    if "arm64-apple" in lean:
        for name in specialized:
            match = re.search(r"^_" + re.escape(name) + ":", assembly, re.M)
            if match is None:
                raise RuntimeError(f"Missing assembly worker: {name}")
            end = assembly.index(".cfi_endproc", match.end())
            body = assembly[match.start():end]
            if re.search(r"\b(?:bl|b)\s+_(?:lean_apply_|lean_alloc_closure)", body) or re.search(r"\bblr\s", body):
                raise RuntimeError(f"Closure/indirect call in ARM64 worker: {name}")
            asm_checked.append(name)
    metadata = {
        "lean": lean,
        "ir_checks": "proof erasure, projection-only size, no product allocation or second lookup, "
                     "direct Nat calls, slot clearing before recursion",
        "generic_workers_with_reuse": generic,
        "collision_ownership_checks": "old array size read before insertion; no retained array alias",
        "timed_nat_and_name_workers_with_reuse_and_direct_calls": specialized,
        "c_timers_checked": timers,
        "arm64_workers_checked": asm_checked,
        "assembly_command": compile_args,
        "generated_c_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
    }
    (output / "compiler.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Passed IR checks; C reuse in {len(generic)} generic and {len(specialized)} timed workers; "
          f"{len(asm_checked)} ARM64 workers checked. Evidence: {output}")


if __name__ == "__main__":
    main()
