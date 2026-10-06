#!/usr/bin/env python3
"""Inspect insertion IR, specialized C, ARM64 assembly, and benchmark timing."""

import argparse
import hashlib
import importlib.util
import json
import platform
import re
import shlex
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("Benchmarks/results"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    output = root / args.output
    output.mkdir(parents=True, exist_ok=True)
    spec = importlib.util.spec_from_file_location("contains_inspection", root / "Benchmarks/inspect.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    subprocess.run(["lake", "build", "insertBench"], cwd=root, check=True)
    lean = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip()
    ir = subprocess.check_output(["lake", "env", "lean", "Benchmarks/InspectInsertIR.lean"], cwd=root, text=True)
    (output / "insert.ir.txt").write_text(ir)
    c_path = root / ".lake/build/ir/Benchmarks/Insert.c"
    source = c_path.read_text()
    selected, timers, hot, loops, helpers = [], [], [], [], []
    cached_checks = []
    for name, body in helper.c_functions(source):
        timed = body.count("lean_io_mono_nanos_now()") == 2
        if timed:
            batch = "nativeBatch" if "measureNative" in name else "totalBatch"
            start, stop = body.index("lean_io_mono_nanos_now()"), body.rindex("lean_io_mono_nanos_now()")
            if not start < body.index(batch + "_", start) < body.index("lean_runtime_hold", start) < stop:
                raise RuntimeError(f"Incorrect C timer order: {name}")
            timers.append(name)
        traversal = (name.startswith("lp_VerifiedHAMT_Lean_PersistentHashMap_insertAux___at") or
                     name.startswith("lp_VerifiedHAMT_VerifiedHAMT_insertNodeCached___at"))
        traversal = traversal and "___redArg(" in body.splitlines()[0] and "lean_obj_tag" in body
        if traversal:
            hot.append(name)
            if "VerifiedHAMT_insertNodeCached___at" in name:
                if "lean_apply_" in body or "lean_alloc_closure" in body:
                    raise RuntimeError(f"Indirect call or closure remains in cached traversal: {name}")
                cached_checks.append(name)
        auxiliary = name.startswith((
            "lp_VerifiedHAMT_Lean_PersistentHashMap_insertAtCollisionNodeAux___at",
            "lp_VerifiedHAMT_VerifiedHAMT_insertCollision___at",
            "lp_VerifiedHAMT_VerifiedHAMT_insertNoExpand___at",
            "lp_VerifiedHAMT_VerifiedHAMT_rebuildCached___at",
        )) and "___redArg(" in body.splitlines()[0]
        if auxiliary:
            helpers.append(name)
        # Keep the actual per-round loop so that repeated round calls and salt
        # progression can be checked, not only their measurement wrappers.
        batch_loop = ("Range_forIn_x27_loop___at" in name and "Batch___at" in name and
                      "___boxed" not in name and "Round" in body and "digest" in body)
        if batch_loop:
            loops.append(name)
        if timed or traversal or batch_loop or auxiliary:
            selected.append((name, body))
    if (len(timers), len(hot), len(loops), len(helpers), len(cached_checks)) != (6, 4, 4, 8, 2):
        raise RuntimeError(f"Review changed specialization: {len(timers)} timers, {len(hot)} traversals, {len(loops)} batch loops, {len(helpers)} helpers, {len(cached_checks)} cached checks")
    (output / "insert.c.txt").write_text("// Extracts from .lake/build/ir/Benchmarks/Insert.c\n\n" +
                                        "\n\n".join(body for _, body in selected) + "\n")

    trace_path = root / ".lake/build/ir/Benchmarks/Insert.c.o.export.trace"
    trace = json.loads(trace_path.read_text())
    command = next(item["message"][3:] for item in trace["log"] if item["message"].startswith(".> "))
    compile_args = shlex.split(command)
    assembly_path = root / ".lake/inspection/Insert.s"
    assembly_path.parent.mkdir(parents=True, exist_ok=True)
    compile_args[compile_args.index("-c")] = "-S"
    compile_args[compile_args.index("-o") + 1] = str(assembly_path)
    subprocess.run(compile_args, cwd=root, check=True)
    assembly = assembly_path.read_text()
    asm_selected, asm_timers = [], []
    if platform.system() == "Darwin" and "arm64-apple" in lean:
        for name, _ in selected:
            match = re.search(r"^_" + re.escape(name) + ":", assembly, re.M)
            if match is None:
                raise RuntimeError(f"Missing assembly symbol: {name}")
            end = assembly.index(".cfi_endproc", match.end()) + len(".cfi_endproc")
            body = assembly[match.start():end]
            if name in cached_checks and re.search(r"\bbl\s+_lean_apply_", body):
                raise RuntimeError(f"Indirect application remains in cached assembly: {name}")
            if name in timers:
                calls = re.findall(r"^\s+bl\s+(\S+)", body, re.M)
                clocks = [i for i, call in enumerate(calls) if call == "_lean_io_mono_nanos_now"]
                batches = [i for i, call in enumerate(calls) if "nativeBatch" in call or "totalBatch" in call]
                if len(clocks) != 2 or len(batches) != 1 or not clocks[0] < batches[0] < clocks[1]:
                    raise RuntimeError(f"Incorrect assembly timer order: {name}")
                asm_timers.append(name)
            asm_selected.append(body)
        (output / "insert.arm64.txt").write_text("; Same Lake clang flags, replacing -c with -S.\n\n" +
                                                "\n\n".join(asm_selected) + "\n")
    metadata = {
        "lean": lean,
        "source_sha256": {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in
                          ("VerifiedHAMT/Insert.lean", "VerifiedHAMT/Basic.lean", "Benchmarks/Insert.lean",
                           "Benchmarks/InspectInsertIR.lean", "Benchmarks/inspect_insert.py")},
        "generated_c_sha256": hashlib.sha256(c_path.read_bytes()).hexdigest(),
        "assembly_command": compile_args,
        "c_timer_order_checked": timers, "arm64_timer_order_checked": asm_timers,
        "specialized_traversals": hot, "round_loops_for_inspection": loops,
        "specialized_helpers": helpers,
        "cached_traversals_without_closures_or_indirect_calls": cached_checks,
    }
    (output / "insert-compiler.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Saved insertion compiler evidence to {output}")
    print(f"Checked {len(timers)} C / {len(asm_timers)} ARM64 timer functions; extracted {len(hot)} traversals and {len(loops)} round loops.")


if __name__ == "__main__":
    main()
