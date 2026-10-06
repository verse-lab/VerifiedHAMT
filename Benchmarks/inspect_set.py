#!/usr/bin/env python3
"""Inspect Set wrapper erasure, actual timed specializations, and round loops."""

import argparse
import hashlib
import importlib.util
import json
import platform
import re
import shlex
import subprocess
from pathlib import Path


def check_sized_reuse(name, body):
    """Guard the ownership behavior lost by the earlier Bool/Node implementation."""
    fields = re.search(r"(\w+) = lean_ctor_get\((\w+), 0\);", body)
    if fields is None:
        raise RuntimeError(f"Missing sized-map projection: {name}")
    node, carrier = fields.groups()
    branch = re.search(r"if \(lean_obj_tag\(" + re.escape(node) + r"\) == 0\)", body)
    if branch is None:
        raise RuntimeError(f"Review changed entries branch: {name}")
    start = body.index("{", branch.end())
    depth = 1
    end = start + 1
    while depth:
        depth += (body[end] == "{") - (body[end] == "}")
        end += 1
    entries = body[start:end]
    if f"lean_is_exclusive({node})" not in entries:
        raise RuntimeError(f"Entries constructor no longer available for reuse: {name}")
    if f"lean_is_exclusive({carrier})" not in body:
        raise RuntimeError(f"Input size container no longer available for reuse: {name}")
    results = re.findall(r"(\w+) = " + re.escape(name) + r"\(", entries)
    if not results or any(f"lean_is_exclusive({result})" not in entries for result in results):
        raise RuntimeError(f"Recursive size result no longer available for reuse: {name}")


def inspect(root, output, helper, stem, lean):
    inserting = stem == "SetInsert"
    label = "set-insert" if inserting else "set-contains"
    c_path = root / f".lake/build/ir/Benchmarks/{stem}.c"
    source = c_path.read_text()
    selected, timers, hot, loops, cached, sized = [], [], [], [], [], []
    prefixes = (
        "lp_VerifiedHAMT_Lean_PersistentHashMap_insertAux___at",
        "lp_VerifiedHAMT_VerifiedHAMT_insertNodeCached___at",
        "lp_VerifiedHAMT_VerifiedHAMT_insertSizedRaw___at",
        "lp_VerifiedHAMT_VerifiedHAMT_insertSizedNoExpand___at",
    ) if inserting else (
        "lp_VerifiedHAMT_Lean_PersistentHashMap_containsAux___at",
        "lp_VerifiedHAMT_VerifiedHAMT_containsNode___at",
    )
    for name, body in helper.c_functions(source):
        timed = body.count("lean_io_mono_nanos_now()") == 2
        if timed:
            batch = "nativeBatch" if "measureNative" in name else "totalBatch"
            start = body.index("lean_io_mono_nanos_now()")
            stop = body.rindex("lean_io_mono_nanos_now()")
            if not start < body.index(batch + "_", start) < body.index("lean_runtime_hold", start) < stop:
                raise RuntimeError(f"Incorrect C timer order: {name}")
            timers.append(name)
        traversal = (name.startswith(prefixes) and "lean_obj_tag" in body and
                     "___redArg(" in body.splitlines()[0])
        if traversal:
            hot.append(name)
            if name.startswith(("lp_VerifiedHAMT_VerifiedHAMT_insertNodeCached___at",
                                "lp_VerifiedHAMT_VerifiedHAMT_insertSizedRaw___at",
                                "lp_VerifiedHAMT_VerifiedHAMT_insertSizedNoExpand___at")):
                if "lean_apply_" in body or "lean_alloc_closure" in body:
                    raise RuntimeError(f"Indirect call or closure in cached traversal: {name}")
                if re.search(r"VerifiedHAMT_contains(?:Node|At)?___", body):
                    raise RuntimeError(f"Separate membership lookup in insertion: {name}")
                cached.append(name)
                if name.startswith("lp_VerifiedHAMT_VerifiedHAMT_insertSized"):
                    check_sized_reuse(name, body)
                    sized.append(name)
        loop = (inserting and "Range_forIn_x27_loop___at" in name and "Batch___at" in name and
                "___boxed" not in name and "Round" in body and "digest" in body)
        if loop:
            # Check data flow, not just the presence of a modulus somewhere:
            # the loop index determines the start passed to the insertion round.
            rotation = re.search(r"(\w+) = lean_nat_mod\((\w+), (\w+)\);", body)
            round_call = re.search(r"= (\w+(?:nativeRound|totalRound)\w*)\(([^;]+)\);", body)
            if rotation is None or round_call is None:
                raise RuntimeError(f"Missing varying round call: {name}")
            if rotation[1] not in round_call[2].split(", "):
                raise RuntimeError(f"Rotation not passed to round: {name}")
            if not re.search(r"lean_nat_add\(" + re.escape(rotation[2]) + r",", body):
                raise RuntimeError(f"Rotation does not depend on incremented loop index: {name}")
            if "goto _start;" not in body:
                raise RuntimeError(f"Missing round-loop back edge: {name}")
            loops.append(name)
        if timed or traversal or loop:
            selected.append((name, body))
    expected = (6, 8, 4, 6) if inserting else (8, 4, 0, 0)
    actual = (len(timers), len(hot), len(loops), len(cached))
    if actual != expected:
        raise RuntimeError(f"Review changed {stem} specialization: {actual} != {expected}")
    (output / f"{label}.c.txt").write_text(f"// Extracts from {c_path.relative_to(root)}\n\n" +
                                          "\n\n".join(body for _, body in selected) + "\n")

    trace = json.loads(Path(str(c_path) + ".o.export.trace").read_text())
    command = next(item["message"][3:] for item in trace["log"] if item["message"].startswith(".> "))
    compile_args = shlex.split(command)
    assembly_path = root / f".lake/inspection/{stem}.s"
    assembly_path.parent.mkdir(parents=True, exist_ok=True)
    compile_args[compile_args.index("-c")] = "-S"
    compile_args[compile_args.index("-o") + 1] = str(assembly_path)
    subprocess.run(compile_args, cwd=root, check=True)
    assembly = assembly_path.read_text()
    asm_selected, asm_timers, asm_loops = [], [], []
    if platform.system() == "Darwin" and "arm64-apple" in lean:
        for name, _ in selected:
            match = re.search(r"^_" + re.escape(name) + ":", assembly, re.M)
            if match is None:
                raise RuntimeError(f"Missing assembly symbol: {name}")
            end = assembly.index(".cfi_endproc", match.end()) + len(".cfi_endproc")
            body = assembly[match.start():end]
            calls = re.findall(r"^\s+bl\s+(\S+)", body, re.M)
            if name in cached and any(call.startswith("_lean_apply_") for call in calls):
                raise RuntimeError(f"Indirect application in cached assembly: {name}")
            if name in timers:
                clocks = [i for i, call in enumerate(calls) if call == "_lean_io_mono_nanos_now"]
                batches = [i for i, call in enumerate(calls) if "nativeBatch" in call or "totalBatch" in call]
                if len(clocks) != 2 or len(batches) != 1 or not clocks[0] < batches[0] < clocks[1]:
                    raise RuntimeError(f"Incorrect assembly timer order: {name}")
                asm_timers.append(name)
            if name in loops:
                rounds = [i for i, call in enumerate(calls) if "nativeRound" in call or "totalRound" in call]
                digests = [i for i, call in enumerate(calls) if "digest" in call]
                # Clang may duplicate the round call across small/big-Nat
                # bounds-check paths; they must still call the same round.
                if (not rounds or not digests or rounds[0] >= digests[0] or
                        len({calls[i] for i in rounds}) != 1 or
                        len({calls[i] for i in digests}) != 1):
                    raise RuntimeError(f"Round/digest calls missing in assembly loop: {name}")
                if not re.search(r"\b(?:udiv|msub)\b|_lean_nat_big_mod", body):
                    raise RuntimeError(f"Round rotation missing in assembly: {name}")
                # The optimizing C compiler must keep a backwards loop branch.
                back_edges = [m for m in re.finditer(r"^\s+b(?:\.[a-z]+)?\s+(LBB\w+)", body, re.M)
                              if 0 <= body.find(m[1] + ":") < m.start()]
                if not back_edges:
                    raise RuntimeError(f"Missing assembly loop back edge: {name}")
                asm_loops.append(name)
            asm_selected.append(body)
        (output / f"{label}.arm64.txt").write_text(helper.redact_paths(
            "; Same Lake clang flags, replacing -c with -S.\n\n" +
            "\n\n".join(asm_selected) + "\n", root))
    print(f"{stem}: checked {len(timers)} C / {len(asm_timers)} ARM64 timers, "
          f"{len(loops)} varying C / {len(asm_loops)} ARM64 round loops; extracted {len(hot)} traversals.")
    return {
        "generated_c_sha256": hashlib.sha256(c_path.read_bytes()).hexdigest(),
        "assembly_command": [helper.redact_paths(arg, root) for arg in compile_args],
        "c_timer_order_checked": timers,
        "arm64_timer_order_checked": asm_timers,
        "c_round_rotation_dataflow_checked": loops,
        "arm64_round_loop_checked": asm_loops,
        "specialized_traversals": hot,
        "cached_traversals_without_closures_or_indirect_calls": cached,
        "sized_traversals_with_container_and_node_reuse": sized,
    }


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
    subprocess.run(["lake", "build", "setContainsBench", "setInsertBench", "VerifiedHAMTTests.SetIR"], cwd=root, check=True)
    # Re-run the imported-entry-point comparison even when Lake's cache is warm.
    subprocess.run(["lake", "env", "lean", "VerifiedHAMTTests/SetIR.lean"], cwd=root, check=True)
    lean = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip()
    ir = subprocess.check_output(["lake", "env", "lean", "Benchmarks/InspectSetIR.lean"], cwd=root, text=True)
    (output / "set.ir.txt").write_text(ir)
    files = ["VerifiedHAMT.lean", "lean-toolchain", "lakefile.toml", "VerifiedHAMTTests/Set.lean", "VerifiedHAMTTests/SetIR.lean",
             "Benchmarks/InspectSetIR.lean", "Benchmarks/inspect_set.py", "Benchmarks/inspect.py",
             "Benchmarks/SetContains.lean", "Benchmarks/SetInsert.lean"]
    files += [str(path.relative_to(root)) for path in sorted((root / "VerifiedHAMT").glob("*.lean"))]
    metadata = {
        "lean": lean,
        "source_sha256": {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in files},
        "set_vs_verified_raw_map_ir_check": "VerifiedHAMTTests/SetIR.lean passed (Nat insert and contains, declaration names normalized)",
        "benchmarks": {stem: inspect(root, output, helper, stem, lean) for stem in ("SetContains", "SetInsert")},
    }
    (output / "set-compiler.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Saved Set compiler evidence to {output}")


if __name__ == "__main__":
    main()
