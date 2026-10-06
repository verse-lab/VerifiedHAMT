#!/usr/bin/env python3
"""Check lookup timer ordering and specialized direct calls; save redacted evidence."""

import argparse
import hashlib
import importlib.util
import json
import re
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("Benchmarks/results/find-ir"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    output = root / args.output
    output.mkdir(parents=True, exist_ok=True)
    spec = importlib.util.spec_from_file_location("contains_inspection", root / "Benchmarks/inspect.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    subprocess.run(["lake", "build", "findBench", "VerifiedHAMTTests.MapIR"], cwd=root, check=True)
    ir = subprocess.check_output(["lake", "env", "lean", "Benchmarks/InspectFindIR.lean"],
                                 cwd=root, text=True)
    c_path = root / ".lake/build/ir/Benchmarks/Find.c"
    source = c_path.read_text()
    timers, loops, selected = [], [], []
    for name, body in helper.c_functions(source):
        timed = body.count("lean_io_mono_nanos_now()") == 2
        if timed:
            backend = next((b for b in ("Native", "Verified", "Std") if "measure" + b in name), None)
            if backend is None:
                raise RuntimeError("unexpected timer implementation")
            start = body.index("lean_io_mono_nanos_now()")
            stop = body.rindex("lean_io_mono_nanos_now()")
            if not start < body.index(backend.lower() + "Batch_", start) < body.index("lean_runtime_hold", start) < stop:
                raise RuntimeError("lookup batch moved outside clock reads")
            timers.append({"backend": backend.lower(), "symbol": name})
        loop = "Array_forIn_x27Unsafe_loop___at" in name and "Batch" in name and "___boxed" not in name
        if loop:
            if "lean_apply_" in body:
                raise RuntimeError("indirect call in specialized query loop")
            lookup_calls = [c for c in re.findall(r"(l[p]?_\w+)\(", body)[1:]
                            if any(marker in c for marker in
                                   ("findAux", "findNode", "find_x3f", "get_x3f", "getCast_x3f"))]
            if len(lookup_calls) != 1:
                raise RuntimeError("expected one direct lookup in query loop")
            loops.append({"symbol": name, "lookup": lookup_calls[0]})
        if timed or loop:
            selected.append(body)
    # Generic + empty Nat + custom-hash Nat + Name timers; three specialized
    # query loops per backend. Symbol-dependent checks may need review on upgrades.
    if len(timers) != 12 or len(loops) != 9 or any(
            sum(t["backend"] == b for t in timers) != 4 for b in ("native", "verified", "std")):
        raise RuntimeError("compiler specialization coverage changed")
    (output / "find.ir.txt").write_text(helper.redact_paths(ir, root))
    (output / "find.c.txt").write_text(helper.redact_paths("\n\n".join(selected) + "\n", root))
    metadata = {
        "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
        "generated_c_sha256": hashlib.sha256(c_path.read_bytes()).hexdigest(),
        "executable_sha256": hashlib.sha256((root / ".lake/build/bin/findBench").read_bytes()).hexdigest(),
        "wrapper_raw_ir": "find? and findD equality checked by VerifiedHAMTTests.MapIR",
        "timer_order_checks": timers, "direct_query_loop_checks": loops,
        "scope": "C timer ordering and direct specialized loop calls; no assembly or cost-bound claim",
    }
    (output / "compiler.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print("Checked 12 timers, 9 direct query loops, and bundled/raw IR; saved redacted evidence.")


if __name__ == "__main__":
    main()
