#!/usr/bin/env python3
"""Compare native, unit-valued, and keys-only HAMTs with and without cached sizes."""

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import io
import json
import math
from pathlib import Path
import platform
import re
import statistics
import subprocess
import sys


def parse_csv(output):
    rows = list(csv.DictReader(io.StringIO(output)))
    for row in rows:
        for field in row:
            if field not in ("case", "mode"):
                row[field] = int(row[field])
    return rows


def inspect_hot_loops(c_file):
    """Check that specializing the benchmark removed per-operation dispatch."""
    text = c_file.read_text()
    functions = re.findall(
        r"^LEAN_EXPORT [^\n]*?\b(\w+)\([^\n]*\)\{\n(.*?)^}", text, re.M | re.S
    )
    counts = {}
    for role in ("round", "insertBatch", "containsBatch"):
        selected = [(name, body) for name, body in functions
                    if f"KeysOnlyBench_{role}___at___" in name and "___boxed" not in name]
        if not selected:
            raise RuntimeError(f"no specialized {role} code; review generated C")
        for name, body in selected:
            if re.search(r"lean_apply_\d+\(", body):
                raise RuntimeError(f"indirect call in specialized hot loop: {name}")
        counts[role] = len(selected)
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--samples", type=int, default=10)
    parser.add_argument("--target-ms", type=int, default=20)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--output", type=Path, default=Path("Benchmarks/results/without-vals-sized.json"))
    args = parser.parse_args()
    if min(args.runs, args.samples, args.target_ms, args.timeout) <= 0:
        parser.error("runs, samples, target-ms, and timeout must be positive")
    root = Path(__file__).resolve().parent.parent
    targets = ["setWithoutValArrayBench", "setWithoutValArrayMemory"]
    subprocess.run(["lake", "build", *targets], cwd=root, check=True)
    binaries = [root / ".lake/build/bin" / name for name in targets]
    c_file = root / ".lake/build/ir/Benchmarks/SetWithoutValArray.c"
    inspection = inspect_hot_loops(c_file)
    rows = []
    for run in range(args.runs):
        print(f"Timing process {run + 1}/{args.runs}...", file=sys.stderr, flush=True)
        result = subprocess.run([str(binaries[0]), str(args.samples), str(args.target_ms)],
                                capture_output=True, text=True, timeout=args.timeout, check=True)
        parsed = parse_csv(result.stdout)
        for row in parsed:
            row["run"] = run + 1
        rows.extend(parsed)
        print(f"  {len(parsed)} five-way samples validated.", file=sys.stderr, flush=True)
    groups = {}
    fields = ("case", "mode", "size", "ops")
    for row in rows:
        groups.setdefault(tuple(row[f] for f in fields), []).append(row)
    if len(groups) != 40 or any(len(g) != args.runs * args.samples for g in groups.values()):
        raise RuntimeError("incomplete benchmark report")
    summary = []
    for key, samples in groups.items():
        item = dict(zip(fields, key))
        for backend in ("native", "raw", "bundled", "bare", "keys"):
            item[f"{backend}_ns_per_op"] = statistics.median(
                s[f"{backend}_ns"] / (s["ops"] * s["rounds"]) for s in samples)
        for baseline in ("native", "raw", "bundled", "bare"):
            item[f"keys_over_{baseline}"] = statistics.median(
                s["keys_ns"] / s[f"{baseline}_ns"] for s in samples)
            item[f"keys_over_{baseline}_by_process"] = [statistics.median(
                s["keys_ns"] / s[f"{baseline}_ns"] for s in samples if s["run"] == run)
                for run in range(1, args.runs + 1)]
        summary.append(item)
    memory = parse_csv(subprocess.check_output([str(binaries[1])], text=True, timeout=args.timeout))
    if len(memory) != 10:
        raise RuntimeError("incomplete memory report")
    source_paths = sorted(set(root.glob("HAMTVerify/**/*.lean")) |
                          {root / "HAMTVerify.lean", root / "lakefile.toml", root / "lean-toolchain",
                           root / "Benchmarks/SetWithoutValArray.lean",
                           root / "Benchmarks/SetWithoutValArrayMemory.lean", Path(__file__).resolve()})
    report = {
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "environment": {"platform": platform.platform(), "machine": platform.machine(),
                        "lean": subprocess.check_output(["lake", "env", "lean", "--version"],
                                                       cwd=root, text=True).strip()},
        "configuration": {"runs": args.runs, "samples": args.samples, "target_ms": args.target_ms,
                          "order": "cyclic rotation of native, raw, bundled, bare, keys",
                          "insertion_scope": "rounds, snapshots, digest, and release",
                          "memory_scope": "unique live HAMT nodes, entries, arrays including capacity, and size carriers; "
                                          "excludes key payloads, history containers and allocator overhead"},
        "source_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in source_paths},
        "binary_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in binaries},
        "generated_c_sha256": hashlib.sha256(c_file.read_bytes()).hexdigest(),
        "direct_call_specializations": inspection,
        "summary": summary, "memory": memory, "samples": rows,
    }
    output = args.output if args.output.is_absolute() else root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print("case,mode,size,ops,keys/native,keys/raw,keys/bundled,keys/bare")
    for s in summary:
        print(",".join(str(s[f]) for f in fields) + "," +
              ",".join(f"{s[f'keys_over_{b}']:.3f}" for b in ("native", "raw", "bundled", "bare")))
    for label, lookup in (("insertion", False), ("lookup", True)):
        selected = [s for s in summary if s["mode"].startswith("contains") == lookup]
        ratios = {b: math.exp(statistics.mean(math.log(s[f"keys_over_{b}"]) for s in selected))
                  for b in ("native", "raw", "bundled", "bare")}
        print(f"{label} geometric means: {ratios}")
    print("Live structural storage (bytes; not RSS):")
    for m in memory:
        print(f"{m['case']}/{m['size']}/{m['snapshots']}: "
              f"bundled={m['bundled_bytes']}, bare={m['bare_bytes']}, keys={m['keys_bytes']} "
              f"({1 - m['keys_bytes'] / m['bundled_bytes']:.1%} saved vs bundled; "
              f"{m['keys_bytes'] - m['bare_bytes']} bytes for cached counts)")
    print(f"Raw samples and metadata: {output}")


if __name__ == "__main__":
    main()
