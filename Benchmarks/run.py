#!/usr/bin/env python3
"""Run the native Lean benchmark and save all samples plus machine metadata."""

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import io
import json
import math
import platform
import shutil
import statistics
import subprocess
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--benchmark", choices=("contains", "insert", "setContains", "setInsert"), default="contains")
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--samples", type=int, default=9)
    parser.add_argument("--target-ms", type=int, default=20)
    parser.add_argument("--timeout", type=int, default=300, help="seconds per benchmark process")
    parser.add_argument("--output", type=Path, default=Path("Benchmarks/results/latest.json"))
    args = parser.parse_args()
    if min(args.runs, args.samples, args.target_ms, args.timeout) <= 0:
        parser.error("runs, samples, target-ms, and timeout must be positive")

    root = Path(__file__).resolve().parent.parent
    kind = args.benchmark
    lookup = kind in ("contains", "setContains")
    set_benchmark = kind in ("setContains", "setInsert")
    subprocess.run(["lake", "build", f"{kind}Bench"], cwd=root, check=True)
    binary = root / f".lake/build/bin/{kind}Bench"
    command = [str(binary), str(args.samples), str(args.target_ms)]
    rows = []
    for run in range(args.runs):
        print(f"Benchmark process {run + 1}/{args.runs}...", file=sys.stderr, flush=True)
        result = subprocess.run(command, cwd=root, capture_output=True, text=True, timeout=args.timeout)
        if result.returncode:
            raise RuntimeError(f"benchmark exited with {result.returncode}:\n{result.stderr}")
        parsed = list(csv.DictReader(io.StringIO(result.stdout)))
        if not parsed:
            raise RuntimeError("benchmark produced no samples")
        for row in parsed:
            row["native_first"] = row["native_first"] == "true"
            for key in row:
                if key not in ("case", "mode", "native_first"):
                    row[key] = int(row[key])
            row["run"] = run + 1
        rows.extend(parsed)
        print(f"  {len(parsed)} paired samples checked.", file=sys.stderr, flush=True)

    group_fields = ("case", "size", "hit_percent") if lookup else (
        "case", "mode", "base_size", "ops_per_round")
    unit = "query" if lookup else "insert"
    count_field = "queries" if lookup else "operations"
    groups = {}
    for row in rows:
        groups.setdefault(tuple(row[key] for key in group_fields), []).append(row)
    expected_cases = 22 if lookup else 18
    if len(groups) != expected_cases or any(len(samples) != args.runs * args.samples for samples in groups.values()):
        raise RuntimeError("Unexpected scenario or sample count; refusing an incomplete report")
    summary = []
    for group, samples in groups.items():
        ratios = [s["total_ns"] / s["native_ns"] for s in samples]
        run_medians = [
            statistics.median(s["total_ns"] / s["native_ns"] for s in samples if s["run"] == run)
            for run in range(1, args.runs + 1)
        ]
        summary.append({
            **dict(zip(group_fields, group)),
            f"native_ns_per_{unit}_median": statistics.median(s["native_ns"] / s[count_field] for s in samples),
            f"total_ns_per_{unit}_median": statistics.median(s["total_ns"] / s[count_field] for s in samples),
            "paired_ratio_median": statistics.median(ratios),
            "process_ratio_medians": run_medians,
        })

    source_files = ("HAMTVerify/Basic.lean", "HAMTVerify/Contains.lean", "Benchmarks/Contains.lean",
                    "Benchmarks/run.py", "lakefile.toml", "lean-toolchain")
    if kind == "insert" or set_benchmark:
        benchmark_source = {"insert": "Insert", "setContains": "SetContains", "setInsert": "SetInsert"}[kind]
        source_files = ("HAMTVerify.lean", f"Benchmarks/{benchmark_source}.lean", "Benchmarks/run.py",
                        "lakefile.toml", "lean-toolchain") + tuple(
                            str(path.relative_to(root)) for path in sorted((root / "HAMTVerify").glob("*.lean")))
    report = {
        "schema_version": 2,
        "benchmark": kind,
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "environment": {
            "python_platform": platform.platform(), "python_machine": platform.machine(),
            "system": platform.system(), "os_release": platform.release(),
            "executable_format": subprocess.check_output(["file", "-b", str(binary)], text=True).strip()
                                 if shutil.which("file") else None,
            "lean": subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip(),
            "python": platform.python_version(),
        },
        "configuration": {"runs": args.runs, "samples_per_case_per_run": args.samples,
                          "target_ms_per_batch": args.target_ms,
                          **({"query_array_size": 8192} if lookup else {
                              "shuffle_seed": 20261001,
                              "timed_scope": "insertion rounds, snapshot retention, 1-2 lookups per round, and release of completed maps",
                              "seed_ownership": "borrowed at round entry; subsequent maps consumed unless snapshots retained"}),
                          **({"seed_construction": "verified Set API, shared native representation for both APIs"}
                             if set_benchmark else {}),
                          **({"round_variation": "cyclic operation-order rotation by round index",
                              "snapshot_workload": "fresh insertions, retaining every old set"}
                             if kind == "setInsert" else {})},
        "source_sha256": {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in source_files},
        "executable_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "summary": summary,
        "samples": rows,
    }
    output = args.output if args.output.is_absolute() else root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(",".join(group_fields) + f",native_ns/{unit},total_ns/{unit},total/native,process_ratio_range")
    for s in summary:
        print(",".join(str(s[key]) for key in group_fields) + "," +
              f"{s[f'native_ns_per_{unit}_median']:.2f},{s[f'total_ns_per_{unit}_median']:.2f},"
              f"{s['paired_ratio_median']:.3f},"
              f"{min(s['process_ratio_medians']):.3f}..{max(s['process_ratio_medians']):.3f}")
    geometric_mean = math.exp(statistics.mean(math.log(s["paired_ratio_median"]) for s in summary))
    print(f"Unweighted geometric mean of scenario ratios: {geometric_mean:.3f}")
    print(f"Raw samples and metadata: {output}")


if __name__ == "__main__":
    main()
