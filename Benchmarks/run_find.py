#!/usr/bin/env python3
"""Compare synthetic find? workloads, saving only allowlisted anonymous metadata."""

import argparse
import csv
import hashlib
import io
import json
import math
import platform
import shutil
import statistics
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--samples", type=int, default=9)
    parser.add_argument("--target-ms", type=int, default=20)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--output", type=Path, default=Path("Benchmarks/results/find.json"))
    args = parser.parse_args()
    if min(args.runs, args.samples, args.target_ms, args.timeout) <= 0 or args.samples % 3:
        parser.error("runs, target-ms, timeout must be positive; samples must be a positive multiple of 3")

    root = Path(__file__).resolve().parent.parent
    subprocess.run(["lake", "build", "findBench"], cwd=root, check=True)
    binary = root / ".lake/build/bin/findBench"
    fields = ("case", "size", "hit_percent", "sample", "first", "queries",
              "native_ns", "verified_ns", "std_ns", "checksum")
    expected_cases = {("nat-empty", 0, 0)} | {
        (label, size, hit) for label, size in (
            ("nat-default", 32), ("nat-default", 4096), ("nat-default", 65536),
            ("nat-identity", 65536), ("nat-prefix", 4096), ("nat-collision", 128),
            ("name-default", 16384)) for hit in (0, 50, 100)}
    rows = []
    for run in range(1, args.runs + 1):
        print(f"Benchmark process {run}/{args.runs}...", flush=True)
        result = subprocess.run([str(binary), str(args.samples), str(args.target_ms)],
                                cwd=root, capture_output=True, text=True, timeout=args.timeout)
        if result.returncode:
            raise RuntimeError("synthetic benchmark failed: " + result.stderr.strip())
        reader = csv.DictReader(io.StringIO(result.stdout))
        if tuple(reader.fieldnames or ()) != fields:
            raise RuntimeError("unexpected benchmark schema")
        parsed = []
        for raw in reader:
            if set(raw) != set(fields):
                raise RuntimeError("unexpected sample fields")
            row = {key: raw[key] if key == "case" else int(raw[key]) for key in fields}
            row["run"] = run
            if (row["case"], row["size"], row["hit_percent"]) not in expected_cases:
                raise RuntimeError("unexpected workload; refusing non-synthetic input")
            if row["first"] != row["sample"] % 3 or row["queries"] <= 0 or any(
                    row[key] <= 0 for key in ("native_ns", "verified_ns", "std_ns")):
                raise RuntimeError("invalid timing or order")
            parsed.append(row)
        expected_ids = {(case, size, hit, sample) for case, size, hit in expected_cases
                        for sample in range(args.samples)}
        actual_ids = {(r["case"], r["size"], r["hit_percent"], r["sample"]) for r in parsed}
        if actual_ids != expected_ids or len(parsed) != len(expected_ids):
            raise RuntimeError("incomplete or duplicated benchmark samples")
        rows.extend(parsed)
        print(f"  {len(parsed)} samples checked.", flush=True)

    group_fields = ("case", "size", "hit_percent")
    groups = {}
    for row in rows:
        groups.setdefault(tuple(row[key] for key in group_fields), []).append(row)
    summary = []
    for group, samples in groups.items():
        item = dict(zip(group_fields, group))
        for backend in ("native", "verified", "std"):
            item[f"{backend}_ns_per_query_median"] = statistics.median(
                s[f"{backend}_ns"] / s["queries"] for s in samples)
        for baseline in ("native", "std"):
            item[f"verified_over_{baseline}_paired_median"] = statistics.median(
                s["verified_ns"] / s[f"{baseline}_ns"] for s in samples)
            item[f"verified_over_{baseline}_process_medians"] = [statistics.median(
                s["verified_ns"] / s[f"{baseline}_ns"] for s in samples if s["run"] == run)
                for run in range(1, args.runs + 1)]
        summary.append(item)

    source_files = ["VerifiedHAMT.lean", "Benchmarks/Find.lean", "Benchmarks/run_find.py",
                    "lakefile.toml", "lean-toolchain"] + [
        str(p.relative_to(root)) for p in sorted((root / "VerifiedHAMT").glob("*.lean"))]
    geometric_ratios = {baseline: math.exp(statistics.mean(math.log(
        s[f"verified_over_{baseline}_paired_median"]) for s in summary))
        for baseline in ("native", "std")}
    report = {
        "schema_version": 1,
        "benchmark": "find?",
        "data_policy": {
            "input": "deterministic synthetic Nat/Name keys and Nat values; no external dataset",
            "metadata": "allowlist only; no username, hostname, machine ID, serial, absolute path, environment variables, or raw key/value samples",
        },
        "environment": {
            "system": platform.system(), "python_architecture": platform.machine(),
            "os_release": platform.release(), "python_version": platform.python_version(),
            "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
            "executable_format": subprocess.check_output(["file", "-b", str(binary)], text=True).strip()
                                 if shutil.which("file") else None,
        },
        "configuration": {
            "runs": args.runs, "samples_per_case_per_run": args.samples,
            "target_ms_per_batch": args.target_ms, "query_array_size": 8192,
            "seed": 0x5eed, "execution_order": "cyclic rotation of native, verified, std",
            "timed_scope": "lookup and value-dependent checksum only",
            "hamt_seed": "verified Map construction and overwrites; shared native tree",
            "std_seed": "Std.HashMap with identical synthetic insertions and overwrites",
        },
        "source_sha256": {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in source_files},
        "executable_sha256": hashlib.sha256(binary.read_bytes()).hexdigest(),
        "geometric_mean_of_scenario_ratios": geometric_ratios,
        "summary": summary, "samples": rows,
    }
    serialized = json.dumps(report, indent=2) + "\n"
    # Defense against accidentally adding local paths to the report in future edits.
    if any(marker in serialized for marker in ("/Users/", "/home/", str(root))):
        raise RuntimeError("report contains a local absolute path")
    output = args.output if args.output.is_absolute() else root / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(serialized)
    print("case,size,hit_percent,native_ns/query,verified_ns/query,std_ns/query,verified/native,verified/std")
    for s in summary:
        print(",".join(str(s[key]) for key in group_fields) + "," + ",".join(
            f"{s[f'{b}_ns_per_query_median']:.2f}" for b in ("native", "verified", "std")) + "," +
            f"{s['verified_over_native_paired_median']:.3f},{s['verified_over_std_paired_median']:.3f}")
    print("Unweighted geometric mean of scenario ratios: " + ", ".join(
        f"verified/{baseline}={ratio:.3f}" for baseline, ratio in geometric_ratios.items()))
    print("Report saved (synthetic data and anonymous metadata only).")


if __name__ == "__main__":
    main()
