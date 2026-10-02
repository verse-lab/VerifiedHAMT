# Benchmarks

Tools for comparing HAMTVerify's map and set operations with Lean's native
implementations. See the [project README](../README.md) for the APIs and
correctness theorems, and [docs/Implementation.md](../docs/Implementation.md) for
the design of the measured code and recorded tuning results. Run the paired
benchmarks on each target machine; this document does not prescribe a fixed
performance baseline.

## Run

Use Python 3 and the pinned Lean toolchain. Run these commands sequentially from
the **repository root** so compilation does not interfere with timing. The
scripts build the required Lake targets automatically.

```sh
python3 Benchmarks/inspect.py
python3 Benchmarks/inspect_insert.py
python3 Benchmarks/inspect_set.py

python3 Benchmarks/run.py --benchmark contains --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/contains.json
python3 Benchmarks/run.py --benchmark insert --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/insert.json
python3 Benchmarks/run.py --benchmark setContains --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/set-contains.json
python3 Benchmarks/run.py --benchmark setInsert --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/set-insert.json
```

Reports and compiler evidence are written to the ignored `Benchmarks/results/`
directory. Use `--output` to keep separate runs when comparing machines or
versions. Each inspection script accepts an output directory; `run.py` accepts
a JSON file path.

## Workloads

| Source | Operations |
| --- | --- |
| [Contains.lean](Contains.lean) | Raw map lookup with empty maps and 0%, 50%, or 100% hits |
| [Insert.lean](Insert.lean) | Map construction, value replacement, extension, bucket promotion, and retained snapshots |
| [SetContains.lean](SetContains.lean) | Public set lookup with the same hit-rate coverage |
| [SetInsert.lean](SetInsert.lean) | Set construction, duplicate insertion, extension, bucket promotion, and retained snapshots |

Workloads cover Nat and Name keys, several collection sizes, and default,
shared-prefix, and constant hashes. Lookup batches reuse 8,192 queries. Map
snapshot workloads overwrite existing bindings; set snapshot workloads insert
fresh keys. Both retain every old collection during a round.

Each insertion round starts from the same borrowed seed. Map rounds vary the
inserted values, while set rounds rotate the operation order, to prevent pure
construction from being reused across rounds. Set benchmarks build the seed
through the verified API and give upstream the same tree via `toRaw`.

## Timing and reports

Input preparation and independent result validation happen outside timing.
Calibration warms both implementations and selects a common batch size targeting
`--target-ms` for the faster implementation. Paired samples alternate execution
order. `Runtime.hold` keeps the observed checksum between the clock reads.
Insertion timing includes allocation, reference counting, snapshot retention,
result release, and one or two common native lookups per round; the reported
ns/insert is an amortized workload cost. Verified set insertion maintains its size
along one hash route, reusing the map's runtime container during the traversal.

[run.py](run.py) saves raw samples, per-operation medians, paired elapsed-time
ratios, per-process median ratios, environment metadata, and source/executable
hashes. A ratio below 1 means the verified implementation was faster in that
measurement. The median paired ratio need not equal the quotient of the two
time medians. The printed geometric mean weights workloads equally.

These are warmed microbenchmarks without CPU affinity or frequency control.
Compare paired runs on the target machine and inspect variation across processes;
timings and ratios depend on hardware, compiler, and workload.

## Compiler inspection

[inspect.py](inspect.py), [inspect_insert.py](inspect_insert.py), and
[inspect_set.py](inspect_set.py) inspect imported Lean IR, generated C, and the
actual benchmark specializations. They check clock/batch ordering and retain
traversal code for review. Insertion inspection checks the cached traversal for
closure allocation and indirect calls; set inspection also checks the sized
traversal's container and entries-node reuse, the absence of a separate membership
lookup, and that varying insertion rounds remain in the loop. The set inspector reruns
[HAMTVerifyTests/SetIR.lean](../HAMTVerifyTests/SetIR.lean) to compare wrapper and raw verified entry
points after proof erasure.

Assembly is generated from Lake's actual C compilation command by replacing
`-c` with `-S`. Assembly extraction and automated assembly checks currently target
macOS ARM64; other targets require adapting those checks. The scripts also make
assumptions about generated symbols and specializations that may need review
when upgrading Lean. Compiler checks support interpretation of the measured
code; they do not prove a universal cost bound or logical equivalence with
upstream's opaque partial constants.
