# Benchmarks

Tools for comparing VerifiedHAMT's map and set operations with Lean's native
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
[VerifiedHAMTTests/SetIR.lean](../VerifiedHAMTTests/SetIR.lean) to compare wrapper and raw verified entry
points after proof erasure.

Assembly is generated from Lake's actual C compilation command by replacing
`-c` with `-S`. Assembly extraction and automated assembly checks currently target
macOS ARM64; other targets require adapting those checks. The scripts also make
assumptions about generated symbols and specializations that may need review
when upgrading Lean. Compiler checks support interpretation of the measured
code; they do not prove a universal cost bound or logical equivalence with
upstream's opaque partial constants.

## Keys-only set experiment

```sh
python3 Benchmarks/run_without_vals.py --runs 3 --samples 10 --target-ms 20
python3 Benchmarks/inspect_without_vals.py
```

This separate runner compares five implementations in 40 workloads (18
insertion and 22 lookup cases), rotating execution order on each sample:

| CSV prefix | Implementation |
| --- | --- |
| `native` | `Lean.PersistentHashSet` |
| `raw` | Existing total `VerifiedHAMT.insert` / `contains` on `PersistentHashMap α Unit`, without a size counter |
| `bundled` | Existing `VerifiedHAMT.Set`, with its cached size |
| `bare` | Unsized keys-only `VerifiedHAMT.SetWithoutValArray.Raw` |
| `keys` | Bundled `VerifiedHAMT.SetWithoutValArray`, with cached size and erased invariant proofs |

`bundled` is the comparison with the same public semantics and size maintenance;
`bare` isolates the cost of adding cached size to the keys-only representation.
`raw` provides the unit-valued control without size maintenance. Native and
bundled seeds share a tree; bare and keys-only seeds share another, built in the
same order. Each insertion round borrows its seed, rotates the operation order,
and consumes intermediate versions unless the workload retains snapshots.
Insertion timings include digest queries and releasing the round's results.
The lookup hit model is independent of all five implementations. Ten samples
allow every backend to run first twice per process.

The runner checks generated C to ensure specialized round and query loops have
direct calls, then saves all samples, ratios, process medians, source/binary
hashes, and environment metadata to `Benchmarks/results/without-vals-sized.json`.
`lake test` also checks that the keys-only insertion traversals clear the parent
slot before recursion, including their `Nat` specializations. Wrapper/raw IR
comparisons check proof erasure, the fused compiler rewrite, and that `size`
compiles like a field projection.

`inspect_without_vals.py` saves IR, selected C, assembly, and check metadata in
`Benchmarks/results/without-vals-ir/`. It checks container/node reuse in both
generic sized workers and the four actual Nat/Name benchmark workers, absence
of a separate lookup/count traversal, and direct calls in those specializations.
It also checks that the old collision-array size is read before insertion,
without retaining an alias to that array across the call; otherwise an inlining
change can silently turn an exclusive update into a copy.
The IR test also rejects intermediate product allocation in sized workers.
The generic workers still use typeclass callbacks; the no-indirect-call checks
apply to specialized code. Assembly checks target macOS ARM64 and reuse Lake's
recorded compiler flags. Symbol-sensitive checks need review on Lean upgrades.

After timing, `setWithoutValArrayMemory` counts unique reachable HAMT storage
using the pinned runtime's `lean_object_byte_size`, deduplicating addresses
across snapshots. This includes array capacity, node/entry objects, and the size
carriers of both bundled APIs. It excludes key payloads, outer snapshot arrays, and
allocator metadata/pages. It measures structural storage, **not RSS or total
allocation traffic**. Its unsafe FFI is confined to the benchmark. Live roots
are retained throughout accounting, and a self-check verifies that a shared
array is counted once. Run the memory probe alone with:

```sh
lake build setWithoutValArrayMemory
.lake/build/bin/setWithoutValArrayMemory
```

[SetWithoutValArray.lean](SetWithoutValArray.lean) contains the timing workloads;
[SetWithoutValArrayMemory.lean](SetWithoutValArrayMemory.lean) contains the memory
probe. Recorded results and their scope are in
[docs/SetWithoutValArray.md](../docs/SetWithoutValArray.md).
