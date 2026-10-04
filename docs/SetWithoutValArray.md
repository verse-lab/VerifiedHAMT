# Set without value arrays

`HAMTVerify.SetWithoutValArray` is a verified, bundled counterpart of
`HAMTVerify.Set`, with constant-time `size`. Its leaves store only keys and its
collision buckets only an `Array α`. There are no value fields or `vals` arrays.
The 32-way entries arrays, four-key promotion threshold, and maximum promotion
depth of seven are unchanged.

## Public API

```lean
import HAMTVerify.SetWithoutValArray
open HAMTVerify
open scoped HAMTVerify.SetWithoutValArray

def s : SetWithoutValArray Nat := .ofList [7, 3, 7]
#eval s.size -- 2 (field access)
#eval (s.insert 7).size -- 2
#eval (s.insert 10).size -- 3
#eval decide (3 ∈ s) -- true

example (s : SetWithoutValArray Nat) (k q : Nat) :
    q ∈ s.insert k ↔ q = k ∨ q ∈ s := by simp

example (s : SetWithoutValArray Nat) (k : Nat) :
    ((s.insert k).insert k).size = (s.insert k).size := by
  simp [SetWithoutValArray.size_insert]
```

The collection operations match `Set.lean`: empty sets, literals, insertion,
bulk construction, membership queries, decidable structural membership,
enumeration, and size. The public type bundles `Valid`, `Unique`, and
`size_eq : size = Raw.keyCount toRaw.root`; clients do not supply invariant
hypotheses. `mem_toList`, `nodup_toList`, and `length_toList` prove that
`toList` enumerates each element once and that its length is the cached size.
Its slot order matches `HAMTVerify.Set.toList`.

`toRaw` returns the keys-only `SetWithoutValArray.Raw` in constant time.
`ofRaw` requires proofs of routing and uniqueness and counts the keys in linear
time and memory, like `HAMTVerify.Set.ofRaw`. There is no zero-copy native-map
bridge or `toMap`/`ofMap`, since the node types differ.

## Reusing sized insertion

The implementation adapts the previous `HAMTVerify.InsertSized` design:

1. A `Raw.SizedRaw` holds the raw root and the **whole set's count**. The public
   set extends this exact container, adding only erased proof fields. Counts
   are not stored in every node.
2. Insertion carries the container down one hash route. At an empty slot it adds
   one; replacing a leaf leaves the count unchanged. At a collision bucket it
   compares the array lengths before and after the existing insertion scan.
3. Promotion rebuilds use unsized insertion: the count change was already
   determined before rebuilding. This prevents counting reinserted keys twice.
4. Parent slots are cleared before recursive calls, preserving exclusive
   ownership and in-place updates where possible. Returning the runtime carrier
   avoids a separate `(Bool, Node)` result at every level.
5. `insertSized` has a simple logical specification: ordinary insertion and an
   `if contains ... then oldSize else oldSize + 1` count. The kernel-checked
   `@[csimp]` theorem `Raw.insertSized_eq_impl` replaces it with the fused
   traversal in compiled code. No separate membership traversal runs.

| File | Contents |
| --- | --- |
| `Basic.lean` | Keys-only representation, raw tree, routing and uniqueness predicates |
| `Contains.lean` | Total lookup, soundness and completeness |
| `Insert.lean` | Unsized total insertion, cached hashes, promotion and slot clearing |
| `InsertProofs.lean` | Routing preservation and exact membership update |
| `Size.lean` | Structural key list, count, membership and absence of duplicates |
| `Unique.lean` | Uniqueness preservation and the key-count insertion law |
| `InsertSized.lean` | Reusable count carrier, fused insertion and compiler-rewrite proof |
| `Operations.lean` | Bundled public API and theorems corresponding to `Set.lean` |

All implementation functions are total. No library implementation uses
`partial`, `unsafe`, `sorry`, or `implemented_by`. The main axioms are checked:
only `propext`, `Classical.choice`, and `Quot.sound` occur. Public simp rules are
scoped to `HAMTVerify.SetWithoutValArray`; raw implementation rules are scoped
to its `Raw` namespace.

## Validation

`lake test` checks proof examples, axiom dependencies, and 240,240 query
comparisons for the keys-only API. It checks every intermediate cached size
against a list model and `HAMTVerify.Set`, compares tree shapes and enumeration,
and checks every retained old version after subsequent insertions. Workloads
include distinct and repeated keys, default/identity/shared-prefix/constant/
high-bit hashes, and Name keys. Raw-level tests cover malformed short entries
arrays and the zero-promotion-level collision worker.

`HAMTVerifyTests/ReleaseIR.lean` checks slot clearing before recursive insertion
for both sized and unsized workers and their Nat specializations.
`HAMTVerifyTests/SetWithoutValArrayIR.lean` checks that insertion and lookup
compile identically to direct operations on `Raw.SizedRaw`, after proof erasure.
It also checks that `size` compiles identically to a plain field projection.
The benchmark runner rejects indirect calls in specialized round and query
loops.

## Measurement method

Run from the repository root with no other benchmark or build running:

```sh
lake test
python3 Benchmarks/run_without_vals.py --runs 3 --samples 10 --target-ms 20
python3 Benchmarks/inspect_without_vals.py
```

The 18 insertion and 22 lookup workloads cover construction, duplicates,
extension, promotion, retained snapshots, hit rates, Nat and Name keys, and
several hash distributions. Five backends run in rotating order:

| Prefix | Backend |
| --- | --- |
| `native` | `Lean.PersistentHashSet` |
| `raw` | Existing total `PersistentHashMap α Unit` operations without a size counter |
| `bundled` | `HAMTVerify.Set`, with cached size and erased proofs |
| `bare` | Unsized keys-only `SetWithoutValArray.Raw` |
| `keys` | Public `SetWithoutValArray`, with cached size and erased proofs |

`bundled` is the comparison with equivalent public semantics; `bare` isolates
size-maintenance cost on the keys-only representation. The keys/bare seeds
share one tree, and native/raw/bundled share another. Both trees are built in
identical order. Each insertion round borrows its seed, rotates the operation
order, and consumes later versions unless snapshots are retained. The timed
scope includes digest queries and releasing completed rounds. Lookup batches
reuse 8,192 independently validated queries. Ten samples let every backend run
first twice; calibration targets 20 ms for the fastest backend.

The runner saves all samples, process medians, source/binary hashes, compiler
checks, and environment metadata to the ignored
`Benchmarks/results/without-vals-sized.json`. Time ratios below one mean the
public keys-only set was faster. Aggregates are equal-weight geometric means
of per-workload median paired ratios. These local microbenchmarks do not use
CPU affinity or frequency control.

The memory probe counts unique reachable runtime objects using
`lean_object_byte_size`, including node/entry objects, array capacities, and
the size carriers of both bundled APIs. It also reports the bare keys-only
footprint, so the carrier cost is visible. Addresses are deduplicated across
snapshots, and all roots stay live throughout traversal. Key payloads, outer
history arrays, and allocator metadata/pages are excluded. These figures are
structural storage, not RSS or total allocation traffic. The unsafe diagnostic
FFI is confined to the benchmark executable.

## Compiler evidence

The inspection script saves `keys-only.ir.txt`, `keys-only.c.txt`, `benchmark.s`,
and `compiler.json` under `Benchmarks/results/without-vals-ir/`. It checks the
generic implementation and the actual timed Nat/Name specializations. On the
pinned Lean 4.32.0 toolchain:

- Wrapper/raw IR is identical for insertion, lookup, and size. The bundled
  routing, uniqueness, and count proofs add no runtime fields or wrapper work.
- The size accessor is a field read with reference-count handling:

  ```text
  def wrappedSize (x_1 : @& obj) : tobj :=
    let x_2 : tobj := proj[1] x_1;
    inc x_2;
    ret x_2
  ```

- Public insertion calls the specialized `Raw.insertSizedRaw` directly after
  hashing. Both generic sized workers and the reachable Nat specializations
  have no `Prod.mk` result allocation or call to `contains`, `keyList`, or
  `keyCount`. The logical two-pass specification has been replaced by the
  proved fused implementation.
- Final IR lowers reuse to sharing tests and field writes. The emitted C keeps
  `lean_is_exclusive` paths for the incoming count carrier, entries node, and
  carrier returned by recursion in both generic workers and all four timed
  Nat/Name workers. Parent slots are cleared before recursive descent. These
  paths permit reuse when ownership is exclusive; retained snapshots still
  require copying shared objects.
- The four timed sized workers have no `lean_apply_*` or closure allocation in
  C, and no indirect branch-and-link or closure/application calls in ARM64
  assembly. Generic workers retain the expected typeclass equality callback,
  and generic promotion constructs a callback; the specialization result should
  not be generalized to every polymorphic caller.
- The timing function calls the batch once between the two clocks, with
  `Runtime.hold` before the second clock. Assembly is generated with Lake's
  exact recorded flags, replacing `-c` with `-S`.

These checks guard specific generated-code properties, not a universal runtime
cost bound. They depend on compiler symbol conventions; review failures after
a Lean upgrade. The assembly checks currently cover macOS ARM64.

## Recorded results

The run on 2026-10-05 (Asia/Singapore) used Lean 4.32.0 Release and a native ARM64
benchmark executable on macOS 26.3.1. The Python launcher reports x86_64 under
Rosetta; that is not the benchmark executable's architecture. Three processes
with ten samples each produced 1,200 validated five-backend samples. All source
hashes and the inspected benchmark C hash match the saved timing report.

Elapsed-time ratios, public keys-only set divided by each baseline:

| Baseline | Insertion, 18 workloads | Lookup, 22 workloads |
| --- | ---: | ---: |
| Native `PersistentHashSet` | 0.982 | 0.874 |
| Unsized unit-valued raw map | 0.970 | 0.998 |
| Bundled `HAMTVerify.Set` | **0.915** | **0.999** |
| Unsized keys-only raw tree | 1.058 | 1.000 |

Relative to the comparable public `Set`, insertion took 8.5% less time in the
geometric mean; the individual process aggregates were 0.914–0.917. Lookup
was essentially unchanged (0.998–0.999). Maintaining cached size costs about
5.8% insertion time relative to the unsized keys-only tree, with unchanged
lookup time.

There are individual regressions. For 128 constant-hash keys, lookup ratios
against `Set` were 1.086, 1.058, and 1.024 at 0%, 50%, and 100% hit rates.
The all-miss regression occurred in all three processes (1.084–1.087).
Name all-hit lookup was 1.020. Thus the results support lower memory use and
competitive overall performance, but do not establish no performance loss
for every workload.

Reachable structural storage, including the cached-size carriers on both sides:

| Workload | `Set` bytes | Keys-only bytes | Reduction |
| --- | ---: | ---: | ---: |
| Default Nat, 32 keys | 1,088 | 832 | 23.5% |
| Default Nat, 4,096 keys | 428,096 | 395,328 | 7.7% |
| Default Nat, 65,536 keys | 5,310,528 | 3,213,376 | 39.5% |
| Default Nat, 1,048,576 keys | 35,719,232 | 27,330,624 | 23.5% |
| Shared-prefix Nat, 4,096 keys | 429,032 | 396,264 | 7.6% |
| Constant-hash Nat, 4,096 keys | 100,240 | 51,072 | 49.1% |
| Name, 16,384 keys | 995,904 | 740,840 | 25.6% |
| Default Nat, 4,096 + 512 retained insertions | 923,712 | 886,848 | 4.0% |
| Shared-prefix Nat, 4,096 + 512 retained insertions | 1,403,880 | 1,367,016 | 2.6% |
| Constant-hash Nat, 128 + 128 retained insertions | 1,438,608 | 842,112 | 41.5% |

In these runs cached size adds exactly 24 bytes per live set version over the
bare keys-only tree: one two-field carrier with a small immediate Nat count.
It adds no per-node counters. With 512 retained insertions plus the seed this
is 12,312 bytes, the same carrier cost as the existing bundled `Set`. Actual
savings depend on the mix of singleton leaves, collision buckets, array
capacities, and shared paths; the structural figures exclude key payloads and
allocator overhead as described above.
