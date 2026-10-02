# HAMTVerify

Verification of membership queries and insertion on Lean **v4.32.0**'s native
`Lean.PersistentHashMap` representation. No external packages are required.

## Bundled map API

Use `HAMTVerify.Map α β` for ordinary code. It bundles the native map with both
`Valid` (hash routing) and `Unique` (no duplicate keys), following the
[standard library's bundled tree-map design](https://lean-lang.org/doc/api/Std/Data/DTreeMap/Basic.html#Std.DTreeMap).
Empty maps and insertions construct and preserve these proofs automatically.
The public theorems require no separate invariant hypotheses:

```lean
import HAMTVerify
open HAMTVerify
open scoped HAMTVerify.Map

def exampleMap : Map Nat String :=
  Map.ofList [(7, "old"), (3, "three"), (7, "new")]

#eval exampleMap.contains 7 -- true
#eval decide (3 ∈ exampleMap) -- true

example (m : Map Nat String) (k q : Nat) (v : String) :
    (m.insert k v).contains q = ((q == k) || m.contains q) := by
  simp

example (m : Map Nat String) (k : Nat) (v w : String) :
    (m.insert k v).MapsTo k w ↔ w = v := by
  simp
```

The API supports `∅`, `{}`, collection literals such as `{(1, "one")}`,
`insert`, `ofList`, `contains`, decidable `∈`, and structural `MapsTo`. Insertion
and the query correctness theorems use `[LawfulBEq α]` in addition to `[BEq α]`
and `[Hashable α]`; values need neither `Inhabited` nor `BEq`. Membership and
bindings are defined structurally, independently of the query algorithm.
Activate the map simplification rules with `open scoped HAMTVerify.Map`.

`m.toRaw` explicitly exports the native representation. Importing a native map
with `Map.ofRaw raw hvalid hunique` requires proofs of **both** invariants;
an arbitrary map built by upstream's opaque insertion cannot be imported without
them. The lower-level operations and their weaker assumptions remain available
for raw-map proofs. The wrapper exposes the currently verified operations;
value lookup and deletion are still outside the verified API.

The proof fields are erased and the wrapper has a single runtime data field.
On Lean 4.32.0, the paired Nat insertion and lookup entry points in `Tests/Map.lean`
compile to identical IR signatures and bodies, including ownership annotations,
and call the same specialized functions in generated C. `Tests/MapIR.lean`
checks this as part of `lake test`. Thus this compiler check finds no extra
wrapper allocation or proof computation for those entry points; it is not a
universal wall-clock performance theorem. Reproduce the IR check with:

```sh
lake test
lake env lean Tests/MapIR.lean
```

## Bundled set API

`HAMTVerify.Set α` wraps `HAMTVerify.Map α Unit`, matching the design of
[Lean's `PersistentHashSet`](https://lean-lang.org/doc/api/Lean/Data/PersistentHashSet.html#Lean.PersistentHashSet),
whose `set` field is a `PersistentHashMap α Unit`. The underlying map carries
`Valid` and `Unique`, so set construction and insertion maintain both proofs
automatically.

```lean
import HAMTVerify
open HAMTVerify
open scoped HAMTVerify.Set

def exampleSet : Set Nat := Set.ofList [7, 3, 7]

#eval exampleSet.contains 7 -- true
#eval decide (9 ∈ exampleSet) -- false
#eval ({1, 2, 1} : Set Nat).contains 2 -- true

example (s : Set Nat) (k q : Nat) :
    q ∈ s.insert k ↔ q = k ∨ q ∈ s := by
  simp

example (xs : List Nat) (k : Nat) :
    k ∈ Set.ofList xs ↔ k ∈ xs := by
  simp
```

The interface provides `∅`, `{}`, singleton and insertion notation, `insert`,
`ofList`, `contains`, and decidable structural membership. Its simplification
lemmas use `@[scoped simp]`: activate them with `open scoped HAMTVerify.Set`.
As for maps, insertion and the query correctness theorems require
`[LawfulBEq α]` alongside `[BEq α]` and `[Hashable α]`.

`Set.contains_eq_true_iff` connects the query to structural membership;
`Set.mem_insert_iff` and `Set.mem_ofList` characterize the elements after
insertion and bulk construction. `Set.contains_ofList` also proves agreement
with `List.contains`. These theorems have no explicit invariant premises.

Use `s.toMap` / `Set.ofMap` to move between verified sets and unit-valued maps.
Use `s.toRaw` / `Set.ofRaw raw hvalid hunique` for the native
`Lean.PersistentHashSet` representation. These conversions do not rebuild the
tree; importing native data requires the invariant proofs for `raw.set`.
Set operations delegate to the verified map operations. The native set's
opaque insertion and query are used only as runtime test oracles.

`Tests/SetIR.lean` compares bundled Nat insertion/query entry points against
the verified map operations on native set representations. Their compiled IR
signatures and bodies are identical after ignoring declaration names, including
ownership annotations. This check is part of `lake test`; it does not assert
formal equivalence with upstream partial constants or a universal timing bound.

## Raw-map membership theorem

`HAMTVerify.contains_eq_true_iff` proves:

```lean
-- Given [BEq α] [LawfulBEq α] [Hashable α], a map m, and h : Valid m:
HAMTVerify.contains m key = true ↔ HAMTVerify.Mem key m
```

`Mem` means that the key occurs in an entry or a collision array anywhere in the
tree. It is defined independently of hash-directed lookup. `Valid` requires
32-slot entries arrays, keys routed to their hash-selected slots, and the same
invariants recursively after consuming each five-bit hash chunk. Membership
does not require unique keys or collision-free hashes.

The development also proves:

- Soundness without `Valid`: a successful query always finds a stored key.
- Completeness under `Valid`, and `contains = false` iff the key is absent.
- Collision scanning from an arbitrary offset agrees with suffix membership.
- Hash-selected indices are in bounds for well-formed entries arrays.
- The native empty map satisfies `Valid` and contains no keys.

## Verified insertion

`HAMTVerify.insert` is a total insertion implementation on the same native map
and node types. It updates existing values, creates collision buckets, and
promotes buckets containing at least four keys into entries nodes while below
the native depth limit of seven. Bucket promotion reinserts the key/value arrays
in their original order. It does not replace the trie with a flat list or omit
the promotion case.

The main theorems are:

| Theorem | Statement / assumptions |
| --- | --- |
| `valid_insert` | `Valid m → Valid (insert m k v)` |
| `mem_insert_iff` | Under `Valid m`, `Mem q (insert m k v) ↔ q = k ∨ Mem q m` |
| `contains_insert` | Under `Valid m`, `contains (insert m k v) q = ((q == k) || contains m q)` |
| `unique_insert` | Under `Valid m`, insertion preserves `Unique m.root` |
| `mapsTo_insert_iff` | Under `Valid m` and `Unique m.root`, the inserted key has exactly its new value; all other bindings are preserved |
| `insert_fold_valid_unique` | Every finite sequence of verified insertions from the native empty map satisfies both invariants |

These theorems assume `[BEq α] [LawfulBEq α] [Hashable α]`; no `Inhabited β`
or value equality instance is needed. `MapsTo` is structural key/value membership,
independent of lookup. The exact value-update theorem is:

```lean
MapsTo q w (insert m k v) ↔
  (q = k ∧ w = v) ∨ (q ≠ k ∧ MapsTo q w m)
```

`mapsTo_insert_self` and `mapsTo_insert_of_ne` specialize this to overwriting the
inserted key and preserving other keys. `HasBinding.functional` proves that
`WellFormed` and `Unique` make structural bindings single-valued.

**Uniqueness is an explicit extra premise for the value-update law.** The earlier
`Valid` definition remains unchanged and permits duplicate collision keys.
`Unique` excludes duplicates within each collision array and holds recursively
for children; routing separates keys in different slots. Insertion preserves
`Valid` and the membership law even without uniqueness. A valid but non-unique
bucket can contain a later duplicate that overwrites the newly updated value
during promotion; the tests include this case. Empty maps satisfy both
invariants, and `insert_fold_valid_unique` supplies them for maps built entirely
with the verified insertion. This closes the invariant precondition for using
the existing `contains` theorem on those maps.

Termination is established in stages: collision scans and rebuilding decrease
the number of unprocessed array entries; recursive node insertion decreases the
remaining promotion levels. At zero remaining levels, `insertNoExpand` still
descends existing children using structural termination and performs insertion.
There is no case that silently drops an insertion because a recursion budget
was exhausted. The executable passes a cached remaining hash and a machine-word
bit offset on descent, and recomputes hashes only while rebuilding promoted
buckets. Malformed short entries arrays are left unchanged
when the selected slot is out of bounds, like upstream's `Array.modify`; the
success guarantees require `Valid`.

The original hash-function-based `insertNode` remains as a total proof model.
`InsertCachedProofs.lean` proves `insertNodeCached_eq` and `insert_root_eq`,
connecting the optimized implementation to that model. The equality needs no
`Valid`, `Unique`, or `LawfulBEq` premise. Its offset bound covers both 32-bit and
64-bit `USize`, including arbitrary existing trees deeper than the promotion
limit. `insertCollision_eq` also connects the direct collision-node scan to the
original bucket scan. The public correctness theorems are unchanged and now
apply to the optimized `insert` through these kernel-checked equalities.
No `implemented_by`, custom axiom, or equality with upstream partial constants
is introduced by this optimization.

Inspect the actual imported insertion IR, including upstream's compiled partial bodies, with:

```sh
lake build
lake env lean Benchmarks/InspectInsertIR.lean
```

The generated insertion C is `.lake/build/ir/HAMTVerify/Insert.c` after `lake test`.

## Insert performance and generated code

Benchmark sources and inspection scripts are versioned alongside the library.
The [2026-10-01 baseline archive](Benchmarks/baselines/2026-10-01/README.md)
preserves the reports and compiler evidence cited below, including the available
historical source snapshots. Commands in this README write to the ignored
`Benchmarks/results/` directory. Keep selected future baselines in a new dated
directory under `Benchmarks/baselines/`; routine runs do not update the archive.

Reproduce the insertion measurements and compiler inspection separately:

```sh
python3 Benchmarks/inspect_insert.py
python3 Benchmarks/run.py --benchmark insert --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/insert.json
```

`Benchmarks/Insert.lean` measures 18 workloads using identical native and total
batch loops. Each round starts from the same borrowed seed map and consumes
successive maps. `build` starts empty; `replace` overwrites existing keys;
`extend` adds new keys. `promote` adds a fourth key to each of 1,024 existing
three-key buckets, and validates the expected before/after node shape. The
`snapshots` workloads retain **every** old map during the round, so modified
paths remain shared. Without snapshots, updated paths can become unshared and
benefit from Lean's in-place updates, although the seed still shares untouched
paths and each round's first root update must copy.

Seed construction, operation generation, full final-map validation, and snapshot
checks are outside timing. IDs are deterministically shuffled with seed 20261001.
Each operation in a round uses a distinct key, and each round adds its index to
the inserted values so completed maps cannot be reused between rounds. The
timed batch includes the insertion loops, allocations, reference counting,
releasing completed maps/history, and one final-value lookup per round (two
lookups when retaining snapshots). Consequently the reported ns/insert are
**amortized workload costs**, not isolated instruction latency. Both versions
use the same upstream lookup for these observations. Expected checksums are
computed independently from the operation IDs, values, and round count.

The measurements use native ARM64 Lean 4.32.0 on macOS 26.3.1, Lake's bundled
Clang with `-O3 -DNDEBUG`, three independent processes, and nine alternating-order
paired samples per workload: 486 pairs in total. Calibration chooses one common
round count targeting at least 20 ms for the faster implementation. There is no
CPU affinity or frequency control; repeated warmed workloads do not represent
all applications. The [raw report](Benchmarks/baselines/2026-10-01/insert.json) includes every
sample, per-process median ratios, environment, and source/executable hashes.
The [pre-optimization report](Benchmarks/baselines/2026-10-01/insert-before-optimization/insert.json)
is retained together with its compiler evidence and exact source snapshots in
`Benchmarks/baselines/2026-10-01/insert-before-optimization/`. The workload and runner are
unchanged. Before/after timings come from separate runs on this machine;
optimized/upstream ratios are paired within the new run.

**Optimization reduces the observed cost by 1.24–7.10×, bringing the total
implementation close to upstream.** The optimized/upstream paired ratios range
from 0.932 to 1.103 across these workloads. Some overwrite workloads remain
about 9–10% slower; this does not establish a universal “no slower” guarantee.
Below, times are medians in ns per inserted/overwritten binding, and the ratio
is the median of paired optimized/upstream times (not the quotient of the two
time medians).
`prefix` shifts the Nat hash left by 15 bits; `collision` uses a constant hash;
`mixed` uses `mixHash 20261001`.

| Case / mode | Seed keys / writes per round | Before ns/write | Upstream ns/write | Optimized ns/write | Optimized / upstream |
| --- | ---: | ---: | ---: | ---: | ---: |
| Nat default / build | 0 / 32 | 59.95 | 35.63 | 36.50 | 1.024 |
| Nat default / build | 0 / 4,096 | 328.06 | 110.32 | 105.27 | 0.956 |
| Nat default / build | 0 / 65,536 | 430.28 | 86.90 | 88.42 | 1.019 |
| Nat mixed / build | 0 / 4,096 | 341.13 | 101.91 | 100.51 | 0.981 |
| Nat prefix / build | 0 / 4,096 | 750.08 | 132.78 | 132.06 | 0.995 |
| Nat collision / build | 0 / 128 | 964.14 | 196.69 | 195.62 | 0.994 |
| Name default / build | 0 / 16,384 | 380.84 | 67.79 | 68.56 | 1.010 |
| Nat default / replace | 4,096 / 4,096 | 293.46 | 74.69 | 81.93 | 1.098 |
| Nat default / replace | 65,536 / 65,536 | 500.89 | 132.96 | 143.04 | 1.065 |
| Nat prefix / replace | 4,096 / 4,096 | 742.15 | 96.00 | 104.53 | 1.090 |
| Nat collision / replace | 128 / 128 | 1,083.45 | 187.98 | 190.92 | 1.016 |
| Name default / replace | 16,384 / 16,384 | 455.69 | 82.61 | 91.16 | 1.103 |
| Nat default / extend | 4,096 / 4,096 | 303.56 | 71.06 | 72.75 | 1.024 |
| Nat default / promote | 3,072 / 1,024 | 529.25 | 298.40 | 278.27 | 0.932 |
| Nat default / snapshots | 4,096 / 512 | 357.98 | 238.55 | 243.69 | 1.024 |
| Nat prefix / snapshots | 4,096 / 512 | 786.78 | 431.37 | 442.84 | 1.026 |
| Nat collision / snapshots | 128 / 128 | 1,175.59 | 772.24 | 788.96 | 1.022 |
| Name default / snapshots | 16,384 / 512 | 461.16 | 368.11 | 373.02 | 1.018 |

The three process median ratios for the 4,096-key default build were
0.953–0.957; for shared-prefix replacement, 1.090–1.092; for default-hash
snapshots, 1.014–1.029. These ranges describe the observed runs and are not
confidence intervals. The unweighted geometric mean of the 18 paired ratios
fell from 3.246 to 1.021; this diagnostic gives each workload equal weight and
does not predict the cost of an application's workload mix.

Compiler evidence is retained as [Lean IR](Benchmarks/baselines/2026-10-01/insert.ir.txt),
[specialized C](Benchmarks/baselines/2026-10-01/insert.c.txt),
[optimized ARM64 assembly](Benchmarks/baselines/2026-10-01/insert.arm64.txt), and
[inspection metadata](Benchmarks/baselines/2026-10-01/insert-compiler.json). The inspection
script checks clock → batch → clock ordering in all six measurement functions
in C and ARM64 assembly. It also extracts the actual repeated-round loops, the
four Nat/Name traversal specializations, and eight collision/rebuild/fallback
helpers. The round loops contain calls to the corresponding insertion batch and
result digest on each iteration. It checks that both cached traversal
specializations have no closure allocation or `lean_apply_*` calls in C, and
no `lean_apply_*` calls in the optimized ARM64 assembly.

Three implementation changes are visible in the compiler evidence:

- **Ownership during child updates.** Entries insertion now uses `Array.modify`,
  like upstream. The compiled code removes the old slot reference before
  recursive insertion and writes the result back afterward. The structurally
  recursive fallback achieves the same effect by explicitly setting the slot to
  `.null` first. This allows otherwise unshared children to remain unshared;
  retained snapshots still correctly require copies. Lean's
  [reference-counting documentation](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/)
  explains why shared arrays copy while unshared arrays can be updated in place.
- **Cached hashes and direct recursion.** `insertNodeCached` passes the remaining
  hash and consumed-bit offset as machine words. The specialized traversal has
  direct recursive calls, with no shifted-hash closures or repeated key hashing
  on descent. `@[specialize]` eliminates the rebuild child callback in the
  inspected specializations. Promotion still computes each reinserted key's
  hash, including a dynamic call for the benchmark's configurable Nat hasher,
  as expected.
- **Collision-node reuse.** `insertCollision` scans and updates the collision
  node directly through an erased subtype. Ordinary collision updates no longer
  allocate the intermediate `Bucket` wrapper. The specialized C reuses an
  exclusive collision constructor; promotion can also reuse that constructor
  for its temporary bucket.

There is no runtime `sizeOf` traversal or termination-proof evaluation. Runtime
differences remain: the optimized version still carries a `Nat` promotion-level
counter and has a separate structural fallback, while upstream uses a
machine-word depth. We have not attributed the remaining timing gap to a
specific instruction or allocation count.

Short exploratory reports for [ownership changes alone](Benchmarks/baselines/2026-10-01/insert-ownership.json)
and [cached hashes before collision-node reuse](Benchmarks/baselines/2026-10-01/insert-cached-pilot.json)
are retained separately (one process, three samples per workload, 10 ms target).
They guided the changes; the table above uses the complete final measurement.

## Relationship to Lean's implementation

The total functions in `HAMTVerify/Contains.lean` use Lean's existing `Node` and
`Entry` types and the same hash masking, shifting, equality checks, and collision
scan as the native implementation. Termination is proved by the number of
remaining collision keys and the structural size of nodes. An explicit bounds
check returns `false` for an out-of-range slot in a malformed short array; this
case cannot occur in a well-formed entries array.

**The theorems are about `HAMTVerify.contains` and `HAMTVerify.insert`.** Formal equivalence with the
existing upstream `partial` constants is outside this project's scope. Upstream
helpers such as `containsAux`, `containsAtAux`, and `insertAux` are opaque to the kernel and expose no defining
equations for their runtime bodies. This is a limitation of the available logical
interface, not merely a missing equivalence proof. We add no axioms connecting
them to our implementation.

Rewriting the bodies as new `partial_fixpoint` definitions would provide equation
theorems and permit proofs about those new definitions; it would not establish a
formal connection to the original opaque constants. See the
[Lean reference on recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/).
Runtime comparisons against upstream are regression tests and performance
measurements, not formal equivalence proofs.

The total insertion's correctness and preservation of `Valid` are proved.
Preservation by upstream's opaque insertion, and correctness of deletion and
value lookup (`find?`), are not proved. In particular, an arbitrary map built by
upstream `insert` still needs a separately established `Valid` hypothesis before
the verified lookup theorem can be applied.

## Check

```sh
lake build
lake test
```

`lake test` checks proof examples (including duplicate collision keys, suffix
boundaries, malformed arrays, and a misplaced-key counterexample) and compares
the total implementation and upstream `contains` with an independent list model.
It checks each insertion, value replacement, deletion, and retained snapshot,
using default, identity, shared-prefix, constant, and high-bit hash functions.

The insertion suite checks **260,720** queries against an independent association
list model, with default, mixed, shared-prefix, constant, high-bit, and Name
hashing. After insertions and overwrites, it compares the complete node structure
against upstream, checks values using upstream `find?` on both maps, checks the
verified `contains`, and checks retained snapshots. Explicit cases exercise the
four-key promotion threshold, manually constructed root buckets, duplicates,
malformed arrays, and an existing tree deeper than the promotion limit. The
structural comparator is a `partial` test helper, outside the verified library;
neither it nor upstream `find?` is used in the proofs.

The tests also guard the main theorems' axiom dependencies:
`propext`, `Classical.choice`, and `Quot.sound` only. The proofs use no `sorry`,
additional axioms, or `native_decide`.

The bundled API suite checks client proofs without explicit invariants,
collection notation, membership decisions, imports with supplied proofs, bulk
construction with duplicate keys, collision promotion, overwrites, and retained
snapshots. Its compiler check compares the bundled and raw entry points after
proof erasure and inlining.

The set suite checks **80,288** query cases against upstream and a list model,
including default, shared-prefix, constant, and Name hashing, duplicate
insertions, retained snapshots, list construction, and native-set imports.
Client proofs exercise `open scoped HAMTVerify.Set`, membership notation, and
the invariant-free operation laws; the set entry points also have an IR check.

## Contains performance and generated code

There is **no unconditional "at least as fast as upstream" guarantee**. The
initial implementation was slower in most measured cases. Inspecting Lean IR,
generated C, and optimized ARM64 assembly identified two avoidable calls:
`slot` at each entries node and `nextHash` at each child descent. Adding
`@[inline]` to those two definitions removes the calls without changing their
logical definitions or proofs. The resulting implementation is generally at
parity or faster in this benchmark, with small measured regressions in the
collision cases. This is evidence for one compiler, machine, and workload.

Reproduce with Python 3 and the pinned Lean toolchain; run timing and compiler
inspection separately to avoid compiler activity interfering with measurements:

```sh
python3 Benchmarks/run.py --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/contains.json
python3 Benchmarks/inspect.py
```

The native executable compares the public upstream and total APIs using identical
batch loops. Map construction, query generation, validation, and calibration
are outside timing. Each case reuses 8,192 queries with a fixed seed, with 0%,
50%, or 100% hits; the 50% case alternates hits and misses. Both implementations
receive the same map, queries, and calibrated round count. Calibration targets
at least 20 ms for the faster batch. Nine paired samples alternate execution
order in each of three independent processes. All queries and batch checksums
are checked against expected membership derived from the inserted keys.

Measurements use `IO.monoNanosNow` and `Runtime.hold checksum`. A plain pure
`let checksum := batch ...` was observed to move **after** the second clock read
during Lean compilation, producing invalid timings; those runs were discarded.
The inspection script verifies clock → batch → clock ordering in all eight
generated measurement functions, in both C and optimized ARM64 assembly.
The clock and checksum bookkeeping overhead is amortized over a whole batch.

Recorded on macOS 26.3.1 using native ARM64 Lean 4.32.0 and Lake's bundled Clang
with `-O3 -DNDEBUG`. The Python driver runs under Rosetta; this does not change
the benchmark executable's ARM64 architecture. Each cell below is the range
across the three hit rates of median paired **total / upstream elapsed time**;
less than 1 means the total implementation is faster. The empty case has only
misses. Each implementation version has 594 recorded pairs (22 cases × 9 × 3).

| Workload | Keys | Before inlining | After inlining |
| --- | ---: | ---: | ---: |
| Empty, Nat | 0 | 1.399 | 1.001 |
| Default hash, Nat | 32 | 0.937–0.940 | 0.828–0.830 |
| Default hash, Nat | 4,096 | 1.037–1.213 | 0.707–0.924 |
| Default hash, Nat | 65,536 | 1.049–1.121 | 0.995–1.003 |
| Explicit identity hash, Nat | 65,536 | 1.047–1.115 | 0.981–1.003 |
| Shared 15-bit prefix, Nat | 4,096 | 1.183–1.257 | 0.952–0.965 |
| Constant hash, Nat | 128 | 0.999–1.018 | 1.003–1.012 |
| Default hash, Name | 16,384 | 1.141–1.207 | 0.898–0.938 |

The [recorded lookup samples](Benchmarks/baselines/2026-10-01/contains.json) and
[pre-inlining samples](Benchmarks/baselines/2026-10-01/before-inline.json) include individual
times, per-process median ratios, toolchain information, source hashes, and
executable hashes. To reproduce the earlier variant, remove only the two
`@[inline]` attributes in `Basic.lean` and rebuild. The default Nat hash in this
Lean version is `UInt64.ofNat`, so the explicit identity-hash case repeats that
distribution. These are warmed, repeated-query microbenchmarks, with no CPU
affinity or frequency control. Some process medians vary substantially (notably
0.583–0.890 for the final 4,096-key, 50%-hit case); the ranges above are across workloads, **not**
confidence intervals. Small differences remain observations, not guarantees or
evidence of a particular cause.

Compiler evidence is saved as [imported Lean IR](Benchmarks/baselines/2026-10-01/contains.ir.txt),
[specialized C excerpts](Benchmarks/baselines/2026-10-01/contains.c.txt),
[optimized ARM64 excerpts](Benchmarks/baselines/2026-10-01/contains.arm64.txt), and
[compiler/check metadata](Benchmarks/baselines/2026-10-01/compiler.json). The IR comes from
`Lean.IR.findEnvDecl` on the actual imported definitions, including the original
upstream `partial` implementations. The C and assembly include the benchmark's
specializations for Nat and Name, rather than only generic library functions.
The assembly is regenerated from the actual Lake C compilation command by
replacing `-c` with `-S`; the complete file is left in `.lake/inspection/Contains.s`.
Assembly extraction and ordering checks currently target macOS ARM64.

The inspection establishes these concrete properties of this compilation:

- Both traversals compile their recursive descent to a loop (`goto _start` in
  C). Neither total lookup computes `sizeOf`, a decreasing fuel value, or a
  termination proof at runtime. This agrees with Lean's documented
  [erasure of types and proofs](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/).
- The reduced collision-scan IR is identical after renaming the function; the
  inspection script checks this. The specialized Nat collision-scan assembly
  also matches after normalizing symbols, local labels, and comments.
- Before inlining, specialized total traversal still called `slot` and
  `nextHash`. The ARM64 code also retained a large-Nat comparison fallback and
  reference-count branches for the opaque-to-Clang slot result. After inlining,
  the index is visibly at most 31, those paths disappear, and both traversals
  use `and ... #0x1f` and `lsr ... #5`. See the saved
  [earlier IR](Benchmarks/baselines/2026-10-01/before-inline.ir.txt),
  [C](Benchmarks/baselines/2026-10-01/before-inline.c.txt), and
  [assembly](Benchmarks/baselines/2026-10-01/before-inline.arm64.txt).
- **Both versions check entries-array bounds.** Upstream's `entries[j]!` uses
  a checked accessor with an out-of-bounds panic path. Ours checks the bound and
  then uses a proved-in-bounds access, returning `false` if out of bounds.
  There is no additional duplicated bounds check in the specialized C. These
  different failure paths also produce different register allocation and
  instruction layout, even though well-formed maps never take them.
- The specialized Nat/Name traversals borrow nodes and entries in both versions;
  the total implementation introduces no extra reference-count traffic for
  termination proofs. Generic dictionary calls and reference-count operations
  should not be confused with the specialized code being timed.

Reading the compiled loops gives the same traversal cost shape: one selected
branch per trie level, then at most a linear collision scan, with constant stack
usage for traversal. This is a code-inspection observation, not a formal cost
theorem. Neither erasure nor matching collision-scan IR establishes a universal
wall-clock ordering, or logical equality with upstream's opaque constants.

## Set performance and generated code

The public `HAMTVerify.Set` API is benchmarked directly against
`Lean.PersistentHashSet`. On this machine, queries are generally at parity or
slightly faster; insertion is close to upstream except for duplicate insertion,
where the Name case is about **12.3% slower**. This does not establish a universal
"no slower" guarantee. The verified implementation and its proofs are unchanged
by these measurements.

Reproduce the compiler inspection and the two measurements sequentially:

```sh
python3 Benchmarks/inspect_set.py
python3 Benchmarks/run.py --benchmark setContains --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/set-contains.json
python3 Benchmarks/run.py --benchmark setInsert --runs 3 --samples 9 --target-ms 20 --output Benchmarks/results/set-insert.json
```

Recorded on 2026-10-01 with native ARM64 Lean 4.32.0, macOS 26.3.1, and Lake's
bundled Clang at `-O3 -DNDEBUG`. Each workload has three independent processes
and nine alternating-order paired samples per process. Calibration uses a
common batch size targeting at least 20 ms for the faster implementation.
There are **594 query pairs and 486 insertion pairs**. Construction of the seed,
operation/query generation, and independent expected-result validation happen
outside timing. The verified API constructs each seed, and `toRaw` gives both
implementations exactly the same underlying seed tree. All validation and timed
checksum checks passed. No CPU affinity or frequency control is applied.

For lookup, each batch repeats 8,192 queries. The table gives the range across
0%, 50%, and 100% hits of the median paired **verified / upstream elapsed time**;
less than 1 means faster. The empty case has only misses. These are ranges
across workloads, not confidence intervals.

| Query workload | Keys | Verified / upstream |
| --- | ---: | ---: |
| Empty, Nat | 0 | 1.000 |
| Default hash, Nat | 32 | 0.907–0.911 |
| Default hash, Nat | 4,096 | 0.907–0.953 |
| Default hash, Nat | 65,536 | 0.997–1.002 |
| Explicit identity hash, Nat | 65,536 | 0.993–1.000 |
| Shared 15-bit prefix, Nat | 4,096 | 0.948–0.963 |
| Constant hash, Nat | 128 | 1.003–1.012 |
| Default hash, Name | 16,384 | 0.922–0.962 |

Insertion covers fresh construction, reinserting existing members (`duplicate`),
extending an existing set, collision-bucket promotion, and retaining every old
set (`snapshots`). Snapshot workloads insert **fresh keys**; unlike the earlier
map benchmark, they do not overwrite existing bindings. Each round borrows the
same seed, consumes successive sets, and releases its final result and retained
snapshots inside timing. A common native lookup checks the last inserted key
(and its absence from an old snapshot when retaining snapshots).

Unit-valued sets cannot vary inserted values between rounds. Instead, each round
cyclically rotates the shuffled insertion order using its round index. Two
ranges implement the rotation, with no modulus per inserted key. The compiled
loops retain the varying round argument and the insertion call; repeated pure
construction has not been lifted out of the round loop.

Times below are medians in ns per insertion, including allocation, reference
counting, result release, and the amortized round/observation overhead. The ratio
is the median of paired times, not the quotient of the two time medians.
`prefix` shifts the hash left by 15 bits; `collision` uses a constant hash;
`mixed` uses `mixHash 20261001`.

| Insertion workload | Seed keys / writes per round | Upstream ns/write | Verified ns/write | Verified / upstream |
| --- | ---: | ---: | ---: | ---: |
| Nat default / build | 0 / 32 | 37.87 | 39.14 | 1.031 |
| Nat default / build | 0 / 4,096 | 112.14 | 107.42 | 0.960 |
| Nat default / build | 0 / 65,536 | 85.52 | 86.78 | 1.018 |
| Nat mixed / build | 0 / 4,096 | 102.84 | 101.08 | 0.982 |
| Nat prefix / build | 0 / 4,096 | 135.67 | 134.74 | 0.993 |
| Nat collision / build | 0 / 128 | 198.47 | 198.71 | 0.999 |
| Name default / build | 0 / 16,384 | 69.58 | 70.23 | 1.008 |
| Nat default / duplicate | 4,096 / 4,096 | 75.74 | 82.98 | 1.091 |
| Nat default / duplicate | 65,536 / 65,536 | 128.20 | 137.25 | 1.065 |
| Nat prefix / duplicate | 4,096 / 4,096 | 97.61 | 106.51 | 1.093 |
| Nat collision / duplicate | 128 / 128 | 190.30 | 191.96 | 1.013 |
| Name default / duplicate | 16,384 / 16,384 | 84.23 | 94.45 | 1.123 |
| Nat default / extend | 4,096 / 4,096 | 73.14 | 74.11 | 1.014 |
| Nat default / promote | 3,072 / 1,024 | 305.37 | 283.88 | 0.930 |
| Nat default / snapshots | 4,096 / 512 | 233.39 | 237.50 | 1.016 |
| Nat prefix / snapshots | 4,096 / 512 | 428.38 | 438.24 | 1.023 |
| Nat collision / snapshots | 128 / 128 | 1,095.08 | 1,111.51 | 1.012 |
| Name default / snapshots | 16,384 / 512 | 375.24 | 374.85 | 0.996 |

The unweighted geometric mean of the scenario ratios is 0.964 for queries and
1.019 for insertion. These summaries weight each workload equally and do not
predict an application's workload mix. Duplicate insertion's gap is visible
across processes: the median ratios for Name duplicates are 1.115–1.125, and for
shared-prefix Nat duplicates 1.090–1.097. We have not isolated its cause to a
particular instruction or allocation. Small differences in the other cases
remain observations of warmed workloads on one machine.

The [query report](Benchmarks/baselines/2026-10-01/set-contains.json) and
[insertion report](Benchmarks/baselines/2026-10-01/set-insert.json) contain every sample,
per-process medians, environment details, and source/executable hashes.
The [imported Lean IR](Benchmarks/baselines/2026-10-01/set.ir.txt) and
[inspection metadata](Benchmarks/baselines/2026-10-01/set-compiler.json) record the compiler
checks; actual benchmark specializations are saved as
[query C](Benchmarks/baselines/2026-10-01/set-contains.c.txt),
[query ARM64](Benchmarks/baselines/2026-10-01/set-contains.arm64.txt),
[insertion C](Benchmarks/baselines/2026-10-01/set-insert.c.txt), and
[insertion ARM64](Benchmarks/baselines/2026-10-01/set-insert.arm64.txt).

The inspector reruns `Tests/SetIR.lean`: the Nat set insertion and query entry
points have the same IR as their raw verified map counterparts, including
ownership annotations, after normalizing declaration names. The Set/Map
wrappers and invariant proofs add no allocation or proof evaluation at those
entry points. This compares the wrapper with our verified core, not with
upstream's different insertion algorithm.

The compiler inspection also checks clock → batch → clock ordering in all
14 C and ARM64 timer functions, rotation data flow in all four specialized C
insertion round loops, and the retained round calls and loop back edges in
ARM64. It extracts the four Nat/Name traversal specializations for each
operation. Both cached insertion traversals contain no closure allocation or
`lean_apply_*` call in C, and no `lean_apply_*` call in ARM64. Assembly is
generated using the actual Lake compilation command with `-c` replaced by `-S`.
These checks explain which code was timed; they are not a formal cost theorem
or logical equivalence to upstream partial constants.

## Files

- `HAMTVerify/Basic.lean`: structural membership, invariants, index bounds, empty map.
- `HAMTVerify/Contains.lean`: total implementation and correctness proofs.
- `HAMTVerify/Bindings.lean`: structural key/value membership and uniqueness.
- `HAMTVerify/Insert.lean`: total insertion, collision updates, and bucket promotion.
- `HAMTVerify/InsertCachedProofs.lean`: equality of cached-hash insertion and the total proof model.
- `HAMTVerify/Map.lean`: bundled map type, invariant-preserving API, and laws without invariant premises.
- `HAMTVerify/Set.lean`: verified set interface backed by `Map α Unit` and scoped membership laws.
- `HAMTVerify/InsertProofs.lean`: insertion invariants, membership and value-update proofs.
- `Tests/Contains.lean`: proof examples, axiom checks, and executable comparisons.
- `Tests/Insert.lean`: insertion proof examples, axiom checks, and regression tests.
- `Tests/Map.lean`: bundled API examples, axiom checks, and executable regressions.
- `Tests/MapIR.lean`: compiler check that the bundled API adds no overhead to the tested entry points.
- `Tests/Set.lean`: set API proofs, axiom checks, and regression tests.
- `Tests/SetIR.lean`: compiler check for erasure of the set and map wrappers.
- `Benchmarks/Contains.lean`: native paired timing and result validation.
- `Benchmarks/Insert.lean`: insertion workloads, ownership modes, and result validation.
- `Benchmarks/SetContains.lean`: paired public set query workloads and result validation.
- `Benchmarks/SetInsert.lean`: paired public set insertion workloads, rotating rounds, and snapshots.
- `Benchmarks/run.py`: repeated processes, raw samples, and summary statistics.
- `Benchmarks/InspectIR.lean`, `Benchmarks/inspect.py`: compiler evidence and timer-order checks.
- `Benchmarks/InspectInsertIR.lean`: inspect the compiled insertion definitions.
- `Benchmarks/inspect_insert.py`: insertion compiler evidence and timer-order checks.
- `Benchmarks/InspectSetIR.lean`, `Benchmarks/inspect_set.py`: set IR, timer-order checks, and insertion-loop inspection.
