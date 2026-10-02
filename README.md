# HAMTVerify

Verification of membership queries and insertion on Lean **v4.32.0**'s native
`Lean.PersistentHashMap` representation. No external packages are required.

## Bundled map API

Use `HAMTVerify.Map α β` for ordinary code. It bundles the native map with both
`Valid` (hash routing) and `Unique` (no duplicate keys), following the
[standard library's bundled `Std.TreeMap` / `Std.DTreeMap` design](https://lean-lang.org/doc/api/Std/Data/DTreeMap/Basic.html#Std.DTreeMap),
and with its number of keys, which the native map does not store.
Empty maps and insertions construct and preserve these proofs and the size automatically.
The public theorems require no separate invariant hypotheses:

```lean
import HAMTVerify
open HAMTVerify
open scoped HAMTVerify.Map

def exampleMap : Map Nat String :=
  Map.ofList [(7, "old"), (3, "three"), (7, "new")]

#eval exampleMap.contains 7 -- true
#eval decide (3 ∈ exampleMap) -- true
#eval exampleMap.size -- 2

example (m : Map Nat String) (k q : Nat) (v : String) :
    (m.insert k v).contains q = ((q == k) || m.contains q) := by
  simp

example (m : Map Nat String) (k : Nat) (v w : String) :
    (m.insert k v).MapsTo k w ↔ w = v := by
  simp
```

The API supports `∅`, `{}`, collection literals such as `{(1, "one")}`,
`insert`, `ofList`, `contains`, `size`, `keys`, decidable `∈`, and structural `MapsTo`. Insertion
and the query correctness theorems use `[LawfulBEq α]` in addition to `[BEq α]`
and `[Hashable α]`; values need neither `Inhabited` nor `BEq`. Membership and
bindings are defined structurally, independently of the query algorithm.
Activate the map simplification rules with `open scoped HAMTVerify.Map`.

`m.toRaw` explicitly exports the native representation. Importing a native map
with `Map.ofRaw raw hvalid hunique` requires proofs of **both** invariants;
an arbitrary map built by upstream's opaque insertion cannot be imported without
them. Importing counts the keys, in time and memory linear in the size of the map. The lower-level operations and their weaker assumptions remain available
for raw-map proofs. The wrapper exposes the currently verified operations;
value lookup and deletion are still outside the verified API.

`Map` extends `SizedRaw`, which holds the native map and its size; the added proof
fields are erased. Insertion passes this runtime container directly to
`insertSized`, updating the tree and size in one traversal. The container is
reused on descent and return, and the traversal releases each old child reference
before updating it. Only a new key increases the size.
On Lean 4.32.0, the paired Nat insertion and lookup entry points in
`HAMTVerifyTests/Map.lean` compile to the same IR signatures and bodies, including
ownership annotations, as hand-written functions on a structure holding just the
native map and the size, and call the same specialized functions in generated C.
`HAMTVerifyTests/MapIR.lean` checks this as part of `lake test`, ignoring only
declaration names. Thus this compiler check finds no proof computation and no
work beyond maintaining the size for those entry points; it is not a universal
wall-clock performance theorem. Reproduce the IR check with:

```sh
lake test
lake env lean HAMTVerifyTests/MapIR.lean
```

## Bundled set API

`HAMTVerify.Set α` wraps `HAMTVerify.Map α Unit`, matching the design of
[Lean's `PersistentHashSet`](https://lean-lang.org/doc/api/Lean/Data/PersistentHashSet.html#Lean.PersistentHashSet),
whose `set` field is a `PersistentHashMap α Unit`. The underlying map carries
`Valid`, `Unique`, and the size, so set construction and insertion maintain them
automatically.

```lean
import HAMTVerify
open HAMTVerify
open scoped HAMTVerify.Set

def exampleSet : Set Nat := Set.ofList [7, 3, 7]

#eval exampleSet.contains 7 -- true
#eval decide (9 ∈ exampleSet) -- false
#eval ({1, 2, 1} : Set Nat).contains 2 -- true
#eval exampleSet.size -- 2

example (s : Set Nat) (k q : Nat) :
    q ∈ s.insert k ↔ q = k ∨ q ∈ s := by
  simp

example (xs : List Nat) (k : Nat) :
    k ∈ Set.ofList xs ↔ k ∈ xs := by
  simp
```

The interface provides `∅`, `{}`, singleton and insertion notation, `insert`,
`ofList`, `contains`, `size`, `toList`, and decidable structural membership. Its simplification
lemmas use `@[scoped simp]`: activate them with `open scoped HAMTVerify.Set`.
As for maps, insertion and the query correctness theorems require
`[LawfulBEq α]` alongside `[BEq α]` and `[Hashable α]`.

`Set.contains_eq_true_iff` connects the query to structural membership;
`Set.mem_insert_iff` and `Set.mem_ofList` characterize the elements after
insertion and bulk construction. `Set.contains_ofList` also proves agreement
with `List.contains`. `Set.size_insert` gives the size after insertion, and
`Set.mem_toList`, `Set.nodup_toList`, and `Set.length_toList` show that `size` is
the number of elements. These theorems have no explicit invariant premises.

Use `s.toMap` / `Set.ofMap` to move between verified sets and unit-valued maps.
Use `s.toRaw` / `Set.ofRaw raw hvalid hunique` for the native
`Lean.PersistentHashSet` representation. These conversions do not rebuild the
tree; importing native data requires the invariant proofs for `raw.set`.
Set operations delegate to the verified map operations. The native set's
opaque insertion and query are used only as runtime test oracles.

`HAMTVerifyTests/SetIR.lean` compares bundled Nat insertion/query entry points against
hand-written functions calling the verified map operations on the set's runtime
data, the native map and its size. Their compiled IR signatures and bodies are
identical after ignoring declaration names, including ownership
annotations. This check is part of `lake test`; it does not assert
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

## Key count

`HAMTVerify.keyList` lists the keys stored in a node structurally, and
`HAMTVerify.keyCount` is its length. Under `Valid` and `Unique` the list contains
exactly the stored keys (`mem_keyList`) without duplicates (`nodup_keyList`), so
`keyCount` is the number of distinct keys: routing separates the keys of different
slots, and uniqueness those of a collision node. `keyCount_insert` shows that
insertion adds one exactly when the key is new. The bundled map caches this count,
with the invariant `size = keyCount toRaw.root`; `Map.keys` exposes the list.

`insertSized` specifies the existing insertion together with the conditional size
update. Its `@[csimp]` theorem replaces it with `insertSizedImpl`, preserving the
bundled API's definitional equalities. The executable traversal carries the
whole map's count in one reusable `SizedRaw`, changes it at the insertion site,
and reconstructs each parent directly so its node constructor can also be reused.
The native HAMT nodes keep their existing representation. This avoids allocating a
`Bool × Node` result at each level or converting wrappers at the public entry point.

At a collision node the traversal compares array lengths before and after the
existing insertion scan, before any promotion rebuild. The equivalence proof
requires no routing, uniqueness, or lawful-equality assumptions. On malformed
short arrays the size accumulator follows the membership-based specification;
it is a correct key count when the bundled invariants hold. `containsThenInsert`
reuses this traversal with an initial accumulator of zero, producing its Boolean
only at the API boundary. Map and set IR tests compare their insertion entry points
with direct calls to the sized implementation.

### Inspiration from Lean's TreeMap

In Lean v4.32.0, `Std.TreeMap` wraps `Std.DTreeMap`. Its internal
[`Impl.insert` and `Impl.containsThenInsert`](https://github.com/leanprover/lean4/blob/8c9756b28d64dab099da31a4c09229a9e6a2ef35/src/Std/Data/DTreeMap/Internal/Operations.lean#L327-L365)
provide the relevant example: insertion returns an updated tree with cached sizes
and erased proofs; `containsThenInsert` saves the old size, inserts, then compares
the old and new sizes. It constructs the Boolean at the outer boundary, without
passing a `Bool × Tree` result through every recursive level.

HAMT nodes have no cached subtree sizes, so this project adapts that idea by
carrying the whole map's count in `SizedRaw`. The insertion site updates the count;
collision buckets compare their array lengths after the existing insertion scan.
`Map` extends this same runtime structure with proof fields, allowing the wrapper
to erase and the container to be reused throughout insertion. TreeMap's
`containsThenInsert` above uses ordinary insertion and size comparison, not a
`@[csimp]` replacement. Our `@[csimp]` theorem is a separate choice to preserve the
simple logical specification and the bundled API's definitional equalities.
`insertIfNew` would leave an existing value unchanged, so it cannot replace the
overwriting `Map.insert` operation.

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
construction with duplicate keys, collision promotion, overwrites, sizes, and
retained snapshots. Its compiler check compares the bundled entry points with
hand-written ones on the native map and its size, after proof erasure and inlining.

The set suite checks **80,288** query cases against upstream and a list model,
including default, shared-prefix, constant, and Name hashing, duplicate
insertions, sizes, retained snapshots, list construction, and native-set imports.
Client proofs exercise `open scoped HAMTVerify.Set`, membership notation, and
the invariant-free operation laws; the set entry points also have an IR check.

## Performance evaluation

See [Benchmarks/README.md](Benchmarks/README.md) for map and set workloads,
measurement commands, and compiler inspection. Run the benchmarks on the target
machine to evaluate performance with its hardware and toolchain.

### Size-insertion tuning, 2026-10-02

The tuning proceeded in three steps:

1. Fusing `contains` and `insert` into a traversal returning `Bool × Node` removed
   the second lookup but made insertion slower. Generated C showed a pair
   allocation at each level and loss of `Node.entries` constructor reuse. These
   observations explain the optimization direction; their individual costs were
   not measured separately.
2. Following the TreeMap idea above, a prototype carried the tree and total count
   together and reconstructed parents directly in each branch. A short pilot
   measured 1.169× native, but the public map still converted to and from a
   distinct traversal container.
3. Making `Map` extend `SizedRaw` eliminated those runtime conversions. The next
   pilot measured 1.068× native; the full evaluation measured 1.074×. Both pilots
   used one process, five paired samples per case, and 10 ms target batches, so
   their figures are exploratory rather than the final comparison.

The full evaluation used Lean v4.32.0 on macOS ARM64, with 18 Set insertion
scenarios exercising `Map α Unit`. Each version ran in three processes with nine
paired samples per scenario per process and 20 ms target batches. All builds
finished before timing, and benchmark processes ran sequentially. The table is
the equal-weight geometric mean of each scenario's median paired verified/native
time ratio; lower is better.

| Implementation | Time / native |
| --- | ---: |
| Historical implementation without a cached size | 1.022× |
| Cached size using `contains` then `insert` | 1.478× |
| Fused traversal returning `Bool × Node` | 1.595× |
| Reusable `SizedRaw`, shared with `Map` | 1.074× |

The final native-normalized time fell 32.7% relative to the pair-returning version
and 27.3% relative to the two-pass version; all 18 scenarios improved against
both. A 5.1% aggregate overhead remains relative to the historical no-size
version. These ratios describe these workloads and this machine; normalizing by
native timings cannot eliminate all measurement noise.

`lake test` passed, including size/overwrite/promotion checks and exact Map/Set IR
comparisons after proof erasure. Compiler inspection also checks that the sized
traversals retain container and entries-node reuse and contain no separate
membership lookup. The local artifacts are in
`Benchmarks/results/fused-insert-20261002/` and
`Benchmarks/results/sized-carrier-20261002/`: metadata, source snapshots, pilot and
full results, comparisons, and generated-code evidence. Those directories are
gitignored; this README preserves the design rationale and measured summary in
the tracked documentation.

## Files

- `HAMTVerify/Basic.lean`: structural membership, invariants, index bounds, empty map.
- `HAMTVerify/Contains.lean`: total implementation and correctness proofs.
- `HAMTVerify/Bindings.lean`: structural key/value membership and uniqueness.
- `HAMTVerify/Insert.lean`: total insertion, collision updates, and bucket promotion.
- `HAMTVerify/InsertCachedProofs.lean`: equality of cached-hash insertion and the total proof model.
- `HAMTVerify/InsertSized.lean`: reusable runtime size container, insertion traversal, and equivalence proofs.
- `HAMTVerify/ContainsThenInsert.lean`: fused membership and insertion, with a proved compiler rewrite.
- `HAMTVerify/Size.lean`: structural key list and count, and their meaning under the invariants.
- `HAMTVerify/Map.lean`: bundled map type with its size, invariant-preserving API, and laws without invariant premises.
- `HAMTVerify/Set.lean`: verified set interface backed by `Map α Unit` and scoped membership laws.
- `HAMTVerify/InsertProofs.lean`: insertion invariants, membership and value-update proofs.
- `HAMTVerifyTests/Contains.lean`: proof examples, axiom checks, and executable comparisons.
- `HAMTVerifyTests/Insert.lean`: insertion proof examples, axiom checks, and regression tests.
- `HAMTVerifyTests/Map.lean`: bundled API examples, axiom checks, and executable regressions.
- `HAMTVerifyTests/MapIR.lean`: compiler check that the tested bundled entry points compile like hand-written code on the native map and its size.
- `HAMTVerifyTests/Set.lean`: set API proofs, axiom checks, and regression tests.
- `HAMTVerifyTests/SetIR.lean`: compiler check for erasure of the set and map wrappers' proofs.
- [Benchmarks/](Benchmarks/README.md): benchmark workloads, runner, and compiler inspection.
