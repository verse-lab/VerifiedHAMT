# Verification

This document describes what HAMTVerify proves about Lean's native
`Lean.PersistentHashMap` representation, and under which assumptions. The
[README](../README.md) covers the bundled `Map` and `Set` APIs, whose theorems
follow from the raw-map results here. Unless stated otherwise, theorems assume
`[BEq α] [LawfulBEq α] [Hashable α]`; values never need instances.

## Specifications

The specifications inspect the stored keys and values, never a lookup algorithm.

| Definition | Meaning |
| --- | --- |
| `Mem key m` (`HasKey`) | `key` occurs in an entry or a collision array anywhere in the tree |
| `MapsTo key value m` (`HasBinding`) | `key` is stored together with `value` somewhere in the tree |
| `Valid m` (`WellFormed`) | every entries array has 32 slots and stores each key in the slot selected by its hash; children satisfy the same invariant for the next five-bit hash chunk |
| `Unique m.root` | no collision array contains a key twice, recursively |
| `keyList`, `keyCount` | the stored keys in tree order, and their number |

`Valid` alone allows duplicate keys within a collision array. Together with
`Valid`, `Unique` excludes duplicates anywhere, since routing already separates
the keys of different slots.

## Membership queries

`HAMTVerify.contains` (`Contains.lean`) is a total version of the native query.
Its main theorem is:

```lean
theorem contains_eq_true_iff (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = true ↔ Mem key map
```

It needs neither unique keys nor collision-free hashes. Termination of `contains`
follows from the number of remaining collision keys and the structural size of
nodes. The development also proves:

- Soundness without `Valid`: a successful query found a stored key
  (`containsNode_sound`).
- Completeness under `Valid` (`containsNode_complete`), and hence
  `contains_eq_false_iff`. A test shows that `Valid` cannot be dropped: a
  misplaced key is stored but missed by the traversal.
- A collision scan from any offset agrees with membership in the remaining
  suffix (`containsAt_eq_true_iff`).
- Hash-selected indices are in bounds for well-formed entries arrays
  (`slot_lt_branching`, `WellFormed.slot_lt`).
- The native empty map is `Valid` and contains no keys (`valid_empty`,
  `not_mem_empty`).

## Insertion

`HAMTVerify.insert` (`Insert.lean`) is a total insertion on the same node types.
Like upstream, it overwrites existing values and creates collision nodes. Below
the native depth limit of seven, a collision node holding at least four keys
after the insertion is promoted to an entries node, which reinserts its keys in
their original order. The main theorems are in `InsertProofs.lean`:

| Theorem | Statement | Premises |
| --- | --- | --- |
| `valid_insert` | `Valid (insert m k v)` | `Valid m` |
| `mem_insert_iff` | `Mem q (insert m k v) ↔ q = k ∨ Mem q m` | `Valid m` |
| `contains_insert` | `contains (insert m k v) q = ((q == k) \|\| contains m q)` | `Valid m` |
| `unique_insert` | `Unique (insert m k v).root` | `Valid m`, `Unique m.root` |
| `mapsTo_insert_iff` | `MapsTo q w (insert m k v) ↔ (q = k ∧ w = v) ∨ (q ≠ k ∧ MapsTo q w m)` | `Valid m`, `Unique m.root` |
| `insert_fold_valid_unique` | inserting any list of bindings into the empty map yields both invariants | none |

`mapsTo_insert_self` and `mapsTo_insert_of_ne` specialize the binding law to the
inserted key and to the other keys. `HasBinding.functional` shows that
`WellFormed` and `Unique` make bindings single-valued.

**The binding law needs `Unique`.** If a valid bucket contains duplicate keys,
promotion can let a later duplicate overwrite the newly inserted value; the tests
include this case. `valid_insert` and `mem_insert_iff` hold even then. Maps built
only with the verified insertion satisfy both invariants
(`insert_fold_valid_unique`), and the bundled `Map` carries them.

Termination is proved in stages. Collision scans and rebuilding decrease the
number of unprocessed array entries, and node insertion decreases the number of
remaining promotion levels. At zero levels, `insertNoExpand` still descends
existing children by structural recursion and inserts, so no case drops an
insertion when the level count runs out, and trees deeper than the promotion
limit are handled.

On a malformed entries array that is too short for the selected slot, `insert`
leaves the array unchanged, like upstream's `Array.modify`, and `contains`
returns `false`. The success guarantees assume `Valid`.

## Key count

`keyList` lists the keys stored in a node, and `keyCount` is its length
(`Size.lean`). Under `Valid` and `Unique` the list contains exactly the stored
keys (`mem_keyList`) without duplicates (`nodup_keyList`), so `keyCount` is the
number of distinct keys. `keyCount_insert` shows that insertion adds one exactly
when the key is new. The bundled `Map` caches this number, with the invariant
`size = keyCount toRaw.root`.

## Executable code and proof models

The theorems are proved about simple models; the executable code is proved equal
to them. These equalities need no `Valid`, `Unique`, or `LawfulBEq` premise:

- `insert_root_eq` and `insertNodeCached_eq` (`InsertCachedProofs.lean`): the
  cached-hash `insert` equals the proof model `insertNode`, for both 32-bit and
  64-bit `USize` and for existing trees deeper than the promotion limit.
  `insertCollision_eq` relates the direct collision-node update to the bucket
  model.
- `insertSized_eq_impl` (`InsertSized.lean`): the single traversal that also
  maintains the size equals `insert` together with the conditional size update.
- `containsThenInsert_eq_impl` (`ContainsThenInsert.lean`): the fused operation
  equals `contains` followed by `insert`.

The last two are `@[csimp]` theorems: compiled code uses the implementation,
while proofs unfold the specification. [Implementation.md](Implementation.md)
explains the implementations.

## Relationship to Lean's implementation

`HAMTVerify.contains` and `HAMTVerify.insert` use Lean's existing `Node` and
`Entry` types, with the same hash masking and shifting, key comparisons,
collision scan, and promotion as the native implementation.

The theorems are about these total functions, not upstream's `partial` helpers
such as `containsAux`, `containsAtAux`, and `insertAux`. Those constants are
opaque to the kernel and expose no equations for their runtime bodies, so
equivalence with them cannot be proved. This is a limitation of the available
logical interface, not merely a missing proof, and the project adds no axiom
connecting them to its implementation. Redefining the bodies with
`partial_fixpoint` would give equation theorems for *new* definitions, not a
connection to the original constants; see the
[Lean reference on recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/).
Runtime comparisons with upstream are regression tests and benchmarks, not
equivalence proofs.

Consequently, a map built by upstream's `insert` needs a separately established
`Valid` proof before the lookup theorem applies to it. Value lookup (`find?`) and
deletion are not verified.

## Trusted base

The tests use `#print axioms` to check that the main theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The library contains no `sorry`,
`native_decide`, `implemented_by`, custom axiom, or `partial` definition. The IR
checks below are compiler regression tests, not theorems.

## Tests

`lake test` checks the following suites:

- `HAMTVerifyTests/Contains.lean`: proof examples, including duplicate collision
  keys, suffix boundaries, malformed arrays, and the misplaced-key counterexample.
  It compares the verified and upstream `contains` with a list model after every
  insertion, overwrite, and deletion and on retained snapshots, using default,
  identity, shared-prefix, constant, and high-bit hashes.
- `HAMTVerifyTests/Insert.lean`: compares insertion with an association-list
  model using default, mixed, shared-prefix, constant, high-bit, and `Name`
  hashes. After every step it compares the complete node structure with
  upstream's, values with upstream `find?`, membership with the verified
  `contains`, and retained snapshots. Each insertion is also checked against the
  compiled sized and fused variants. Explicit cases cover the four-key promotion
  threshold, manually built root buckets, duplicate keys, malformed arrays, and a
  tree deeper than the promotion limit. The structural comparator is a `partial`
  test helper; neither it nor upstream `find?` is used in the proofs.
- `HAMTVerifyTests/Map.lean`, `HAMTVerifyTests/Set.lean`: client proofs without
  invariant hypotheses, collection notation, membership decisions, imports with
  supplied proofs, bulk construction with duplicate keys, promotion, overwrites,
  sizes, and retained snapshots. The set suite also compares against upstream's
  `PersistentHashSet` and a list model.
- `HAMTVerifyTests/MapIR.lean`, `HAMTVerifyTests/SetIR.lean`: after proof
  erasure, the bundled `Nat` insertion and lookup compile to the same IR
  signatures and bodies, including ownership annotations, as direct calls on
  `SizedRaw`, ignoring only declaration names.
