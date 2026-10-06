# Verification

This document describes what VerifiedHAMT proves about Lean's native
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

`VerifiedHAMT.contains` (`Contains.lean`) is a total version of the native query.
Its main theorem is:

```lean
theorem contains_eq_true_iff (map : Lean.PersistentHashMap α β) (wf : Valid map) (key : α) :
    contains map key = true ↔ Mem key map
```

It needs neither unique keys nor collision-free hashes. `containsNode` recurses on
the size of the node and searches a collision node with `Array.contains`. The
development also proves:

- Soundness without `Valid`: a successful query found a stored key
  (`containsNode_sound`).
- Completeness under `Valid` (`containsNode_complete`), and hence
  `contains_eq_false_iff`. A test shows that `Valid` cannot be dropped: a
  misplaced key is stored but missed by the traversal.
- Hash-selected indices are in bounds for well-formed entries arrays
  (`slot_lt_branching`, `WellFormed.slot_lt`).
- The native empty map is `Valid` and contains no keys (`valid_empty`,
  `not_mem_empty`).

## Value lookup

`VerifiedHAMT.find?` (`Find.lean`) follows the same hash route and first-match
collision scan as upstream, with checked array bounds and structural termination.
Its specification is the independent structural binding relation:

```lean
theorem find?_eq_some_iff (map : Lean.PersistentHashMap α β)
    (wf : Valid map) (hu : Unique map.root) (key : α) (value : β) :
    find? map key = some value ↔ MapsTo key value map

theorem find?_eq_none_iff (map : Lean.PersistentHashMap α β)
    (wf : Valid map) (key : α) : find? map key = none ↔ ¬ Mem key map
```

`findNode_sound` needs neither routing nor uniqueness: a successful result is
always stored. `findNode_exists_of_hasKey` needs routing alone. The `some` iff
needs uniqueness because a duplicate-key collision bucket can store multiple
values while lookup returns only the first. The `none` iff and
`find?_isSome_eq_contains` do not need uniqueness. Values need neither `BEq` nor
`Inhabited`; a stored `none` value is distinct from an absent key.

`find?_insert`, `find?_insert_self`, and `find?_insert_of_ne` prove last-write
lookup behavior from the binding insertion law. `findD` is `(find? m k).getD d`;
`findD_eq_of_mapsTo`, `findD_eq_of_not_mem`, `findD_empty`, and `findD_insert`
prove its value/default and update behavior. The bundled `Map` exports these
theorems without invariant hypotheses, with scoped simp rules for empty maps
and insertions. Short malformed arrays return `none`.

## Insertion

`VerifiedHAMT.insert` (`Insert.lean`) is a total insertion on the same node types.
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

`mapsTo_insert_self` and `mapsTo_insert_of_ne` specialize the binding law to the
inserted key and to the other keys. `HasBinding.functional` shows that
`WellFormed` and `Unique` make bindings single-valued.

**The binding law needs `Unique`.** If a valid bucket contains duplicate keys,
promotion can let a later duplicate overwrite the newly inserted value; the tests
include this case. `valid_insert` and `mem_insert_iff` hold even then. The
bundled `Map` carries both invariants, maintained by `valid_insert` and
`unique_insert`, so its theorems need neither as a hypothesis.

Termination is proved in stages. The collision scan (`insertCollisionAux`) and
`rebuild` decrease the number of unprocessed collision entries, and `insertNode`
decreases the number of remaining promotion levels. At zero levels,
`insertNoExpand` still descends existing children and inserts, so no case drops
an insertion when the level count runs out, and trees deeper than the promotion
limit are handled. Its recursion decreases `sizeOf node`: `insertEntries` passes
the child callback a proof that the child is an element of the entries array.
`insertEntries` clears the selected slot before writing the new entry, a runtime
detail (see [Implementation.md](Implementation.md#insertion-traversal)); by
`insertEntries_eq`, the result is logically a single write.

On a malformed entries array that is too short for the selected slot, `insert`
leaves the array unchanged, like upstream's `Array.modify`, and `contains`
returns `false`. The success guarantees assume `Valid`.

## Key count

`keyList` lists the keys stored in a node, and `keyCount` is its length
(`Size.lean`). Under `Valid` and `Unique` the list contains exactly the stored
keys (`mem_keyList`) without duplicates (`nodup_keyList`), so `keyCount` is the
number of distinct keys. `keyCount_insert` (`InsertProofs.lean`) shows that
insertion adds one exactly when the key is new. The bundled `Map` caches this number, with the invariant
`size = keyCount toRaw.root`.

## Executable code

The insertion theorems are proved directly about the executable `insertNode`,
which receives the remaining hash and the number of hash bits already consumed
(`offset`) as machine words. At a node, the invariant is
`WellFormed (fun k => (hash k).toUSize >>> offset)`. The lemmas
`hash_shift_offset` and `offset_add_shift` relate this arithmetic to `nextHash`
on both 32-bit and 64-bit `USize`, provided `offset + 5 * levels ≤ 30`, which
holds at the root.

Two fast paths are proved equal to simple specifications, with no `Valid`,
`Unique`, or `LawfulBEq` premise, and installed as `@[csimp]` rewrites:

- `insertSized_eq_impl` (`InsertSized.lean`): the single traversal that also
  maintains the size equals `insert` together with the conditional size update.
- `containsThenInsert_eq_impl` (`ContainsThenInsert.lean`): the fused operation
  equals `contains` followed by `insert`.

Compiled code uses the implementations, while proofs unfold the specifications.
[Implementation.md](Implementation.md) explains the implementations.

## Relationship to Lean's implementation

`VerifiedHAMT.contains`, `VerifiedHAMT.find?`, and `VerifiedHAMT.insert` use Lean's existing `Node` and
`Entry` types, with the same hash masking and shifting, key comparisons,
collision scan, and promotion as the native implementation.

The theorems are about these total functions, not upstream's `partial` helpers
such as `containsAux`, `containsAtAux`, `findAux`, `findAtAux`, and `insertAux`. Those constants are
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
`Valid` proof before the lookup theorem applies to it; the successful-value iff
also needs `Unique`. Deletion is not verified.

## Trusted base

The tests use `#print axioms` to check that the main theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The library contains no `sorry`,
`native_decide`, `implemented_by`, custom axiom, or `partial` definition. The IR
checks below are compiler regression tests, not theorems.

## Tests

`lake test` checks the following suites:

- `VerifiedHAMTTests/Contains.lean`: proof examples, including duplicate collision
  keys, malformed arrays, and the misplaced-key counterexample.
  It compares the verified and upstream `contains` with a list model after every
  insertion, overwrite, and deletion and on retained snapshots, using default,
  identity, shared-prefix, constant, and high-bit hashes.
- `VerifiedHAMTTests/Insert.lean`: compares insertion with an association-list
  model using default, mixed, shared-prefix, constant, high-bit, and `Name`
  hashes. After every step it compares the complete node structure with
  upstream's, values with upstream `find?`, membership with the verified
  `contains`, and retained snapshots. Each insertion is also checked against the
  compiled sized and fused variants. Explicit cases cover the four-key promotion
  threshold, manually built root buckets, duplicate keys, malformed arrays, and a
  tree deeper than the promotion limit. The structural comparator is a `partial`
  test helper; neither it nor upstream `find?` is used in the proofs.
- `VerifiedHAMTTests/Find.lean`: generic-value proof examples, axiom checks,
  duplicate-key and misplaced-key counterexamples, empty/malformed arrays,
  out-of-range collision suffixes, and nested `Option` values. Synthetic runtime
  checks compare bundled and raw lookup with upstream HAMT, `Std.HashMap`, and a
  list model after insertions, overwrites, and on retained snapshots. Raw lookup
  is also compared after upstream deletion, without claiming a deletion proof.
  Hashes include default, identity, mixed, shared-prefix, constant, and high-bit
  hashes; `Name` keys and trees deeper than the promotion limit are covered.
  `ofList_lookup_eq_std` and `ofList_findD_eq_std` additionally prove lookup
  equality with `Std.HashMap.ofList` for arbitrary lists, including duplicates,
  using the standard library's insertion equations.
- `VerifiedHAMTTests/Map.lean`, `VerifiedHAMTTests/Set.lean`: client proofs without
  invariant hypotheses, collection notation, membership decisions, imports with
  supplied proofs, bulk construction with duplicate keys, promotion, overwrites,
  sizes, and retained snapshots. The set suite also compares against upstream's
  `PersistentHashSet` and a list model.
- `VerifiedHAMTTests/MapIR.lean`, `VerifiedHAMTTests/SetIR.lean`: after proof
  erasure, the bundled `Nat` insertion, membership, `find?`, and `findD` compile to the same IR
  signatures and bodies, including ownership annotations, as direct calls on
  `SizedRaw`, ignoring only declaration names.
- `VerifiedHAMTTests/ReleaseIR.lean`: in the compiled insertion traversals, both
  the generic workers and their `Nat` specializations, every path to a recursive
  call first clears the entries slot with `Entry.null`.
