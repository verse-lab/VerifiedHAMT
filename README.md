# VerifiedHAMT

Verified membership queries and insertion for Lean's native hash array mapped
trie, `Lean.PersistentHashMap`, with bundled map and set APIs whose theorems need
no invariant hypotheses. Targets Lean **v4.32.0**; no external packages are
required.

## Usage

### Bundled map API

```lean
import VerifiedHAMT
open VerifiedHAMT
open scoped VerifiedHAMT.Map

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

`VerifiedHAMT.Map α β` bundles a native map with its number of keys and two
invariants, `Valid` (every key is in the slot its hash selects) and `Unique` (no
duplicate keys), following the
[`Std.TreeMap` / `Std.DTreeMap` design](https://lean-lang.org/doc/api/Std/Data/DTreeMap/Basic.html#Std.DTreeMap).
`∅`, `{}`, literals such as `{(1, "one")}`, `insert`, and `ofList` maintain them
automatically. Maps provide `contains`, decidable `∈`, `size`, `keys`, and the
binding relation `MapsTo`. Keys need `[BEq α] [Hashable α]`, plus `[LawfulBEq α]`
for insertion and the correctness theorems; values need no instances. The simp
lemmas are scoped: `open scoped VerifiedHAMT.Map`.

### Bundled set API

```lean
import VerifiedHAMT
open VerifiedHAMT
open scoped VerifiedHAMT.Set

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

`VerifiedHAMT.Set α` wraps `Map α Unit`, as
[`Lean.PersistentHashSet`](https://lean-lang.org/doc/api/Lean/Data/PersistentHashSet.html#Lean.PersistentHashSet)
wraps `PersistentHashMap α Unit`. It provides the corresponding operations,
including `size` and `toList`, with the same instance requirements. Its simp
lemmas are activated by `open scoped VerifiedHAMT.Set`.

### Native representation

`m.toRaw` returns the underlying `Lean.PersistentHashMap`, and `s.toRaw` the
`Lean.PersistentHashSet`; `s.toMap` and `Set.ofMap` convert between sets and
unit-valued maps. None of these rebuilds the tree. `Map.ofRaw raw hvalid hunique`
and `Set.ofRaw` import native data given proofs of both invariants, counting the
keys in linear time and memory. Maps built by upstream's `insert` come with no
such proofs.

The proof fields are erased, so at runtime a `Map` is just the native map and its
size. `lake test` checks that the bundled `Nat` insertion and lookup compile to
the same IR as direct calls on that data.

### Bundled set without values

`VerifiedHAMT.SetWithoutValArray α` uses a separate keys-only representation:
`Entry.entry key` and `Node.collision keys`, with no value fields or `vals`
arrays. It keeps the native branching factor, promotion threshold, and depth
limit, adapting this project's total insertion and membership implementations.

```lean
import VerifiedHAMT.SetWithoutValArray
open VerifiedHAMT
open scoped VerifiedHAMT.SetWithoutValArray

def compactSet : SetWithoutValArray Nat := .ofList [7, 3, 7]
#eval compactSet.contains 3 -- true
#eval compactSet.size -- 2, in constant time
#eval (compactSet.insert 10).size -- 3

example (xs : List Nat) (key : Nat) :
    (SetWithoutValArray.ofList xs).contains key = xs.contains key := by simp
```

The collection API follows `VerifiedHAMT.Set`: `empty`, literals, `insert`,
`ofList`, `contains`, decidable structural membership, `toList`, and **O(1)
`size`**. It bundles routing, uniqueness, and count-correctness proofs, so the
public theorems need no invariant hypotheses. `size_insert`, `mem_toList`,
`nodup_toList`, and `length_toList` are proved, as are the query and insertion
laws. Proof fields are erased.

Insertion reuses the existing `SizedRaw` technique: the public runtime container
carries the total count along one hash route, and a proved `@[csimp]` rewrite
selects the fused implementation. There is no separate membership traversal.
`toRaw` exports a `SetWithoutValArray.Raw` tree in constant time; `ofRaw` accepts
proofs of its invariants and counts its keys in linear time. This representation
has no zero-copy native-map bridge or `toMap`/`ofMap`.

See [the experiment](docs/SetWithoutValArray.md) for measurements and limitations,
and [the benchmark instructions](Benchmarks/README.md#keys-only-set-experiment)
to reproduce them. The existing `Set` API is unchanged.

## What is verified

| Theorem | Statement |
| --- | --- |
| `Map.contains_eq_true_iff` | `m.contains k = true ↔ k ∈ m` |
| `Map.mem_insert_iff` | `q ∈ m.insert k v ↔ q = k ∨ q ∈ m` |
| `Map.contains_insert` | `(m.insert k v).contains q = ((q == k) \|\| m.contains q)` |
| `Map.mapsTo_insert_iff` | `(m.insert k v).MapsTo q w ↔ (q = k ∧ w = v) ∨ (q ≠ k ∧ m.MapsTo q w)` |
| `Map.size_insert` | `(m.insert k v).size = if k ∈ m then m.size else m.size + 1` |
| `Map.mem_keys`, `Map.nodup_keys`, `Map.length_keys` | `m.keys` lists every key exactly once, and its length is `m.size` |

Membership `k ∈ m` and `MapsTo` are structural: the key, or the key/value pair,
is stored somewhere in the tree. They are defined independently of the
hash-directed algorithms. `Set` has the corresponding theorems, such as
`Set.mem_insert_iff`, `Set.mem_ofList`, and `Set.size_insert`. Unbundled versions
in the `VerifiedHAMT` namespace apply to any native map, taking `Valid` and `Unique`
as hypotheses; the membership results need only `Valid`.

The proofs depend only on the axioms `propext`, `Classical.choice`, and
`Quot.sound`, which the tests check, and use no `sorry`, `native_decide`, or
`implemented_by`. Sized insertion and the fused `containsThenInsert` are proved
equal to simple specifications and installed as `@[csimp]` rewrites.

## Scope

- The theorems concern this project's total `VerifiedHAMT.contains` and
  `VerifiedHAMT.insert`. These run on Lean's native `Node` and `Entry` types with
  the same hashing scheme and bucket promotion as upstream, but are not proved
  equivalent to upstream's `partial` implementations (`containsAux`,
  `insertAux`, …), which are opaque to the kernel. Tests compare against those
  at runtime only.
- Value lookup (`find?`) and deletion are not yet verified.

## Build and test

```sh
lake build
lake test
```

`lake test` checks proof examples, axiom dependencies, and compiled IR. It also
compares the verified operations with upstream and with list models under several
hash functions, including a constant one.

## Documentation

- [docs/Verification.md](docs/Verification.md): specifications, raw-map theorems,
  assumptions, relationship to upstream, and test coverage.
- [docs/Implementation.md](docs/Implementation.md): cached hashes, size
  maintenance, compiler checks, and tuning results.
- [Benchmarks/README.md](Benchmarks/README.md): benchmark workloads, measurement
  commands, and compiler inspection.

## Layout

| Path | Contents |
| --- | --- |
| `VerifiedHAMT/Basic.lean` | structural membership and bindings, `Valid`, `Unique`, empty map |
| `VerifiedHAMT/Size.lean` | structural key list and count |
| `VerifiedHAMT/Contains.lean` | total `contains` and its correctness proofs |
| `VerifiedHAMT/Bindings.lean` | `Updated` and lemmas for replacing an entries slot |
| `VerifiedHAMT/Insert.lean` | total insertion with cached hashes |
| `VerifiedHAMT/InsertProofs.lean` | invariant preservation; membership, binding, and key-count laws |
| `VerifiedHAMT/InsertSized.lean` | insertion that also updates the size |
| `VerifiedHAMT/ContainsThenInsert.lean` | fused membership test and insertion |
| `VerifiedHAMT/Map.lean`, `VerifiedHAMT/Set.lean` | bundled APIs |
| `VerifiedHAMT/SetWithoutValArray/` | keys-only bundled set, fused size maintenance, membership/uniqueness/count proofs |
| `VerifiedHAMTTests/` | proof examples, axiom and IR checks, regression tests |
| `Benchmarks/` | benchmark workloads, runner, compiler inspection |
