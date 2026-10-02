# HAMTVerify

Verified membership queries and insertion for Lean's native hash array mapped
trie, `Lean.PersistentHashMap`, with bundled map and set APIs whose theorems need
no invariant hypotheses. Targets Lean **v4.32.0**; no external packages are
required.

## Usage

### Bundled map API

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

`HAMTVerify.Map α β` bundles a native map with its number of keys and two
invariants, `Valid` (every key is in the slot its hash selects) and `Unique` (no
duplicate keys), following the
[`Std.TreeMap` / `Std.DTreeMap` design](https://lean-lang.org/doc/api/Std/Data/DTreeMap/Basic.html#Std.DTreeMap).
`∅`, `{}`, literals such as `{(1, "one")}`, `insert`, and `ofList` maintain them
automatically. Maps provide `contains`, decidable `∈`, `size`, `keys`, and the
binding relation `MapsTo`. Keys need `[BEq α] [Hashable α]`, plus `[LawfulBEq α]`
for insertion and the correctness theorems; values need no instances. The simp
lemmas are scoped: `open scoped HAMTVerify.Map`.

### Bundled set API

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

`HAMTVerify.Set α` wraps `Map α Unit`, as
[`Lean.PersistentHashSet`](https://lean-lang.org/doc/api/Lean/Data/PersistentHashSet.html#Lean.PersistentHashSet)
wraps `PersistentHashMap α Unit`. It provides the corresponding operations,
including `size` and `toList`, with the same instance requirements. Its simp
lemmas are activated by `open scoped HAMTVerify.Set`.

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
in the `HAMTVerify` namespace apply to any native map, taking `Valid` and `Unique`
as hypotheses; the membership results need only `Valid`.

The proofs depend only on the axioms `propext`, `Classical.choice`, and
`Quot.sound`, which the tests check. They use no `sorry`, `native_decide`, or
`implemented_by`. Optimized executable code is proved equal to simpler models,
and two of these equalities serve as `@[csimp]` rewrites.

## Scope

- The theorems concern this project's total `HAMTVerify.contains` and
  `HAMTVerify.insert`. These run on Lean's native `Node` and `Entry` types with
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

`lake test` checks proof examples, axiom dependencies, and the compiled IR of the
bundled API. It also compares the verified operations with upstream and with list
models under several hash functions, including a constant one.

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
| `HAMTVerify/Basic.lean` | structural membership, `Valid`, empty map |
| `HAMTVerify/Size.lean` | structural key list and count |
| `HAMTVerify/Contains.lean` | total `contains` and its correctness proofs |
| `HAMTVerify/Bindings.lean` | structural key/value bindings, `Unique` |
| `HAMTVerify/Insert.lean` | total insertion: proof model and cached-hash implementation |
| `HAMTVerify/InsertProofs.lean` | invariant preservation, membership and binding laws |
| `HAMTVerify/InsertSized.lean` | insertion that also updates the size |
| `HAMTVerify/ContainsThenInsert.lean` | fused membership test and insertion |
| `HAMTVerify/Map.lean`, `HAMTVerify/Set.lean` | bundled APIs |
| `HAMTVerifyTests/` | proof examples, axiom and IR checks, regression tests |
| `Benchmarks/` | benchmark workloads, runner, compiler inspection |
