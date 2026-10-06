module

public import VerifiedHAMT.InsertProofs
public import VerifiedHAMT.ContainsThenInsert
import all Lean.Data.PersistentHashMap

@[expose] public section

/-!
A persistent map with bundled routing and uniqueness invariants and its number of
keys, analogous to the invariant-carrying `Std.TreeMap` API. The native representation
and the unbundled theorems remain available for reasoning about arbitrary raw nodes.
-/

namespace VerifiedHAMT

/-- A native HAMT together with the invariants needed by the verified operations and
its number of keys, which the native map does not store. The proof fields are erased
at runtime; the native map and the size remain. Use `∅`, `insert`, and `ofList` to build
maps, or `ofRaw` when proofs for an existing native map are available. -/
structure Map (α : Type u) (β : Type v) [BEq α] [Hashable α] extends SizedRaw α β where
  /-- Every stored key follows its hash route. -/
  valid : Valid toRaw
  /-- Keys are unique, so overwriting has the usual map semantics. -/
  unique : Unique toRaw.root
  /-- `size` counts the keys stored in the native tree. -/
  size_eq : size = keyCount toRaw.root

namespace Map

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- Bundle an existing native map with proofs of both invariants. Its keys are counted,
in time and memory linear in the size of the map. -/
@[inline] def ofRaw (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) : Map α β :=
  ⟨⟨raw, keyCount raw.root⟩, valid, unique, rfl⟩

/-- `unique_empty`, stated for the root of the native empty map: the body of `empty` below
is exposed, so it cannot unfold the unexposed `Lean.PersistentHashMap.empty` itself. -/
theorem unique_empty_root : Unique (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β).root :=
  unique_empty

/-- The empty map; also written `∅` or `{}`. -/
@[inline] def empty : Map α β :=
  ⟨⟨Lean.PersistentHashMap.empty, 0⟩, valid_empty, unique_empty_root, keyCount_empty_root.symm⟩

instance : EmptyCollection (Map α β) := ⟨empty⟩
instance : Inhabited (Map α β) := ⟨∅⟩

/-- Verified insertion, carrying the preservation proofs automatically. The tree
and size are updated together in one traversal using a reusable container. -/
@[inline] def insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) : Map α β :=
  let result := VerifiedHAMT.insertSized map.toSizedRaw key value
  ⟨result,
    valid_insert map.toRaw map.valid key value,
    unique_insert map.toRaw map.valid map.unique key value,
    by
      change (if VerifiedHAMT.contains map.toRaw key then map.size else map.size + 1) =
        keyCount (VerifiedHAMT.insert map.toRaw key value).root
      rw [keyCount_insert map.toRaw map.valid map.unique, ← map.size_eq]⟩

instance [LawfulBEq α] : Singleton (α × β) (Map α β) :=
  ⟨fun kv => (∅ : Map α β).insert kv.1 kv.2⟩

instance [LawfulBEq α] : Insert (α × β) (Map α β) :=
  ⟨fun kv map => map.insert kv.1 kv.2⟩

instance [LawfulBEq α] : LawfulSingleton (α × β) (Map α β) := ⟨fun _ => rfl⟩

/-- Build a map in list order. Later occurrences of a key overwrite earlier ones. -/
@[inline] def ofList [LawfulBEq α] (bindings : List (α × β)) : Map α β :=
  bindings.foldl (fun map kv => map.insert kv.1 kv.2) ∅

/-- The verified hash-directed membership query. -/
@[inline] def contains (map : Map α β) (key : α) : Bool :=
  VerifiedHAMT.contains map.toRaw key

/-- Membership remains structural, independently of the query implementation. -/
instance : Membership α (Map α β) := ⟨fun map key => VerifiedHAMT.Mem key map.toRaw⟩

/-- Structural key/value membership. -/
def MapsTo (map : Map α β) (key : α) (value : β) : Prop :=
  VerifiedHAMT.MapsTo key value map.toRaw

/-- The keys, in the order of the native tree. -/
def keys (map : Map α β) : List α := keyList map.toRaw.root

@[scoped simp] theorem toRaw_ofRaw (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) :
    (ofRaw raw valid unique).toRaw = raw := rfl

@[scoped simp] theorem ofRaw_toRaw (map : Map α β) :
    ofRaw map.toRaw map.valid map.unique = map := by
  cases map with
  | mk data valid unique size_eq =>
    cases data with
    | mk raw size =>
      change size = keyCount raw.root at size_eq
      subst size
      rfl

@[scoped simp] theorem size_ofRaw (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) :
    (ofRaw raw valid unique).size = keyCount raw.root := rfl

@[scoped simp] theorem toRaw_empty : (∅ : Map α β).toRaw = Lean.PersistentHashMap.empty := rfl

@[scoped simp] theorem toRaw_insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).toRaw = VerifiedHAMT.insert map.toRaw key value := rfl

theorem contains_eq_true_iff [LawfulBEq α] (map : Map α β) (key : α) :
    map.contains key = true ↔ key ∈ map :=
  VerifiedHAMT.contains_eq_true_iff map.toRaw map.valid key

theorem contains_eq_false_iff [LawfulBEq α] (map : Map α β) (key : α) :
    map.contains key = false ↔ key ∉ map :=
  VerifiedHAMT.contains_eq_false_iff map.toRaw map.valid key

/-- Decide structural membership using the verified query. -/
instance [LawfulBEq α] (map : Map α β) (key : α) : Decidable (key ∈ map) :=
  decidable_of_iff (map.contains key = true) (contains_eq_true_iff map key)

theorem mem_keys (map : Map α β) (key : α) : key ∈ map.keys ↔ key ∈ map :=
  mem_keyList map.valid key

theorem nodup_keys (map : Map α β) : map.keys.Nodup :=
  nodup_keyList map.valid map.unique

/-- `size` is the number of keys. -/
theorem length_keys (map : Map α β) : map.keys.length = map.size :=
  map.size_eq.symm

theorem mem_iff_exists_mapsTo (map : Map α β) (key : α) :
    key ∈ map ↔ ∃ value, map.MapsTo key value :=
  hasKey_iff_exists_binding

theorem MapsTo.functional {map : Map α β} {key : α} {v w : β}
    (hv : map.MapsTo key v) (hw : map.MapsTo key w) : v = w :=
  HasBinding.functional map.valid map.unique hv hw

@[scoped simp] theorem not_mem_empty (key : α) : key ∉ (∅ : Map α β) :=
  VerifiedHAMT.not_mem_empty key

@[scoped simp] theorem not_mapsTo_empty (key : α) (value : β) :
    ¬ (∅ : Map α β).MapsTo key value :=
  fun h => not_mem_empty key h.hasKey

@[scoped simp] theorem contains_empty [LawfulBEq α] (key : α) :
    (∅ : Map α β).contains key = false := VerifiedHAMT.contains_empty key

@[scoped simp] theorem size_empty : (∅ : Map α β).size = 0 := rfl

theorem size_insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).size = if key ∈ map then map.size else map.size + 1 := by
  change (if map.contains key then map.size else map.size + 1) = _
  by_cases h : key ∈ map
  · rw [if_pos ((contains_eq_true_iff map key).mpr h), if_pos h]
  · rw [if_neg (mt (contains_eq_true_iff map key).mp h), if_neg h]

@[scoped simp] theorem contains_insert [LawfulBEq α] (map : Map α β) (key q : α) (value : β) :
    (map.insert key value).contains q = ((q == key) || map.contains q) :=
  VerifiedHAMT.contains_insert map.toRaw map.valid key q value

@[scoped simp] theorem contains_insert_self [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).contains key = true :=
  VerifiedHAMT.contains_insert_self map.toRaw map.valid key value

@[scoped simp] theorem mem_insert_iff [LawfulBEq α] (map : Map α β) (key q : α) (value : β) :
    q ∈ map.insert key value ↔ q = key ∨ q ∈ map :=
  VerifiedHAMT.mem_insert_iff map.toRaw map.valid key q value

@[scoped simp] theorem mapsTo_insert_iff [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) :
    (map.insert key value).MapsTo q w ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ map.MapsTo q w) :=
  VerifiedHAMT.mapsTo_insert_iff map.toRaw map.valid map.unique key q value w

@[scoped simp] theorem mapsTo_insert_self [LawfulBEq α]
    (map : Map α β) (key : α) (value w : β) :
    (map.insert key value).MapsTo key w ↔ w = value :=
  VerifiedHAMT.mapsTo_insert_self map.toRaw map.valid map.unique key value w

theorem mapsTo_insert_of_ne [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) (hne : q ≠ key) :
    (map.insert key value).MapsTo q w ↔ map.MapsTo q w :=
  VerifiedHAMT.mapsTo_insert_of_ne map.toRaw map.valid map.unique key q value w hne

end Map
end VerifiedHAMT
