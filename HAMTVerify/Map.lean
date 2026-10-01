import HAMTVerify.InsertProofs

/-!
A persistent map with bundled routing and uniqueness invariants, analogous to
the invariant-carrying `Std.TreeMap` API. The native representation and the
unbundled theorems remain available for reasoning about arbitrary raw nodes.
-/

namespace HAMTVerify

/-- A native HAMT together with the invariants needed by the verified operations.
The proof fields are erased at runtime. Use `∅`, `insert`, and `ofList` to build
maps, or `ofRaw` when proofs for an existing native map are available. -/
structure Map (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- Explicit access to the native representation. -/
  toRaw : Lean.PersistentHashMap α β
  /-- Every stored key follows its hash route. -/
  valid : Valid toRaw
  /-- Keys are unique, so overwriting has the usual map semantics. -/
  unique : Unique toRaw.root

namespace Map

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- Bundle an existing native map with proofs of both invariants. -/
@[inline] def ofRaw (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) : Map α β :=
  ⟨raw, valid, unique⟩

/-- The empty map; also written `∅` or `{}`. -/
@[inline] def empty : Map α β :=
  ⟨Lean.PersistentHashMap.empty, valid_empty, unique_empty⟩

instance : EmptyCollection (Map α β) := ⟨empty⟩
instance : Inhabited (Map α β) := ⟨∅⟩

/-- Verified insertion, carrying both preservation proofs automatically. -/
@[inline] def insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) : Map α β :=
  ⟨HAMTVerify.insert map.toRaw key value,
    valid_insert map.toRaw map.valid key value,
    unique_insert map.toRaw map.valid map.unique key value⟩

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
  HAMTVerify.contains map.toRaw key

/-- Membership remains structural, independently of the query implementation. -/
instance : Membership α (Map α β) := ⟨fun map key => HAMTVerify.Mem key map.toRaw⟩

/-- Structural key/value membership. -/
def MapsTo (map : Map α β) (key : α) (value : β) : Prop :=
  HAMTVerify.MapsTo key value map.toRaw

@[scoped simp] theorem toRaw_ofRaw (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) :
    (ofRaw raw valid unique).toRaw = raw := rfl

@[scoped simp] theorem ofRaw_toRaw (map : Map α β) :
    ofRaw map.toRaw map.valid map.unique = map := rfl

@[scoped simp] theorem toRaw_empty : (∅ : Map α β).toRaw = Lean.PersistentHashMap.empty := rfl

@[scoped simp] theorem toRaw_insert [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).toRaw = HAMTVerify.insert map.toRaw key value := rfl

theorem contains_eq_true_iff [LawfulBEq α] (map : Map α β) (key : α) :
    map.contains key = true ↔ key ∈ map :=
  HAMTVerify.contains_eq_true_iff map.toRaw map.valid key

theorem contains_eq_false_iff [LawfulBEq α] (map : Map α β) (key : α) :
    map.contains key = false ↔ key ∉ map :=
  HAMTVerify.contains_eq_false_iff map.toRaw map.valid key

/-- Decide structural membership using the verified query. -/
instance [LawfulBEq α] (map : Map α β) (key : α) : Decidable (key ∈ map) :=
  decidable_of_iff (map.contains key = true) (contains_eq_true_iff map key)

theorem mem_iff_exists_mapsTo (map : Map α β) (key : α) :
    key ∈ map ↔ ∃ value, map.MapsTo key value :=
  hasKey_iff_exists_binding

theorem MapsTo.functional {map : Map α β} {key : α} {v w : β}
    (hv : map.MapsTo key v) (hw : map.MapsTo key w) : v = w :=
  HasBinding.functional map.valid map.unique hv hw

@[scoped simp] theorem not_mem_empty (key : α) : key ∉ (∅ : Map α β) :=
  HAMTVerify.not_mem_empty key

@[scoped simp] theorem not_mapsTo_empty (key : α) (value : β) :
    ¬ (∅ : Map α β).MapsTo key value :=
  fun h => not_mem_empty key h.hasKey

@[scoped simp] theorem contains_empty [LawfulBEq α] (key : α) :
    (∅ : Map α β).contains key = false := HAMTVerify.contains_empty key

@[scoped simp] theorem contains_insert [LawfulBEq α] (map : Map α β) (key q : α) (value : β) :
    (map.insert key value).contains q = ((q == key) || map.contains q) :=
  HAMTVerify.contains_insert map.toRaw map.valid key q value

@[scoped simp] theorem contains_insert_self [LawfulBEq α] (map : Map α β) (key : α) (value : β) :
    (map.insert key value).contains key = true :=
  HAMTVerify.contains_insert_self map.toRaw map.valid key value

@[scoped simp] theorem mem_insert_iff [LawfulBEq α] (map : Map α β) (key q : α) (value : β) :
    q ∈ map.insert key value ↔ q = key ∨ q ∈ map :=
  HAMTVerify.mem_insert_iff map.toRaw map.valid key q value

@[scoped simp] theorem mapsTo_insert_iff [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) :
    (map.insert key value).MapsTo q w ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ map.MapsTo q w) :=
  HAMTVerify.mapsTo_insert_iff map.toRaw map.valid map.unique key q value w

@[scoped simp] theorem mapsTo_insert_self [LawfulBEq α]
    (map : Map α β) (key : α) (value w : β) :
    (map.insert key value).MapsTo key w ↔ w = value :=
  HAMTVerify.mapsTo_insert_self map.toRaw map.valid map.unique key value w

theorem mapsTo_insert_of_ne [LawfulBEq α]
    (map : Map α β) (key q : α) (value w : β) (hne : q ≠ key) :
    (map.insert key value).MapsTo q w ↔ map.MapsTo q w :=
  HAMTVerify.mapsTo_insert_of_ne map.toRaw map.valid map.unique key q value w hne

end Map
end HAMTVerify
