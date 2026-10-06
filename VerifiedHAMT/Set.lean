module

public import VerifiedHAMT.Map
public import Lean.Data.PersistentHashSet
import all Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashSet

@[expose] public section

/-!
A verified persistent set backed by `Map α Unit`, following the representation
of Lean's `PersistentHashSet`. Routing and uniqueness proofs and the size live in
the map; set operations reuse its verified implementation and preservation theorems.
-/

namespace VerifiedHAMT

/-- A persistent set carrying the invariants of its underlying verified map. -/
structure Set (α : Type u) [BEq α] [Hashable α] where
  toMap : Map α Unit

namespace Set

variable {α : Type u} [BEq α] [Hashable α]

/-- View a verified unit-valued map as a set, without rebuilding it. -/
@[inline] def ofMap (map : Map α Unit) : Set α := ⟨map⟩

/-- Explicitly export the native persistent-set representation. -/
@[inline] def toRaw (set : Set α) : Lean.PersistentHashSet α := ⟨set.toMap.toRaw⟩

/-- Import a native set when both map invariants have been established. Its elements
are counted, in time and memory linear in the size of the set. -/
@[inline] def ofRaw (raw : Lean.PersistentHashSet α)
    (valid : Valid raw.set) (unique : Unique raw.set.root) : Set α :=
  ⟨Map.ofRaw raw.set valid unique⟩

/-- The empty set; also written `∅` or `{}`. -/
@[inline] def empty : Set α := ⟨∅⟩

instance : EmptyCollection (Set α) := ⟨empty⟩
instance : Inhabited (Set α) := ⟨∅⟩

/-- Insert an element, maintaining the invariants and the size automatically. -/
@[inline] def insert [LawfulBEq α] (set : Set α) (key : α) : Set α :=
  ⟨set.toMap.insert key ()⟩

instance [LawfulBEq α] : Singleton α (Set α) := ⟨fun key => (∅ : Set α).insert key⟩
instance [LawfulBEq α] : Insert α (Set α) := ⟨fun key set => set.insert key⟩
instance [LawfulBEq α] : LawfulSingleton α (Set α) := ⟨fun _ => rfl⟩

/-- Build a set by inserting the elements in list order. -/
@[inline] def ofList [LawfulBEq α] (keys : List α) : Set α :=
  keys.foldl insert ∅

/-- The verified hash-directed membership query. -/
@[inline] def contains (set : Set α) (key : α) : Bool := set.toMap.contains key

/-- The number of elements. -/
@[inline] def size (set : Set α) : Nat := set.toMap.size

/-- The elements, in the order of the native tree. -/
def toList (set : Set α) : List α := set.toMap.keys

/-- Structural membership inherited from the underlying map. -/
instance : Membership α (Set α) := ⟨fun set key => key ∈ set.toMap⟩

instance [LawfulBEq α] (set : Set α) (key : α) : Decidable (key ∈ set) :=
  inferInstanceAs (Decidable (key ∈ set.toMap))

@[scoped simp] theorem toMap_ofMap (map : Map α Unit) : (ofMap map).toMap = map := rfl

@[scoped simp] theorem ofMap_toMap (set : Set α) : ofMap set.toMap = set := rfl

@[scoped simp] theorem toRaw_ofRaw (raw : Lean.PersistentHashSet α)
    (valid : Valid raw.set) (unique : Unique raw.set.root) :
    (ofRaw raw valid unique).toRaw = raw := rfl

@[scoped simp] theorem ofRaw_toRaw (set : Set α) :
    ofRaw set.toRaw set.toMap.valid set.toMap.unique = set :=
  congrArg Set.mk (Map.ofRaw_toRaw set.toMap)

@[scoped simp] theorem empty_eq_emptyc : (empty : Set α) = ∅ := rfl

@[scoped simp] theorem toRaw_empty :
    (∅ : Set α).toRaw = Lean.PersistentHashSet.empty := (rfl)

@[scoped simp] theorem toMap_insert [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).toMap = set.toMap.insert key () := rfl

@[scoped simp] theorem toRaw_insert [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).toRaw = ⟨VerifiedHAMT.insert set.toMap.toRaw key ()⟩ := rfl

theorem contains_eq_true_iff [LawfulBEq α] (set : Set α) (key : α) :
    set.contains key = true ↔ key ∈ set := Map.contains_eq_true_iff set.toMap key

theorem contains_eq_false_iff [LawfulBEq α] (set : Set α) (key : α) :
    set.contains key = false ↔ key ∉ set := Map.contains_eq_false_iff set.toMap key

@[scoped simp] theorem not_mem_empty (key : α) : key ∉ (∅ : Set α) :=
  Map.not_mem_empty key

theorem mem_toList (set : Set α) (key : α) : key ∈ set.toList ↔ key ∈ set :=
  Map.mem_keys set.toMap key

theorem nodup_toList (set : Set α) : set.toList.Nodup := Map.nodup_keys set.toMap

/-- `size` is the number of elements. -/
theorem length_toList (set : Set α) : set.toList.length = set.size :=
  Map.length_keys set.toMap

@[scoped simp] theorem size_empty : (∅ : Set α).size = 0 := rfl

theorem size_insert [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).size = if key ∈ set then set.size else set.size + 1 :=
  Map.size_insert set.toMap key ()

@[scoped simp] theorem contains_empty [LawfulBEq α] (key : α) :
    (∅ : Set α).contains key = false := Map.contains_empty key

@[scoped simp] theorem contains_insert [LawfulBEq α] (set : Set α) (key q : α) :
    (set.insert key).contains q = ((q == key) || set.contains q) :=
  Map.contains_insert set.toMap key q ()

@[scoped simp] theorem contains_insert_self [LawfulBEq α] (set : Set α) (key : α) :
    (set.insert key).contains key = true := Map.contains_insert_self set.toMap key ()

@[scoped simp] theorem mem_insert_iff [LawfulBEq α] (set : Set α) (key q : α) :
    q ∈ set.insert key ↔ q = key ∨ q ∈ set := Map.mem_insert_iff set.toMap key q ()

@[scoped simp] theorem mem_insert_self [LawfulBEq α] (set : Set α) (key : α) :
    key ∈ set.insert key := (mem_insert_iff set key key).mpr (Or.inl rfl)

@[scoped simp] theorem mem_singleton [LawfulBEq α] (key q : α) :
    q ∈ ({key} : Set α) ↔ q = key := by
  change q ∈ (∅ : Set α).insert key ↔ q = key
  simp

/-- Membership in a bulk insertion is membership in the old set or input list. -/
theorem mem_foldl_insert [LawfulBEq α] (keys : List α) (set : Set α) (q : α) :
    q ∈ keys.foldl insert set ↔ q ∈ set ∨ q ∈ keys := by
  induction keys generalizing set with
  | nil => simp
  | cons key keys ih =>
    simp only [List.foldl_cons, ih, mem_insert_iff, List.mem_cons]
    simp only [or_assoc, or_left_comm]

@[scoped simp] theorem mem_ofList [LawfulBEq α] (keys : List α) (key : α) :
    key ∈ ofList keys ↔ key ∈ keys := by
  simp [ofList, mem_foldl_insert]

@[scoped simp] theorem contains_ofList [LawfulBEq α] (keys : List α) (key : α) :
    (ofList keys).contains key = keys.contains key := by
  apply Bool.eq_iff_iff.mpr
  simp only [contains_eq_true_iff, mem_ofList, List.contains_iff_mem]

end Set
end VerifiedHAMT
