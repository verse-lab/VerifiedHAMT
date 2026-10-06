module

public import VerifiedHAMT.SetWithoutValArray.Unique
public import VerifiedHAMT.SetWithoutValArray.InsertSized

@[expose] public section

/-! The keys-only counterpart of VerifiedHAMT.Set. The size and invariant proofs
are bundled with the raw tree, using exactly the sized traversal's runtime data. -/

/-- A verified persistent set whose nodes have no value fields or arrays.
The runtime representation is a keys-only tree and a cached count; all three
proof fields are erased. Use `empty`, `insert`, `ofList`, or `ofRaw` to build it. -/
structure VerifiedHAMT.SetWithoutValArray (α : Type u) [BEq α] [Hashable α]
    extends SetWithoutValArray.Raw.SizedRaw α where
  valid : SetWithoutValArray.Raw.Valid toRaw
  unique : SetWithoutValArray.Raw.Unique toRaw.root
  size_eq : size = SetWithoutValArray.Raw.keyCount toRaw.root

namespace VerifiedHAMT.SetWithoutValArray

variable {α : Type u} [BEq α] [Hashable α]

/-- Import a keys-only raw set with proofs of its invariants. Counting the keys
costs linear time and memory, just as for `VerifiedHAMT.Set.ofRaw`. -/
@[inline] def ofRaw (raw : Raw α) (valid : Raw.Valid raw) (unique : Raw.Unique raw.root) :
    SetWithoutValArray α :=
  ⟨⟨raw, Raw.keyCount raw.root⟩, valid, unique, rfl⟩

/-- The empty set; also written `∅` or `{}`. -/
@[inline] def empty : SetWithoutValArray α :=
  ⟨⟨Raw.empty, 0⟩, Raw.valid_empty, Raw.unique_empty, Raw.keyCount_empty_root.symm⟩

instance : EmptyCollection (SetWithoutValArray α) := ⟨empty⟩
instance : Inhabited (SetWithoutValArray α) := ⟨∅⟩

/-- Insert and update the cached size in one hash-directed traversal.
The public container is passed directly to the sized worker after proof erasure. -/
@[inline] def insert [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    SetWithoutValArray α :=
  let result := Raw.insertSized set.toSizedRaw key
  ⟨result, Raw.valid_insert set.toRaw set.valid key,
    Raw.unique_insert set.toRaw set.valid set.unique key, by
      change (if Raw.contains set.toRaw key then set.size else set.size + 1) =
        Raw.keyCount (Raw.insert set.toRaw key).root
      rw [Raw.keyCount_insert set.toRaw set.valid set.unique, ← set.size_eq]⟩

instance [LawfulBEq α] : Singleton α (SetWithoutValArray α) := ⟨fun key => empty.insert key⟩
instance [LawfulBEq α] : Insert α (SetWithoutValArray α) := ⟨fun key set => set.insert key⟩
instance [LawfulBEq α] : LawfulSingleton α (SetWithoutValArray α) := ⟨fun _ => rfl⟩

@[inline] def ofList [LawfulBEq α] (keys : List α) : SetWithoutValArray α :=
  keys.foldl insert ∅

@[inline] def contains (set : SetWithoutValArray α) (key : α) : Bool :=
  Raw.contains set.toRaw key

/-- Enumerate in native slot order, matching `VerifiedHAMT.Set.toList`. -/
def toList (set : SetWithoutValArray α) : List α := Raw.keyList set.toRaw.root

instance : Membership α (SetWithoutValArray α) := ⟨fun set key => Raw.Mem key set.toRaw⟩

theorem contains_eq_true_iff [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    set.contains key = true ↔ key ∈ set := Raw.contains_eq_true_iff set.toRaw set.valid key

theorem contains_eq_false_iff [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    set.contains key = false ↔ key ∉ set := Raw.contains_eq_false_iff set.toRaw set.valid key

instance [LawfulBEq α] (set : SetWithoutValArray α) (key : α) : Decidable (key ∈ set) :=
  decidable_of_iff (set.contains key = true) (contains_eq_true_iff set key)

@[scoped simp] theorem toRaw_ofRaw (raw : Raw α)
    (valid : Raw.Valid raw) (unique : Raw.Unique raw.root) :
    (ofRaw raw valid unique).toRaw = raw := rfl

@[scoped simp] theorem ofRaw_toRaw (set : SetWithoutValArray α) :
    ofRaw set.toRaw set.valid set.unique = set := by
  cases set with
  | mk data valid unique size_eq =>
    cases data with
    | mk raw size =>
      change size = Raw.keyCount raw.root at size_eq
      subst size
      rfl

@[scoped simp] theorem size_ofRaw (raw : Raw α)
    (valid : Raw.Valid raw) (unique : Raw.Unique raw.root) :
    (ofRaw raw valid unique).size = Raw.keyCount raw.root := rfl

@[scoped simp] theorem empty_eq_emptyc : (empty : SetWithoutValArray α) = ∅ := rfl

@[scoped simp] theorem toRaw_empty : (∅ : SetWithoutValArray α).toRaw = Raw.empty := rfl

@[scoped simp] theorem toRaw_insert [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).toRaw = Raw.insert set.toRaw key := rfl

@[scoped simp] theorem not_mem_empty (key : α) : key ∉ (∅ : SetWithoutValArray α) :=
  Raw.not_mem_empty key

theorem mem_toList (set : SetWithoutValArray α) (key : α) : key ∈ set.toList ↔ key ∈ set :=
  Raw.mem_keyList set.valid key

theorem nodup_toList (set : SetWithoutValArray α) : set.toList.Nodup :=
  Raw.nodup_keyList set.valid set.unique

/-- The cached count is exactly the number of distinct stored keys. -/
theorem length_toList (set : SetWithoutValArray α) : set.toList.length = set.size :=
  set.size_eq.symm

@[scoped simp] theorem size_empty : (∅ : SetWithoutValArray α).size = 0 := rfl

theorem size_insert [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).size = if key ∈ set then set.size else set.size + 1 := by
  change (if set.contains key then set.size else set.size + 1) = _
  by_cases h : key ∈ set
  · rw [if_pos ((contains_eq_true_iff set key).mpr h), if_pos h]
  · rw [if_neg (mt (contains_eq_true_iff set key).mp h), if_neg h]

@[scoped simp] theorem contains_empty [LawfulBEq α] (key : α) :
    (∅ : SetWithoutValArray α).contains key = false := Raw.contains_empty key

@[scoped simp] theorem contains_insert [LawfulBEq α] (set : SetWithoutValArray α) (key q : α) :
    (set.insert key).contains q = ((q == key) || set.contains q) :=
  Raw.contains_insert set.toRaw set.valid key q

@[scoped simp] theorem contains_insert_self [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    (set.insert key).contains key = true := Raw.contains_insert_self set.toRaw set.valid key

@[scoped simp] theorem mem_insert_iff [LawfulBEq α] (set : SetWithoutValArray α) (key q : α) :
    q ∈ set.insert key ↔ q = key ∨ q ∈ set := Raw.mem_insert_iff set.toRaw set.valid key q

@[scoped simp] theorem mem_insert_self [LawfulBEq α] (set : SetWithoutValArray α) (key : α) :
    key ∈ set.insert key := (mem_insert_iff set key key).mpr (Or.inl rfl)

@[scoped simp] theorem mem_singleton [LawfulBEq α] (key q : α) :
    q ∈ ({key} : SetWithoutValArray α) ↔ q = key := by
  change q ∈ (∅ : SetWithoutValArray α).insert key ↔ q = key
  simp

theorem mem_foldl_insert [LawfulBEq α] (keys : List α) (set : SetWithoutValArray α) (q : α) :
    q ∈ keys.foldl insert set ↔ q ∈ set ∨ q ∈ keys := by
  induction keys generalizing set with
  | nil => simp
  | cons key keys ih =>
    simp only [List.foldl_cons, ih, mem_insert_iff, List.mem_cons]
    simp only [or_assoc, or_left_comm]

@[scoped simp] theorem mem_ofList [LawfulBEq α] (keys : List α) (key : α) :
    key ∈ ofList keys ↔ key ∈ keys := by simp [ofList, mem_foldl_insert]

@[scoped simp] theorem contains_ofList [LawfulBEq α] (keys : List α) (key : α) :
    (ofList keys).contains key = keys.contains key := by
  apply Bool.eq_iff_iff.mpr
  simp only [contains_eq_true_iff, mem_ofList, List.contains_iff_mem]

end VerifiedHAMT.SetWithoutValArray
