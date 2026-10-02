module

public import HAMTVerify.Basic
import all Lean.Data.PersistentHashMap

@[expose] public section

/-!
The keys stored in a native node, listed structurally, and their number. Under the
routing and uniqueness invariants the list has no duplicates, so its length is the
number of distinct keys. The native map does not store this number; the bundled `Map`
caches it and updates it on insertion.
-/

namespace HAMTVerify

open Lean.PersistentHashMap

variable {α : Type u} {β : Type v}

mutual
/-- The keys stored in a node, in slot order. A key stored twice, which the invariants
exclude, is listed twice. -/
def keyList : Node α β → List α
  | .entries es => entriesKeyList es
  | .collision keys _ _ => keys.toList

/-- The keys stored in an entries array. -/
def entriesKeyList : Array (Entry α β (Node α β)) → List α
  | ⟨es⟩ => entryListKeyList es

/-- The keys stored in a list of entries. -/
def entryListKeyList : List (Entry α β (Node α β)) → List α
  | [] => []
  | e :: es => entryKeyList e ++ entryListKeyList es

/-- The keys stored in an entry. -/
def entryKeyList : Entry α β (Node α β) → List α
  | .null => []
  | .entry key _ => [key]
  | .ref child => keyList child
end

/-- The number of keys stored in a node, counted structurally. It takes time and
memory linear in the size of the node. -/
def keyCount (node : Node α β) : Nat := (keyList node).length

theorem entryListKeyList_eq_flatMap (es : List (Entry α β (Node α β))) :
    entryListKeyList es = es.flatMap entryKeyList := by
  induction es with
  | nil => simp [entryListKeyList]
  | cons e es ih => simp [entryListKeyList, ih]

theorem keyList_entries (es : Array (Entry α β (Node α β))) :
    keyList (.entries es) = es.toList.flatMap entryKeyList := by
  cases es with
  | mk es => simp [keyList, entriesKeyList, entryListKeyList_eq_flatMap]

@[scoped simp] theorem keyList_collision {keys : Array α} {vals : Array β}
    {hsz : keys.size = vals.size} : keyList (.collision keys vals hsz) = keys.toList := by
  simp [keyList]

/-- An entry lists exactly its structural keys, given that its child does. -/
theorem mem_entryKeyList {key : α} {e : Entry α β (Node α β)}
    (child : ∀ c, e = .ref c → (key ∈ keyList c ↔ HasKey key c)) :
    key ∈ entryKeyList e ↔ EntryHasKey key e := by
  cases e with
  | null => simp [entryKeyList, EntryHasKey]
  | entry k v => simp [entryKeyList, EntryHasKey]
  | ref c => simpa [entryKeyList, EntryHasKey] using child c rfl

/-- The listed keys are exactly the stored keys. -/
theorem mem_keyList {hashAt : α → USize} {node : Node α β} (wf : WellFormed hashAt node)
    (key : α) : key ∈ keyList node ↔ HasKey key node := by
  induction wf generalizing key with
  | collision hashAt keys vals hsz => simp
  | @entries hashAt es size_eq routing children ih =>
    rw [keyList_entries, hasKey_entries, List.mem_flatMap]
    constructor
    · rintro ⟨e, he, hk⟩
      obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp he)
      exact ⟨i, hi, (mem_entryKeyList fun c hc => ih i hi c hc key).mp hk⟩
    · rintro ⟨i, hi, hk⟩
      exact ⟨es[i], Array.getElem_mem_toList hi,
        (mem_entryKeyList fun c hc => ih i hi c hc key).mpr hk⟩

theorem DistinctKeys.nodup_toList {keys : Array α} (h : DistinctKeys keys) :
    keys.toList.Nodup := by
  simp only [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [Array.length_toList] at hi hj
  have := h i hi j hj (by simpa using heq)
  omega

/-- A concatenation has no duplicates when no part has, and `slotOf` sends the elements
of the part at position `i` to `offset + i`. -/
private theorem nodup_flatMap_of_slots {γ : Type w} {δ : Type x} (f : γ → List δ) (slotOf : δ → Nat) :
    ∀ (l : List γ) (offset : Nat), (∀ x ∈ l, (f x).Nodup) →
      (∀ (i : Nat) (hi : i < l.length) (k : δ), k ∈ f l[i] → slotOf k = offset + i) →
      (l.flatMap f).Nodup
  | [], _, _, _ => List.nodup_nil
  | x :: l, offset, parts, slots => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨parts x (List.mem_cons_self ..),
      nodup_flatMap_of_slots f slotOf l (offset + 1)
        (fun y hy => parts y (List.mem_cons_of_mem _ hy))
        (fun i hi k hk => by
          have := slots (i + 1) (by simp; omega) k (by simpa using hk)
          omega), ?_⟩
    intro a ha b hb hab
    subst hab
    have h₁ := slots 0 (by simp) a (by simpa using ha)
    obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp hb
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have h₂ := slots (j + 1) (by simp; omega) a (by simpa using hay)
    omega

/-- Under the invariants no key is listed twice: routing separates the slots, and
uniqueness the keys of a collision node. -/
theorem nodup_keyList {hashAt : α → USize} {node : Node α β} (wf : WellFormed hashAt node)
    (hu : Unique node) : (keyList node).Nodup := by
  induction wf with
  | collision hashAt keys vals hsz =>
    cases hu with
    | collision distinct => simpa using distinct.nodup_toList
  | @entries hashAt es size_eq routing children ih =>
    cases hu with
    | entries uchildren =>
      rw [keyList_entries]
      apply nodup_flatMap_of_slots entryKeyList (fun k => slot (hashAt k)) es.toList 0
      · intro e he
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp he)
        cases hc : es[i] with
        | null => simp [entryKeyList]
        | entry k v => simp [entryKeyList]
        | ref c => simpa [entryKeyList] using ih i hi c hc (uchildren i hi c hc)
      · intro i hi k hk
        simp only [Array.length_toList] at hi
        simp only [Array.getElem_toList, Nat.zero_add] at hk ⊢
        exact routing i hi k ((mem_entryKeyList fun c hc =>
          mem_keyList (children i hi c hc) k).mp hk)

theorem keyCount_empty_root [BEq α] [Hashable α] :
    keyCount (Lean.PersistentHashMap.empty : Lean.PersistentHashMap α β).root = 0 := by
  simp [keyCount, Lean.PersistentHashMap.empty, mkEmptyEntriesArray, keyList_entries,
    List.flatMap_replicate, entryKeyList]

end HAMTVerify
