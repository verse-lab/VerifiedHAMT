module

public import VerifiedHAMT.InsertSized

@[expose] public section

/-!
Fused membership and insertion reuse the sized traversal. Starting its accumulator
at zero yields zero for an existing key and one for a new key, so the membership
result is produced only at the outer API boundary. Bundled maps pass their actual
size directly to `insertSized`, avoiding this final pair as well.
-/

namespace VerifiedHAMT

variable {α : Type u} {β : Type v}

/-- Executable fused operation. The temporary size container is reused during
recursion; the Boolean result is constructed once, after insertion finishes. -/
def containsThenInsertImpl [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β)
    (key : α) (value : β) : Bool × Lean.PersistentHashMap α β :=
  let result := insertSizedImpl ⟨map, 0⟩ key value
  (result.size == 0, result.toRaw)

/-- Return whether the key was present and the updated map. The compiler uses the
single-traversal implementation via the equality proved below. -/
def containsThenInsert [BEq α] [Hashable α] (map : Lean.PersistentHashMap α β)
    (key : α) (value : β) : Bool × Lean.PersistentHashMap α β :=
  (contains map key, insert map key value)

/-- This equality is valid even for malformed nodes and unlawful key equality. -/
@[csimp] theorem containsThenInsert_eq_impl : @containsThenInsert = @containsThenInsertImpl := by
  funext α β _ _ map key value
  simp only [containsThenInsert, containsThenInsertImpl, insertSizedImpl,
    insertSizedRaw_eq, contains, insert]
  cases containsNode map.root (hash key).toUSize key <;> rfl

end VerifiedHAMT
