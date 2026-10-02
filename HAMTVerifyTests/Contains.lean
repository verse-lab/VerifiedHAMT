import HAMTVerify
import HAMTVerifyTests.Insert
import HAMTVerifyTests.ModifyIR
import HAMTVerifyTests.MapIR
import HAMTVerifyTests.SetIR

/-!
Kernel-checked examples and executable comparisons against the upstream partial
implementation. Runtime comparisons are regression tests, not refinement proofs.
Run with `lake test`.
-/

namespace HAMTVerify.Tests

open Lean.PersistentHashMap

-- A nonempty native collision node satisfies the invariant for any remaining
-- hash, and the main correctness theorem applies even with duplicate keys.
private def bucket : Node Nat Nat := .collision #[2, 7, 2] #[20, 70, 21] rfl

example (hashAt : Nat → USize) : WellFormed hashAt bucket :=
  .collision _ _ _ _

example (hashAt : Nat → USize) (key : Nat) :
    containsNode bucket (hashAt key) key = true ↔ key = 2 ∨ key = 7 := by
  unfold bucket
  rw [containsNode_eq_true_iff (.collision _ _ _ _)]
  simp [or_comm]

-- The suffix specification includes the empty suffix and out-of-range offsets.
example : (#[2, 7, 2].drop 1).contains 2 = true := by simp
example : (#[2, 7, 2].drop 3).contains 2 = false := by simp
example : (#[2, 7, 2].drop 20).contains 2 = false := by simp

-- Membership is independent of routing. A misplaced key is genuinely present,
-- but traversal can miss it; the validity hypothesis cannot simply be dropped.
private def misplaced : Node Nat Nat :=
  .entries (Array.replicate 32 .null |>.set 1 (.entry 7 70) (by decide))

example : HasKey 7 misplaced :=
  HasKey.entry (i := 1) (hi := by decide) (v := 70) (by simp)

example : containsNode misplaced 0 7 = false := by
  simp [containsNode_entries, misplaced]

-- Malformed short arrays are handled by the total version's explicit check.
example : containsNode (.entries (#[] : Array (Entry Nat Nat (Node Nat Nat)))) 0 7 = false := by
  simp [containsNode]

/-- info: 'HAMTVerify.contains_eq_true_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.contains_eq_true_iff
/-- info: 'HAMTVerify.contains_eq_false_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.contains_eq_false_iff
/-- info: 'HAMTVerify.slot_lt_branching' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HAMTVerify.slot_lt_branching

private def checkQueries [Hashable Nat] (label : String)
    (map : Lean.PersistentHashMap Nat Nat) (expected : List Nat) : IO Nat := do
  for key in [0:80] do
    let verified := HAMTVerify.contains map key
    let upstream := map.contains key
    let model := expected.contains key
    unless verified == model && upstream == model do
      throw <| IO.userError s!"{label}: key {key}: verified={verified}, upstream={upstream}, model={model}"
  return 80

private def checkSequence (label : String) (hashFn : Nat → UInt64) : IO Nat := do
  let _ : Hashable Nat := ⟨hashFn⟩
  let mut map : Lean.PersistentHashMap Nat Nat := {}
  let mut expected : List Nat := []
  let mut checks ← checkQueries s!"{label}/empty" map expected
  -- A permutation of 0..63 creates branches in a nonmonotone order.
  for step in [0:64] do
    let key := (step * 37) % 64
    let oldMap := map
    let oldExpected := expected
    map := map.insert key (key * 10)
    expected := key :: expected
    checks := checks + (← checkQueries s!"{label}/insert/{key}" map expected)
    checks := checks + (← checkQueries s!"{label}/snapshot/{key}" oldMap oldExpected)
  -- Replacing values must not affect membership.
  for key in [0:32] do
    map := map.insert key (key + 1000)
    checks := checks + (← checkQueries s!"{label}/replace/{key}" map expected)
  -- Includes absent keys and eventually empty buckets and collapsed branches.
  for step in [0:80] do
    let key := (step * 37) % 80
    map := map.erase key
    expected := expected.filter (· != key)
    checks := checks + (← checkQueries s!"{label}/erase/{key}" map expected)
  return checks

def run : IO Unit := do
  let mut checks := 0
  checks := checks + (← checkSequence "default-hash" hash)
  checks := checks + (← checkSequence "identity-hash" Nat.toUInt64)
  checks := checks + (← checkSequence "shared-prefix" (fun n => n.toUInt64 <<< 15))
  checks := checks + (← checkSequence "complete-collisions" (fun _ => 0))
  checks := checks + (← checkSequence "high-bits" (fun n => n.toUInt64 <<< 60))
  IO.println s!"contains: {checks} comparisons passed (total implementation, upstream, list model)."

end HAMTVerify.Tests

def main : IO Unit := do
  HAMTVerify.Tests.run
  HAMTVerify.InsertTests.run
  HAMTVerify.MapTests.run
  HAMTVerify.SetTests.run
