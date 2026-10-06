import Lean
import VerifiedHAMT

/-!
Compiler regression check, not a logical theorem: in the compiled insertion
traversals, every path to a recursive call first clears an entries slot by
writing `Entry.null`. Clearing first keeps an unshared child unshared during the
recursive call, so that it can be updated in place. The compiler may move this
pure write after the call, so the order depends on the shape of `insertEntries`
and `insertSizedEntries`. It is checked on the generic workers and on the `Nat`
specializations created by the entry points below.
-/

namespace VerifiedHAMT.ReleaseIRTests

open Lean IR

/-- Makes the compiler specialize the plain traversals for `Nat`. -/
def natInsert (map : Lean.PersistentHashMap Nat Nat) (key value : Nat) :
    Lean.PersistentHashMap Nat Nat :=
  VerifiedHAMT.insert map key value

/-- Makes the compiler specialize the sized traversals for `Nat`. -/
def natSizedInsert (s : SizedRaw Nat Nat) (key value : Nat) : SizedRaw Nat Nat :=
  VerifiedHAMT.insertSizedImpl s key value

def natKeysOnlyInsert (s : SetWithoutValArray Nat) (key : Nat) : SetWithoutValArray Nat :=
  s.insert key

def natKeysOnlyRawInsert (s : SetWithoutValArray.Raw Nat) (key : Nat) : SetWithoutValArray.Raw Nat :=
  s.insert key

/-- Count the recursive calls on every path through a function body, failing
when one is reached before an array write of `Entry.null`. Join points are
followed at each jump. -/
partial def countGuardedCalls (self : Array Name) (jps : Std.HashMap JoinPointId FnBody)
    (nulls : Std.HashSet VarId) (cleared : Bool) : FnBody → Except String Nat
  | .vdecl x _ e b =>
    match e with
    | .ctor info _ =>
      let nulls := if info.name == ``Lean.PersistentHashMap.Entry.null ||
          info.name == ``VerifiedHAMT.SetWithoutValArray.Entry.null then nulls.insert x else nulls
      countGuardedCalls self jps nulls cleared b
    | .fap f ys =>
      if self.contains f then
        if cleared then (· + 1) <$> countGuardedCalls self jps nulls cleared b
        else throw s!"recursive call to {f} before an entries slot is cleared"
      else
        let clears := f == ``Array.set && ys.any fun
          | .var y => nulls.contains y
          | .erased => false
        countGuardedCalls self jps nulls (cleared || clears) b
    | _ => countGuardedCalls self jps nulls cleared b
  | .jdecl j _ v b => countGuardedCalls self (jps.insert j v) nulls cleared b
  | .case _ _ _ alts =>
    alts.foldlM (init := 0) fun n alt =>
      (n + ·) <$> countGuardedCalls self jps nulls cleared alt.body
  | .jmp j _ =>
    match jps[j]? with
    | some v => countGuardedCalls self jps nulls cleared v
    | none => throw s!"unknown join point {j}"
  | .ret _ | .unreachable => pure 0
  | b => countGuardedCalls self jps nulls cleared b.body

/-- The traversals that recurse through an entries slot. -/
def traversals : Array Name :=
  #[``VerifiedHAMT.insertNoExpand, ``VerifiedHAMT.insertNode,
    ``VerifiedHAMT.insertSizedNoExpand, ``VerifiedHAMT.insertSizedRaw,
    ``VerifiedHAMT.SetWithoutValArray.Raw.insertNoExpand, ``VerifiedHAMT.SetWithoutValArray.Raw.insertNode,
    ``VerifiedHAMT.SetWithoutValArray.Raw.insertSizedNoExpand,
    ``VerifiedHAMT.SetWithoutValArray.Raw.insertSizedRaw]

run_meta do
  let env ← getEnv
  -- The compiler's `_redArg` worker of each traversal contains its recursion.
  let isWorker (name : Name) := (name matches .str _ "_redArg") ||
    ((`VerifiedHAMT.SetWithoutValArray).isPrefixOf name &&
      match name with
      | .str _ s => s.startsWith "spec_"
      | _ => false)
  let generic := traversals.map (· ++ `_redArg)
  let specialized := (declMapExt.getEntries env).toArray.filterMap fun decl =>
    if isWorker decl.name && traversals.any (·.isPrefixOf decl.name) then
      some decl.name
    else none
  for t in traversals do
    unless specialized.any (t.isPrefixOf ·) do
      throwError "No Nat specialization of {t} found; review this check"
  for name in generic ++ specialized do
    let some (.fdecl _ _ _ body _) := findEnvDecl env name
      | throwError "Missing function IR for {name}"
    match countGuardedCalls #[name, name.getPrefix] {} {} false body with
    | .error e => throwError "{name}: {e}"
    | .ok 0 => throwError "{name}: no recursive call found; review this check"
    | .ok _ => pure ()

end VerifiedHAMT.ReleaseIRTests
