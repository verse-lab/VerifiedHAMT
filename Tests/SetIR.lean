import Lean
import Tests.Set

/-! Check erasure of the Set and Map wrappers and invariant proofs. This is a
compiler regression check against our total map operations, not an equivalence
theorem about the native partial set implementation. -/

open Lean in
run_meta do
  let env ← getEnv
  let normalized := fun (decl : IR.Decl) =>
    match decl with
    | .fdecl _ params result body info =>
      some (IR.declToString (.fdecl .anonymous params result body info))
    | .extern .. => none
  for (wrapped, raw) in [
      (``HAMTVerify.SetTests.wrappedInsert, ``HAMTVerify.SetTests.rawInsert),
      (``HAMTVerify.SetTests.wrappedContains, ``HAMTVerify.SetTests.rawContains)] do
    let some wrappedIR := (IR.findEnvDecl env wrapped).bind normalized
      | throwError "Missing function IR for {wrapped}"
    let some rawIR := (IR.findEnvDecl env raw).bind normalized
      | throwError "Missing function IR for {raw}"
    unless wrappedIR == rawIR do
      throwError "Set wrapper/raw compiler IR differs:\n{wrappedIR}\n{rawIR}"
