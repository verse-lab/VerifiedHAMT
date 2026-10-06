import Lean
import VerifiedHAMTTests.Set

/-! Check erasure of the Set and Map wrappers and invariant proofs: the bundled
entry points must compile like hand-written ones on the set's runtime data
(`SizedRaw`: the native map and its size), ignoring only declaration names.
The raw insertion calls the sized implementation directly, also
checking that sets benefit from the proved compiler rewrite. This is a compiler
regression check, not a theorem about the native partial set implementation. -/

open Lean in
run_meta do
  let env ← getEnv
  let normalized := fun (decl : IR.Decl) =>
    match decl with
    | .fdecl _ params result body info =>
      some (IR.declToString (.fdecl .anonymous params result body info))
    | .extern .. => none
  for (wrapped, raw) in [
      (``VerifiedHAMT.SetTests.wrappedInsert, ``VerifiedHAMT.SetTests.rawInsert),
      (``VerifiedHAMT.SetTests.wrappedContains, ``VerifiedHAMT.SetTests.rawContains)] do
    let some wrappedIR := (IR.findEnvDecl env wrapped).bind normalized
      | throwError "Missing function IR for {wrapped}"
    let some rawIR := (IR.findEnvDecl env raw).bind normalized
      | throwError "Missing function IR for {raw}"
    unless wrappedIR == rawIR do
      throwError "Set wrapper/raw compiler IR differs:\n{wrappedIR}\n{rawIR}"
