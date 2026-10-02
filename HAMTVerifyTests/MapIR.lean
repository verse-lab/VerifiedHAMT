import Lean
import HAMTVerifyTests.Map

/-!
Compiler regression check, not a logical theorem: after proof erasure and
inlining, the bundled Nat entry points must have the same IR signature and body,
including ownership annotations, as hand-written ones on the map's runtime data
(`SizedRaw`: the native map and its size). Ignore only the declaration names.
The raw insertion calls `insertSizedImpl` directly, so this also checks that the
proved compiler rewrite removes the separate lookup and wrapper conversions.
-/

open Lean in
run_meta do
  let env ← getEnv
  let normalized := fun (decl : IR.Decl) =>
    match decl with
    | .fdecl _ params result body info =>
      some (IR.declToString (.fdecl .anonymous params result body info))
    | .extern .. => none
  for (wrapped, raw) in [
      (``HAMTVerify.MapTests.wrappedInsert, ``HAMTVerify.MapTests.rawInsert),
      (``HAMTVerify.MapTests.wrappedContains, ``HAMTVerify.MapTests.rawContains)] do
    let some wrappedIR := (IR.findEnvDecl env wrapped).bind normalized
      | throwError "Missing function IR for {wrapped}"
    let some rawIR := (IR.findEnvDecl env raw).bind normalized
      | throwError "Missing function IR for {raw}"
    unless wrappedIR == rawIR do
      throwError "Bundled/raw compiler IR differs:\n{wrappedIR}\n{rawIR}"
