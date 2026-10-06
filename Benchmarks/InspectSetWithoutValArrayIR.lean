import Lean
import VerifiedHAMTTests.SetWithoutValArrayIR

/-! Save the generic runtime workers and the actual public Nat entry points,
including the specialized helpers reached through the public insertion call. -/

open Lean in
run_meta do
  let env ← getEnv
  for name in #[``VerifiedHAMT.SetWithoutValArrayTests.wrappedSize,
      ``VerifiedHAMT.SetWithoutValArrayTests.wrappedContains,
      ``VerifiedHAMT.SetWithoutValArrayTests.wrappedInsert,
      ``VerifiedHAMT.SetWithoutValArray.Raw.insertSizedNoExpand,
      ``VerifiedHAMT.SetWithoutValArray.Raw.insertSizedRaw] do
    let some decl := IR.findEnvDecl env name | throwError "Missing IR: {name}"
    logInfo m!"{format decl}"
    if let some worker := IR.findEnvDecl env (name ++ `_redArg) then
      logInfo m!"{format worker}"
  for name in VerifiedHAMT.SetWithoutValArrayIRTests.reachableRawDecls env
      ``VerifiedHAMT.SetWithoutValArrayTests.wrappedInsert do
    if name != ``VerifiedHAMT.SetWithoutValArrayTests.wrappedInsert then
      let some decl := IR.findEnvDecl env name | throwError "Missing IR: {name}"
      logInfo m!"{format decl}"
