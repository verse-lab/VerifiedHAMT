import Lean
import HAMTVerifyTests.SetWithoutValArrayIR

/-! Save the generic runtime workers and the actual public Nat entry points,
including the specialized helpers reached through the public insertion call. -/

open Lean in
run_meta do
  let env ← getEnv
  for name in #[``HAMTVerify.SetWithoutValArrayTests.wrappedSize,
      ``HAMTVerify.SetWithoutValArrayTests.wrappedContains,
      ``HAMTVerify.SetWithoutValArrayTests.wrappedInsert,
      ``HAMTVerify.SetWithoutValArray.Raw.insertSizedNoExpand,
      ``HAMTVerify.SetWithoutValArray.Raw.insertSizedRaw] do
    let some decl := IR.findEnvDecl env name | throwError "Missing IR: {name}"
    logInfo m!"{format decl}"
    if let some worker := IR.findEnvDecl env (name ++ `_redArg) then
      logInfo m!"{format worker}"
  for name in HAMTVerify.SetWithoutValArrayIRTests.reachableRawDecls env
      ``HAMTVerify.SetWithoutValArrayTests.wrappedInsert do
    if name != ``HAMTVerify.SetWithoutValArrayTests.wrappedInsert then
      let some decl := IR.findEnvDecl env name | throwError "Missing IR: {name}"
      logInfo m!"{format decl}"
