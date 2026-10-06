import Lean
import VerifiedHAMT.Map

/-! Actual compiler IR for the total and opaque native value-lookup workers. -/

open Lean in
run_meta do
  let env ← getEnv
  for name in [``Lean.PersistentHashMap.find?, ``Lean.PersistentHashMap.findAux,
      ``Lean.PersistentHashMap.findAtAux, ``VerifiedHAMT.find?,
      ``VerifiedHAMT.findNode, ``VerifiedHAMT.findCollisionAux,
      ``VerifiedHAMT.findD, ``VerifiedHAMT.Map.find?, ``VerifiedHAMT.Map.findD] do
    if (IR.findEnvDecl env name).isNone then
      throwError "No compiler IR found for {name}"
    for candidate in [name, name ++ `_redArg] do
      if let some decl := IR.findEnvDecl env candidate then
        logInfo m!"{format decl}"
