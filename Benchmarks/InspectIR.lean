import Lean
import Lean.Data.PersistentHashMap
import HAMTVerify.Contains

/-! Dump the compiler IR actually stored for the imported implementations. -/

open Lean in
run_meta do
  let env ← getEnv
  for name in [``Lean.PersistentHashMap.contains,
      ``Lean.PersistentHashMap.containsAux, ``Lean.PersistentHashMap.containsAtAux,
      ``HAMTVerify.contains, ``HAMTVerify.containsNode, ``HAMTVerify.containsAt,
      ``HAMTVerify.slot, ``HAMTVerify.nextHash] do
    if (IR.findEnvDecl env name).isNone then
      throwError "No compiler IR found for {name}"
    for candidate in [name, name ++ `_redArg] do
      if let some decl := IR.findEnvDecl env candidate then
        logInfo m!"{format decl}"
