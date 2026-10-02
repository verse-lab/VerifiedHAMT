import Lean
import HAMTVerify

/-! Imported compiler IR for the actual set interfaces and their map cores. -/

open Lean in
run_meta do
  let env ← getEnv
  for name in [``Lean.PersistentHashSet.insert, ``Lean.PersistentHashSet.contains,
      ``HAMTVerify.Set.insert, ``HAMTVerify.Set.contains, ``HAMTVerify.Set.toRaw,
      ``HAMTVerify.Map.insert, ``HAMTVerify.Map.contains,
      ``Lean.PersistentHashMap.containsAux, ``HAMTVerify.containsNode,
      ``Lean.PersistentHashMap.insertAux, ``HAMTVerify.insertNodeCached,
      ``HAMTVerify.containsThenInsertImpl, ``HAMTVerify.insertSizedRaw,
      ``HAMTVerify.insertSizedNoExpand] do
    if (IR.findEnvDecl env name).isNone then
      throwError "No compiler IR found for {name}"
    for candidate in [name, name ++ `_redArg] do
      if let some decl := IR.findEnvDecl env candidate then
        logInfo m!"{format decl}"
