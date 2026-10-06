import Lean
import VerifiedHAMT

/-! Imported compiler IR for the actual set interfaces and their map cores. -/

open Lean in
run_meta do
  let env ← getEnv
  for name in [``Lean.PersistentHashSet.insert, ``Lean.PersistentHashSet.contains,
      ``VerifiedHAMT.Set.insert, ``VerifiedHAMT.Set.contains, ``VerifiedHAMT.Set.toRaw,
      ``VerifiedHAMT.Map.insert, ``VerifiedHAMT.Map.contains,
      ``Lean.PersistentHashMap.containsAux, ``VerifiedHAMT.containsNode,
      ``Lean.PersistentHashMap.insertAux, ``VerifiedHAMT.insertNodeCached,
      ``VerifiedHAMT.containsThenInsertImpl, ``VerifiedHAMT.insertSizedRaw,
      ``VerifiedHAMT.insertSizedNoExpand] do
    if (IR.findEnvDecl env name).isNone then
      throwError "No compiler IR found for {name}"
    for candidate in [name, name ++ `_redArg] do
      if let some decl := IR.findEnvDecl env candidate then
        logInfo m!"{format decl}"
