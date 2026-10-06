import Lean
import VerifiedHAMT.Insert

/-! Actual compiled bodies, for inspecting proof erasure and remaining overhead.
Run: lake env lean Benchmarks/InspectInsertIR.lean
-/

open Lean in
run_meta do
  let env ← getEnv
  for name in [``Lean.PersistentHashMap.insertAux,
      ``Lean.PersistentHashMap.insertAtCollisionNodeAux,
      ``VerifiedHAMT.insert, ``VerifiedHAMT.insertNode, ``VerifiedHAMT.insertNoExpand,
      ``VerifiedHAMT.insertAt, ``VerifiedHAMT.insertEntries, ``VerifiedHAMT.rebuild,
      ``VerifiedHAMT.insertNodeCached, ``VerifiedHAMT.insertCollisionAux,
      ``VerifiedHAMT.insertEntriesCached, ``VerifiedHAMT.rebuildCached] do
    if (IR.findEnvDecl env name).isNone then
      throwError "No compiler IR found for {name}"
    for candidate in [name, name ++ `_redArg] do
      if let some decl := IR.findEnvDecl env candidate then
        logInfo m!"{format decl}"
