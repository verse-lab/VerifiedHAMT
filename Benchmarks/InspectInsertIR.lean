import Lean
import HAMTVerify.Insert

/-! Actual compiled bodies, for inspecting proof erasure and remaining overhead.
Run: lake env lean Benchmarks/InspectInsertIR.lean
-/

open Lean in
run_meta do
  let env ← getEnv
  for name in [``Lean.PersistentHashMap.insertAux,
      ``Lean.PersistentHashMap.insertAtCollisionNodeAux,
      ``HAMTVerify.insert, ``HAMTVerify.insertNode, ``HAMTVerify.insertNoExpand,
      ``HAMTVerify.insertAt, ``HAMTVerify.insertEntries, ``HAMTVerify.rebuild,
      ``HAMTVerify.insertNodeCached, ``HAMTVerify.insertCollisionAux,
      ``HAMTVerify.insertEntriesCached, ``HAMTVerify.rebuildCached] do
    if (IR.findEnvDecl env name).isNone then
      throwError "No compiler IR found for {name}"
    for candidate in [name, name ++ `_redArg] do
      if let some decl := IR.findEnvDecl env candidate then
        logInfo m!"{format decl}"
