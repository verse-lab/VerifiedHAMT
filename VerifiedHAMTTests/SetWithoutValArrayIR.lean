import Lean
import VerifiedHAMTTests.SetWithoutValArray

/-! Proof erasure and compiler-rewrite regression checks for the bundled set.
In particular, reading size must compile like a plain field projection. -/

open Lean in
run_meta do
  let env ← getEnv
  let normalized := fun (decl : IR.Decl) =>
    match decl with
    | .fdecl _ params result body info =>
      some (IR.declToString (.fdecl .anonymous params result body info))
    | .extern .. => none
  for (wrapped, raw) in [
      (``VerifiedHAMT.SetWithoutValArrayTests.wrappedInsert, ``VerifiedHAMT.SetWithoutValArrayTests.rawInsert),
      (``VerifiedHAMT.SetWithoutValArrayTests.wrappedContains, ``VerifiedHAMT.SetWithoutValArrayTests.rawContains),
      (``VerifiedHAMT.SetWithoutValArrayTests.wrappedSize, ``VerifiedHAMT.SetWithoutValArrayTests.rawSize)] do
    let some wrappedIR := (IR.findEnvDecl env wrapped).bind normalized
      | throwError "Missing function IR for {wrapped}"
    let some rawIR := (IR.findEnvDecl env raw).bind normalized
      | throwError "Missing function IR for {raw}"
    unless wrappedIR == rawIR do
      throwError "Keys-only set wrapper/raw compiler IR differs:\n{wrappedIR}\n{rawIR}"

namespace VerifiedHAMT.SetWithoutValArrayIRTests

open Lean IR

private partial def expressions : FnBody → List IR.Expr
  | .vdecl _ _ e body => e :: expressions body
  | .jdecl _ _ value body => expressions value ++ expressions body
  | .case _ _ _ alts => alts.toList.flatMap (fun alt => expressions alt.body)
  | .ret _ | .unreachable | .jmp _ _ => []
  | body => expressions body.body

/-- Follow the actual public call, including specializations reused from imports. -/
partial def reachableRawDecls (env : Environment) (root : Name) : Array Name :=
  go [root] #[]
where
  go (pending : List Name) (seen : Array Name) : Array Name :=
    match pending with
    | [] => seen
    | name :: pending =>
      if seen.contains name then go pending seen else
      let callees := match findEnvDecl env name with
        | some (.fdecl _ _ _ body _) => (expressions body).filterMap fun
          | .fap callee _ =>
            if (`VerifiedHAMT.SetWithoutValArray.Raw).isPrefixOf callee then some callee else none
          | _ => none
        | _ => []
      go (callees ++ pending) (seen.push name)

run_meta do
  let env ← getEnv
  let traversals := #[``SetWithoutValArray.Raw.insertSizedRaw,
    ``SetWithoutValArray.Raw.insertSizedNoExpand]
  let reachable := reachableRawDecls env ``SetWithoutValArrayTests.wrappedInsert
  let specialized := reachable.filter fun name =>
    traversals.any (fun traversal => traversal.isPrefixOf name &&
        name != traversal && name != traversal ++ `_redArg) &&
        (match name with
        | .str _ "_redArg" => true
        | .str _ s => s.startsWith "spec_"
        | _ => false)
  for traversal in traversals do
    unless specialized.any (traversal.isPrefixOf ·) do
      throwError "No specialized sized worker for {traversal}"
  for name in traversals.map (· ++ `_redArg) ++ specialized do
    let some (.fdecl _ _ _ body _) := findEnvDecl env name
      | throwError "Missing worker IR for {name}"
    let es := expressions body
    -- Final IR has already lowered reuse to sharing tests and field writes.
    -- inspect_without_vals.py checks those paths in emitted C.
    for e in es do
      match e with
      | .ctor info _ | .reuse _ info _ _ =>
        if info.name == ``Prod.mk then
          throwError "{name}: unexpected product allocation"
      | .fap callee _ =>
        if #[``SetWithoutValArray.Raw.contains, ``SetWithoutValArray.Raw.containsNode,
            ``SetWithoutValArray.Raw.keyList, ``SetWithoutValArray.Raw.keyCount].any
            (·.isPrefixOf callee) then
          throwError "{name}: separate lookup or count traversal: {callee}"
      | .ap .. | .pap .. =>
        if specialized.contains name then
          throwError "{name}: closure or indirect call remains in Nat worker"
      | _ => pure ()

end VerifiedHAMT.SetWithoutValArrayIRTests
