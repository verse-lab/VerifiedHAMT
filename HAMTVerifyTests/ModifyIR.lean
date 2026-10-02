import Lean
import HAMTVerify.Insert

/-! Check that inlining the checked modifier still selects its unsafe
implementation, including the slot release before the callback. The callback
is a runtime parameter so its invocation cannot be folded away. -/

namespace HAMTVerify.ModifyIRTests

def viaWrapper (xs : Array Nat) (i : Nat) (f : Nat → Nat) : Array Nat :=
  HAMTVerify.Array.modifyWithCallBackProof xs i (fun x _ => f x)

unsafe def viaUnsafe (xs : Array Nat) (i : Nat) (f : Nat → Nat) : Array Nat :=
  if hi : i < xs.size then
    HAMTVerify.Array.modifyInBoundWithCallBackProofUnsafe xs i (fun x _ => f x) hi
  else xs

open Lean in
run_meta do
  let env ← getEnv
  let normalized := fun (decl : IR.Decl) =>
    match decl with
    | .fdecl _ params result body info =>
      some (IR.declToString (.fdecl .anonymous params result body info))
    | .extern .. => none
  let some wrapperIR := (IR.findEnvDecl env ``viaWrapper).bind normalized
    | throwError "Missing IR for the checked modifier"
  let some unsafeIR := (IR.findEnvDecl env ``viaUnsafe).bind normalized
    | throwError "Missing IR for the unsafe modifier"
  unless wrapperIR == unsafeIR do
    throwError "Checked/unsafe modifier IR differs:\n{wrapperIR}\n{unsafeIR}"

end HAMTVerify.ModifyIRTests
