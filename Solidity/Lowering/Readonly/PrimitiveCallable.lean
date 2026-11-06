import Solidity.Lowering.Readonly.PrimitiveInitialization
import Solidity.Lowering.V08.SourceCallable

/-! Actual source-call composition with primitive return-slot initialization
DISCHARGED. Published V08 body/result transport is reused unchanged. The actual
selected body execution, frame fit and return extraction remain typed premises;
this does not certify target body compilation, world linkage or ABI outcomes. -/
namespace Solidity.Lowering.Readonly.PrimitiveCallable
open Solidity.Source PrimitiveValues PrimitiveInitialization
variable {E : Env} {ps : List STy}

theorem complete (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (arguments : Vals E.layout ps) (rs : List PrimTy) (body : RBody E)
    (selected : global.prog.body (global.dispatchFn frame.contract d) = some body)
    (fits : (rs.map sourceTy).reverseAux (ps.reverseAux []) = body.locals)
    (returned : Locals E.layout body.locals) (outputs : RVals E.layout (rs.map sourceTy))
    (entry final : St E)
    (execution : (runMods global {frame with checked := true} (n + 1) body body.mods
      (fits ▸ (defaults E.layout rs).onto (arguments.onto (L0 E)))).run (L0 E, entry) =
        (.ok returned, (L0 E, final)))
    (extraction : retVals returned 0 (rs.map sourceTy) = .ok outputs) :
    (callInternal global frame (n + 2) d arguments (rs.map sourceTy)).run (L0 E, entry) =
      (.ok (mkRet (rs.map sourceTy) outputs), (L0 E, final)) := by
  apply Solidity.Lowering.V08.SourceCallable.complete global frame (n + 1) d arguments body
    selected (defaults E.layout rs) fits returned outputs entry entry final _ execution extraction
  rw [zero_values]
  rfl

theorem body_failure (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (arguments : Vals E.layout ps) (rs : List PrimTy) (body : RBody E)
    (selected : global.prog.body (global.dispatchFn frame.contract d) = some body)
    (fits : (rs.map sourceTy).reverseAux (ps.reverseAux []) = body.locals)
    (entry final : St E) (halt : Halt)
    (execution : (runMods global {frame with checked := true} (n + 1) body body.mods
      (fits ▸ (defaults E.layout rs).onto (arguments.onto (L0 E)))).run (L0 E, entry) =
        (.error halt, (L0 E, final))) :
    (callInternal global frame (n + 2) d arguments (rs.map sourceTy)).run (L0 E, entry) =
      (.error halt, (L0 E, final)) := by
  apply Solidity.Lowering.V08.SourceCallable.body_failure global frame (n + 1) d arguments body
    selected (defaults E.layout rs) fits entry entry final halt _ execution
  rw [zero_values]
  rfl

theorem wrong_frame (global : Glob E) (frame : Fr) (n : Nat) (d : Decl)
    (arguments : Vals E.layout ps) (rs : List PrimTy) (body : RBody E)
    (selected : global.prog.body (global.dispatchFn frame.contract d) = some body)
    (wrong : (rs.map sourceTy).reverseAux (ps.reverseAux []) ≠ body.locals) (entry : St E) :
    (callInternal global frame (n + 2) d arguments (rs.map sourceTy)).run (L0 E, entry) =
      (.error (.stuck "call frame"), (L0 E, entry)) := by
  apply Solidity.Lowering.V08.SourceCallable.wrong_frame global frame (n + 1) d arguments body
    selected (defaults E.layout rs) wrong entry entry
  rw [zero_values]
  rfl

end Solidity.Lowering.Readonly.PrimitiveCallable
