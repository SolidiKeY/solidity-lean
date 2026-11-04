import Solidity.Lowering.V08.LiteralFailureMemoryReason

/-! Direct Source revert with an effectful heap-backed reason. -/
namespace Solidity.Lowering.V08.LiteralFailureMemoryRevert
open Solidity Source Backend
open LiteralFailureMemoryReason

def revertAssigned {E : Env} {Γ : RCtx} : RExpr E (context Γ) (.tuple []) :=
 .builtin .revert (.cons assignMessage .nil) rfl

/-- The argument assignment precedes reading the actual string object.
No rollback, target lowering or runtime encoder is asserted. -/
theorem execution {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (b : Bool) (current next : Nat) (older : Locals E.layout Γ) (state : St E)
 (bs : Roadmap.Bytes)
 (heap : state.heap.get next = some ⟨.string .memory,.string bs⟩) :
 (evalE G F (n+8) revertAssigned).run (caller b current next older,state) =
 (.error (.revert (errorData bs)),(caller b next next older,state)) := by
  dsimp [revertAssigned,assignMessage,caller,evalE,evalBuiltin,evalArgs,evalLoc,writeLoc,
    getV,RVal.get,bytesOfRV,heapBytes,heapObj,EM.st,EM.locals,EM.lift,EM.setLocals]
  dsimp [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
    liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,
    modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,Except.pure,Locals.get,Locals.set]
  first | (rw [heap]; rfl) | rfl
end Solidity.Lowering.V08.LiteralFailureMemoryRevert
