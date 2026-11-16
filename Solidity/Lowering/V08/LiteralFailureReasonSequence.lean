import Solidity.Lowering.V08.LiteralFailureStatementReason

/-! Actual Source statement sequencing of effectful memory reasons.
No transaction rollback, target encoder or world simulation is asserted. -/
namespace Solidity.Lowering.V08.LiteralFailureReasonSequence
open Solidity Source
open LiteralFailureMemoryReason LiteralFailureMemoryRevert LiteralFailureStatementReason

/-- Actual item recursion stops at a failed statement, independently of its tail. -/
theorem prefix_error {E : Env} {Γ Δ Ξ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (s : RStmt E [] false .body Γ Δ) (tail : RItems E [] false .body Δ Ξ)
 (locals : Locals E.layout Γ) (state final : St E) (h : Halt)
 (run : (execS G F n 0 none s locals).run (L0 E,state)=(.error h,(L0 E,final))) :
 (execItems G F (n+1) 0 none (.stmt s tail) locals).run (L0 E,state)=
 (.error h,(L0 E,final)) := by
 dsimp only [ExceptT.run] at run
 simp only [execItems,bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,run]
 rfl

/-- No admission or execution premise is imposed on the unreachable tail. -/
theorem failed_require {E : Env} {Γ Ξ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (tail : RItems E [] false .body (context Γ) Ξ)
 (current next : Nat) (older : Locals E.layout Γ) (state : St E)
 (bs : Roadmap.Bytes) (heap : state.heap.get next=some ⟨.string .memory,.string bs⟩) :
 (execItems G F (n+10) 0 none (.stmt (.expr requireAssigned) tail)
  (caller false current next older)).run (L0 E,state)=
 (.error (.revert (errorData bs)),(L0 E,state)) :=
 prefix_error G F (n+9) _ tail _ state state _
  (require_statement G F n current next older state bs heap)

def revertCurrent {E : Env} {Γ : RCtx} : RExpr E (context Γ) (.tuple []) :=
 .builtin .revert (.cons (.local (.there .here)) .nil) rfl

theorem current_statement {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (b : Bool) (current next : Nat) (older : Locals E.layout Γ) (state : St E)
 (bs : Roadmap.Bytes) (heap : state.heap.get current=some ⟨.string .memory,.string bs⟩) :
 (execS G F (n+9) 0 none (.expr revertCurrent : RStmt E [] false .body (context Γ) (context Γ))
 (caller b current next older)).run (L0 E,state)=(.error (.revert (errorData bs)),(L0 E,state)) := by
 apply expression_error G F (n+8) revertCurrent _ (caller b current next older) state state
 dsimp [revertCurrent,caller,evalE,withLibraryCalldata,evalBuiltin,evalArgs,evalLoc,getV,RVal.get,
   bytesOfRV,heapBytes,heapObj,EM.st,EM.locals,EM.lift]
 dsimp [bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
   liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,
   Except.pure,Locals.get]
 first | (rw [heap]; rfl) | rfl

def requireThenRevert {E : Env} {Γ : RCtx} :
 RItems E [] false .body (context Γ) (context Γ) :=
 .stmt (.expr requireAssigned) (.stmt (.expr revertCurrent) .nil)

/-- A successful require returns the changed locals to the next real statement. -/
theorem success_then_revert {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (current next : Nat) (older : Locals E.layout Γ) (state : St E)
 (bs : Roadmap.Bytes) (heap : state.heap.get next=some ⟨.string .memory,.string bs⟩) :
 (execItems G F (n+12) 0 none requireThenRevert
  (caller true current next older)).run (L0 E,state)=
 (.error (.revert (errorData bs)),(L0 E,state)) := by
 have first := require_success G F (n+2) current next older state
 have second := current_statement G F (n+1) true next next older state bs heap
 dsimp only [ExceptT.run] at first second
 simp only [requireThenRevert,execItems,bind,ExceptT.bind,ExceptT.bindCont,
   ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,first,second]
 rfl
end Solidity.Lowering.V08.LiteralFailureReasonSequence
