import Solidity.Lowering.V08.LiteralFailureMemoryRevert

/-! Actual Source statement boundary for effectful memory-backed reasons.
A failed subcomputation discards its local frame, but carries its exact state.
This is not transaction/world rollback or target lowering. -/
namespace Solidity.Lowering.V08.LiteralFailureStatementReason
open Solidity Source
open LiteralFailureMemoryReason LiteralFailureMemoryRevert

theorem expression_error {E : Env} {Γ : RCtx} {τ : STy}
 (G : Glob E) (F : Fr) (n : Nat) (e : RExpr E Γ τ)
 (locals changed : Locals E.layout Γ) (state final : St E) (h : Halt)
 (run : (evalE G F n e).run (locals,state)=(.error h,(changed,final))) :
 (execS G F (n+1) 0 none (.expr e : RStmt E [] false .body Γ Γ) locals).run
  (L0 E,state)=(.error h,(L0 E,final)) := by
 dsimp only [ExceptT.run] at run
 simp only [execS,EM.sub,bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,run]
 rfl

theorem revert_statement {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (b : Bool) (current next : Nat) (older : Locals E.layout Γ) (state : St E)
 (bs : Roadmap.Bytes) (heap : state.heap.get next=some ⟨.string .memory,.string bs⟩) :
 (execS G F (n+9) 0 none (.expr revertAssigned :
  RStmt E [] false .body (context Γ) (context Γ)) (caller b current next older)).run
 (L0 E,state)=(.error (.revert (errorData bs)),(L0 E,state)) :=
 expression_error G F (n+8) revertAssigned _ _ state state _
  (execution G F n b current next older state bs heap)

theorem require_statement {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (current next : Nat) (older : Locals E.layout Γ) (state : St E)
 (bs : Roadmap.Bytes) (heap : state.heap.get next=some ⟨.string .memory,.string bs⟩) :
 (execS G F (n+9) 0 none (.expr requireAssigned :
  RStmt E [] false .body (context Γ) (context Γ)) (caller false current next older)).run
 (L0 E,state)=(.error (.revert (errorData bs)),(L0 E,state)) :=
 expression_error G F (n+8) requireAssigned _ _ state state _
  (require_false G F n current next older state bs heap)
theorem require_success {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (current next : Nat) (older : Locals E.layout Γ) (state : St E) :
 (execS G F (n+9) 0 none (.expr requireAssigned :
  RStmt E [] false .body (context Γ) (context Γ)) (caller true current next older)).run
 (L0 E,state)=(.ok (.normal (caller true next next older)),(L0 E,state)) := by
 have run := require_true G F n current next older state
 dsimp only [ExceptT.run] at run
 simp only [execS,EM.sub,bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
   StateT.bind,StateT.pure,run]
 rfl
end Solidity.Lowering.V08.LiteralFailureStatementReason
