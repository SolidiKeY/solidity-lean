import Solidity.Lowering.V08.SourceFailures
import Solidity.Lowering.V08.ProjectionControls
import Solidity.Lowering.V08.SourceKeccak
import Solidity.Lowering.V08.SourceCustomErrorControls

/-! Regression: a reason revert or timeout after hashing must preserve the
reached allocation rather than silently roll it back. These are ordinary EM
compositions of existing actual Source evaluators; no new failure emitter,
Source admission, catch selection, target body or session/frame certificate. -/
namespace H62.AuditV08Adapters.SourceReasonJoint
open Solidity Source
open Solidity.Lowering.V08

/-- Actual head and tail executions compose on the identical reached machine. -/
theorem actual {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (hashFuel reasonFuel : Nat) (hashInput bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (do let _ ← Source.evalE global frame (hashFuel+5) (SourceKeccak.literal hashInput)
        Source.evalE global frame (reasonFuel+5) (SourceFailures.reason bytes)).run (locals,state) =
      (.error (.revert (Semantics.encodeError bytes)),(locals,SourceKeccak.afterLiteral state hashInput)) := by
  have hash := SourceKeccak.eval_literal global frame hashFuel hashInput locals state
  have reason := SourceFailures.eval_reason_transport global frame reasonFuel bytes locals
    (SourceKeccak.afterLiteral state hashInput)
  simp only [ExceptT.run] at hash reason
  simp only [bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,hash,reason]

/-- The insufficient tail horizon also retains the already executed head's allocation. -/
theorem tail_timeout {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (hashFuel : Nat) (hashInput bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (do let _ ← Source.evalE global frame (hashFuel+5) (SourceKeccak.literal hashInput)
        Source.evalE global frame 2 (SourceFailures.reason bytes)).run (locals,state) =
      (.error .timeout,(locals,SourceKeccak.afterLiteral state hashInput)) := by
  have hash := SourceKeccak.eval_literal global frame hashFuel hashInput locals state
  have reason := SourceFailures.reason_low_horizon global frame bytes locals
    (SourceKeccak.afterLiteral state hashInput)
  simp only [ExceptT.run] at hash reason
  simp only [bind,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.bind,hash,reason]

/-- An unfinished head never executes the later reason expression. -/
theorem head_timeout {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (reasonFuel : Nat) (hashInput bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (do let _ ← Source.evalE global frame 0 (SourceKeccak.literal hashInput)
        Source.evalE global frame reasonFuel (SourceFailures.reason bytes)).run (locals,state) =
      (.error .timeout,(locals,state)) := rfl

open SourceCustomErrorControls

/-- The existing populated model refuses rollback even with the exact reason payload. -/
theorem reason_not_rollback (pipeline : Roadmap.Pipeline) (static : Bool)
    (hashFuel reasonFuel : Nat) (hashInput bytes : Roadmap.Bytes) :
    (do let _ ← Source.evalE (global pipeline) {frame with static:=static} (hashFuel+5)
          (SourceKeccak.literal hashInput)
        Source.evalE (global pipeline) {frame with static:=static} (reasonFuel+5)
          (SourceFailures.reason bytes)).run (locals,populated) ≠
      (.error (.revert (Semantics.encodeError bytes)),(locals,populated)) := by
  rw [actual]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

/-- Full timeout results distinguish whether the allocation already occurred. -/
theorem timeout_not_rollback (pipeline : Roadmap.Pipeline) (static : Bool)
    (hashFuel : Nat) (hashInput bytes : Roadmap.Bytes) :
    (do let _ ← Source.evalE (global pipeline) {frame with static:=static} (hashFuel+5)
          (SourceKeccak.literal hashInput)
        Source.evalE (global pipeline) {frame with static:=static} 2
          (SourceFailures.reason bytes)).run (locals,populated) ≠
      (.error .timeout,(locals,populated)) := by
  rw [tail_timeout]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

/-- The expression's original low horizon becomes a full statement timeout. -/
theorem statement_low_horizon {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.execS global frame 3 0 none
      (.expr (SourceFailures.reason bytes) : RStmt E [] false .body Γ Γ) locals).run
      (Source.L0 E,state) = (.error .timeout,(Source.L0 E,state)) := by
  have expression := SourceFailures.reason_low_horizon global frame bytes locals state
  simp only [ExceptT.run] at expression
  simp only [Source.execS,Source.EM.sub,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
    ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,expression]

/-- Actual statement execution in the inner local scope retains the hash state. -/
theorem statement_actual {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (hashFuel reasonFuel : Nat) (hashInput bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (do let _ ← Source.evalE global frame (hashFuel+5) (SourceKeccak.literal hashInput)
        Source.EM.sub (Source.L0 E) (Source.execS global frame (reasonFuel+6) 0 none
          (.expr (SourceFailures.reason bytes) : RStmt E [] false .body Γ Γ) locals)).run
          (locals,state) =
      (.error (.revert (Source.errorData bytes)),(locals,SourceKeccak.afterLiteral state hashInput)) := by
  have hash := SourceKeccak.eval_literal global frame hashFuel hashInput locals state
  have body := SourceFailures.exec_reason global frame reasonFuel bytes locals
    (SourceKeccak.afterLiteral state hashInput)
  simp only [ExceptT.run] at hash body
  simp only [Source.EM.sub,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,hash,body]

theorem statement_tail_timeout {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (hashFuel : Nat) (hashInput bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (do let _ ← Source.evalE global frame (hashFuel+5) (SourceKeccak.literal hashInput)
        Source.EM.sub (Source.L0 E) (Source.execS global frame 3 0 none
          (.expr (SourceFailures.reason bytes) : RStmt E [] false .body Γ Γ) locals)).run
          (locals,state) =
      (.error .timeout,(locals,SourceKeccak.afterLiteral state hashInput)) := by
  have hash := SourceKeccak.eval_literal global frame hashFuel hashInput locals state
  have body := statement_low_horizon global frame bytes locals (SourceKeccak.afterLiteral state hashInput)
  simp only [ExceptT.run] at hash body
  simp only [Source.EM.sub,bind,pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,
    StateT.bind,hash,body]

/-- Restoring the outer typed locals does not roll back the reached machine. -/
theorem statement_not_rollback (pipeline : Roadmap.Pipeline) (static : Bool)
    (hashFuel reasonFuel : Nat) (hashInput bytes : Roadmap.Bytes) :
    (do let _ ← Source.evalE (global pipeline) {frame with static:=static} (hashFuel+5)
          (SourceKeccak.literal hashInput)
        Source.EM.sub (Source.L0 E) (Source.execS (global pipeline) {frame with static:=static}
          (reasonFuel+6) 0 none
          (.expr (SourceFailures.reason bytes) : RStmt E [] false .body [.bool] [.bool]) locals)).run
          (locals,populated) ≠
      (.error (.revert (Source.errorData bytes)),(locals,populated)) := by
  rw [statement_actual]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

#print axioms statement_low_horizon
#print axioms statement_actual
#print axioms statement_tail_timeout
#print axioms statement_not_rollback

/-- Existing projected target data supplies the original explicit-state parameter.
This is an independent constructor execution, not a compiler-selected body. -/
theorem target_explicit (bytes : Roadmap.Bytes) :
    (SourceFailures.reasonStatement bytes : Stmt Controls.Cell [] []).runC
      ProjectionControls.projected = .error (.revertWith (Semantics.encodeError bytes)) :=
  SourceFailures.target_reason bytes ProjectionControls.projected

/-- Same payload in two actual runs, without asserting their states are related. -/
theorem independent_runs (pipeline : Roadmap.Pipeline) (static : Bool)
    (fuel : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} (fuel+5)
      (SourceFailures.reason bytes)).run (locals,populated) =
      (.error (.revert (Semantics.encodeError bytes)),(locals,populated)) ∧
    (SourceFailures.reasonStatement bytes : Stmt Controls.Cell [] []).runC
      ProjectionControls.projected = .error (.revertWith (Semantics.encodeError bytes)) :=
  SourceFailures.reason_execution_transport (global pipeline) {frame with static:=static}
    fuel bytes locals populated ProjectionControls.projected

/-- Empty reason text is still encoded reason data, not the bare intrinsic revert. -/
theorem empty_reason_not_plain :
    (SourceFailures.reasonStatement [] : Stmt Controls.Cell [] []).runC
      ProjectionControls.projected ≠ .error .revert := by
  rw [target_explicit]
  intro same
  have status := Except.error.inj same
  cases status

#print axioms target_explicit
#print axioms independent_runs
#print axioms empty_reason_not_plain

#print axioms actual
#print axioms tail_timeout
#print axioms head_timeout
#print axioms reason_not_rollback
#print axioms timeout_not_rollback
end H62.AuditV08Adapters.SourceReasonJoint
