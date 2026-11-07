import Solidity.Lowering.V08.SourceFailures
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

#print axioms actual
#print axioms tail_timeout
#print axioms head_timeout
#print axioms reason_not_rollback
#print axioms timeout_not_rollback
end H62.AuditV08Adapters.SourceReasonJoint
