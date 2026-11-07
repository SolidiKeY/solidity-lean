import Solidity.Lowering.V08.SourceRethrow
import Solidity.Lowering.V08.SourceCustomErrorControls

/-! Regression: rethrow evaluation and heap premises must share the same reached
allocation. A statement timeout retains that allocation, while an allocation
timeout retains the prestate. These are independent Source boundaries, not
admission, rollback, a selected target body or full-session correspondence. -/
namespace H62.AuditV08Adapters.SourceRethrowJoint
open Solidity Source
open Solidity.Lowering.V08

/-- Both original expression-rethrow premises use the returned pointer and heap. -/
theorem joint {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (fuel : Nat) (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ)
    (state : Source.St E) :
    (Source.evalE global frame (fuel+4) (SourceAbi.literal true bytes)).run (locals,state) =
      (.ok (.val (.memRef rfl state.heap.next)),
        (locals,SourceKeccak.afterLiteral state bytes)) ∧
    (SourceKeccak.afterLiteral state bytes).heap.get state.heap.next =
      some ⟨.bytes .memory,.bytes bytes⟩ :=
  ⟨SourceAbi.literal_execution global frame fuel true bytes locals state,
    SourceRethrow.allocated_object state bytes⟩

theorem actual {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (fuel statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (SourceRethrow.fromExpression global frame (fuel+4) (statementFuel+1)
      (SourceAbi.literal true bytes)).run (locals,state) =
      (.error (.revert bytes),(locals,SourceKeccak.afterLiteral state bytes)) := by
  have h := joint global frame fuel bytes locals state
  exact SourceRethrow.expression_rethrow global frame (fuel+4) statementFuel
    (SourceAbi.literal true bytes) locals locals state _ state.heap.next bytes h.1 h.2

/-- An existing populated model inhabits the two premises simultaneously. -/
theorem fixture_joint (pipeline : Roadmap.Pipeline) (static : Bool) (fuel : Nat) :
    ∃ (address : Nat) (final : Source.St SourceCustomErrorControls.E),
      (Source.evalE (SourceCustomErrorControls.global pipeline)
        {SourceCustomErrorControls.frame with static:=static} (fuel+4)
        (SourceAbi.literal true SourceCustomErrorControls.binary)).run
        (SourceCustomErrorControls.locals,SourceCustomErrorControls.populated) =
          (.ok (.val (.memRef rfl address)),(SourceCustomErrorControls.locals,final)) ∧
      final.heap.get address = some ⟨.bytes .memory,.bytes SourceCustomErrorControls.binary⟩ :=
  ⟨SourceCustomErrorControls.populated.heap.next,
    SourceKeccak.afterLiteral SourceCustomErrorControls.populated SourceCustomErrorControls.binary,
    joint (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} fuel SourceCustomErrorControls.binary
      SourceCustomErrorControls.locals SourceCustomErrorControls.populated⟩

/-- Zero expression fuel supplies the original failure premise, for any later horizon. -/
theorem expression_timeout {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (statementFuel : Nat) (bytes : Roadmap.Bytes)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (SourceRethrow.fromExpression global frame 0 statementFuel
      (SourceAbi.literal true bytes)).run (locals,state) =
      (.error .timeout,(locals,state)) :=
  SourceRethrow.expression_failure global frame 0 statementFuel
    (SourceAbi.literal true bytes) locals locals state state .timeout rfl

/-- The existing populated fixture makes the two timeout states observably different. -/
theorem timeout_states_differ (pipeline : Roadmap.Pipeline) (static : Bool)
    (fuel : Nat) (bytes : Roadmap.Bytes) :
    (SourceRethrow.allocated (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} (fuel+4) 0 bytes).run
        (SourceCustomErrorControls.locals,SourceCustomErrorControls.populated) ≠
    (SourceRethrow.allocated (SourceCustomErrorControls.global pipeline)
      {SourceCustomErrorControls.frame with static:=static} 0 0 bytes).run
        (SourceCustomErrorControls.locals,SourceCustomErrorControls.populated) := by
  rw [SourceRethrow.statement_timeout,SourceRethrow.allocation_timeout]
  intro same
  have heapSame := congrArg (fun result => result.2.2.heap.next) same
  change 2 = 1 at heapSame
  cases heapSame

#print axioms joint
#print axioms fixture_joint
#print axioms actual
#print axioms expression_timeout
#print axioms timeout_states_differ
end H62.AuditV08Adapters.SourceRethrowJoint
