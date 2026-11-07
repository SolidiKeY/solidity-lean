import Solidity.Source.FailureMachine

/-! Full-state law for the actual Source event emitter. Connecting the stored
cursor to the explicit plan remains a producer obligation; this theorem
describes actual behavior for every typed cursor and does not install recursive
Eval/Session hooks. A reached stop emits no event and retains every other
caller/state field. No rollback, catch selection or P8 realization is claimed. -/
namespace Solidity.Source.FailureExecution
open EM
theorem emit_stopped_run {E : Env} {Γ : RCtx} (plan : Roadmap.Evm.FailurePoints)
    (event : Roadmap.Event) (l : Locals E.layout Γ) (s : St E)
    (stop : Stop s.resource.nextRequest s.resource.nextFrame)
    (h : s.resource.stop? = some stop) :
    (Source.emitEvent event (some plan)).run (l,s) =
      (.error (.revert []),(l,{ s with resource := { s.resource with pending := some stop } })) := by
  have hc : (check (some plan) : EM E Γ Unit).run (l,s) =
      (.error (.revert []),(l,{ s with resource := { s.resource with pending := some stop } })) := by
    have hs : (st : EM E Γ (St E)).run (l,s) = (.ok s,(l,s)) := by rfl
    unfold check
    rw [ExceptT.run_bind]
    show StateT.bind (ExceptT.run (st : EM E Γ (St E))) _ (l,s) = _
    simp only [StateT.bind]
    rw [hs]
    dsimp only [bind, pure]
    rw [h]
    rfl
  simp only [Source.emitEvent]
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run (check (some plan))) _ (l,s) = _
  simp only [StateT.bind]
  rw [hc]
  rfl
/- BEGIN GENERATED EVENT PINS -/
/-- info: 'Solidity.Source.emitEvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.emitEvent
/-- info: 'Solidity.Source.FailureExecution.emit_stopped_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.emit_stopped_run
/- END GENERATED EVENT PINS -/

end Solidity.Source.FailureExecution
