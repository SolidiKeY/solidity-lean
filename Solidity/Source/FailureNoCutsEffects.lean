import Solidity.Source.FailureNoCuts
import Solidity.Source.Horizon

/-! Actual event execution with clear active budgets. This does not erase
metadata, choose receipts, install balances or prove full evaluator NoFail. -/
namespace Solidity.Source.FailureExecution
open EM

/-- An enabled real event appends its complete event and advances every live
budget once. All other locals/state are exact, under the real cursor invariant. -/
theorem emitEvent_cutFree {E : Env} {Γ : RCtx} (event : Roadmap.Event)
    (points : Roadmap.Evm.FailurePoints) (locals : Locals E.layout Γ) (state : St E)
    (clear : state.resource.CutFree) :
    (Source.emitEvent event (some points) : EM E Γ Unit).run (locals,state) =
      (.ok (),(locals,{ state with events := state.events ++ [event], resource := state.resource.advanceEvent })) := by
  unfold Source.emitEvent
  rw [run_bind, check_cutFree _ _ _ clear]
  dsimp only []
  change (check (some points) : EM E Γ Unit).run
    (locals,{ state with events := state.events ++ [event], resource := state.resource.advanceEvent }) = _
  exact check_cutFree _ _ _ (Cursor.cutFree_advanceEvent _ clear)

end Solidity.Source.FailureExecution

/-- info: 'Solidity.Source.FailureExecution.emitEvent_cutFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.emitEvent_cutFree
