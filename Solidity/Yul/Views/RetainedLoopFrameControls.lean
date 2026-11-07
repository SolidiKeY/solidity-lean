import Solidity.Yul.Views.RetainedLoopFrame
import Solidity.Yul.Views.RetainedLoopRefreshControls

/-! Actual checked loop-derived writes preserve another account, a dormant
unselected sibling, transient storage, and complete non-ex administration.
The selected header is exhibited separately, so exclusion is not vacuous. -/
namespace Solidity.Yul.Views.Controls

theorem rflf_unselected (G : Source.Glob agEnv) (flag : Bool) :
    ∀ c∈(rfliImage G flag).snapshot rhNextRaw, agInner 1≠c.path := by
  intro c member
  rw [rflw_next_snapshot] at member
  change c∈[_,_,_,_,_,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rflf_other_account (G : Source.Glob agEnv) (flag : Bool) :
    (rflswRun G flag).2.2.ex.world.accounts 2=(rflswState G flag).2.ex.world.accounts 2 :=
  RetainedLoopFrame.other_account packedStepFrame (rfliImage G flag) rhNextRaw (rflswState G flag)
    rhOp (rflw_prepared G flag) 2 (by decide)

theorem rflf_other_path (G : Source.Glob agEnv) (flag : Bool) :
    ((rflswRun G flag).2.2.ex.world.accounts account).storage.cell (agInner 1)=
      ((rflswState G flag).2.ex.world.accounts account).storage.cell (agInner 1) :=
  RetainedLoopFrame.other_path packedStepFrame (rfliImage G flag) rhNextRaw (rflswState G flag)
    rhOp (rflw_prepared G flag) (agInner 1) (rflf_unselected G flag)

theorem rflf_transient (G : Source.Glob agEnv) (flag : Bool) :
    (rflswRun G flag).2.2.ex.transient=(rflswState G flag).2.ex.transient :=
  RetainedLoopFrame.transient packedStepFrame (rfliImage G flag) rhNextRaw (rflswState G flag)
    rhOp (rflw_prepared G flag)

theorem rflf_administration (G : Source.Glob agEnv) (flag : Bool) :
    let reached := rflswRun G flag
    let state := rflswState G flag
    (reached.2.1,reached.2.2.heap,reached.2.2.events,reached.2.2.logs,reached.2.2.fnLocals)=
      (state.1,state.2.heap,state.2.events,state.2.logs,state.2.fnLocals) :=
  RetainedLoopFrame.administration packedStepFrame rhOp (rflswState G flag)

theorem rflf_selected_header (G : Source.Glob agEnv) (flag : Bool) :
    ∃ c∈(rfliImage G flag).snapshot rhNextRaw, c.path=agInner 0 ∧ c.slot=101 := by
  rw [rflw_next_snapshot]
  change ∃ c∈[_,_,_,_,_,_], _
  refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
  decide

end Solidity.Yul.Views.Controls
