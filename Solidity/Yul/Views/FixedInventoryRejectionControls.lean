import Solidity.Yul.Views.FixedInventoryRejection
import Solidity.Yul.Views.FixedInventoryHistoryControls

/-! A real changed fixed snapshot is followed by noncanonical preparation.
The successful mutation and both aliases survive, the exact rejected suffix is
retained, and later snapshots are not run. No Source halt is manufactured. -/
namespace Solidity.Yul.Views.FixedInventory.RejectionControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedInventory.RealizationControls
open Solidity.Yul.Views.FixedInventory.CursorControls
open Solidity.Yul.Views.FixedInventory.HistoryControls

theorem dirty_snapshot : snapshot FixedMemory.Controls.placement FixedMemory.Controls.f (some 2)
    dirty (FixedMemory.Controls.placement.address 0)=none := by
  first | solve | simp only [snapshot]
        | solve | decide
        | solve | rfl

theorem changed_then_rejected : ∃ next,
    snapshotStep FixedMemory.Controls.placement FixedMemory.Controls.state initial FixedMemory.Controls.changedRaw=some next ∧
    next.1=expectedState ∧
    snapshotStep FixedMemory.Controls.placement next.1 next.2 dirty=none ∧
    runSnapshots FixedMemory.Controls.placement next.1 next.2 [dirty,FixedMemory.Controls.raw]=
      ⟨next,[dirty,FixedMemory.Controls.raw]⟩ := by
  first | solve | simp only
        | obtain ⟨next,step,same,covered,addresses,_,_⟩ := actual_step
          have preserved := snapshotStep_preserves FixedMemory.Controls.placement FixedMemory.Controls.state initial
            FixedMemory.Controls.changedRaw next step
          have typed : next.1.2.heap.ty 0=some FixedMemory.Controls.ty := by
            rw [preserved.2.1]
            rfl
          have bad : snapshot next.2.placement FixedMemory.Controls.f (some 2) dirty
              (next.2.placement.address 0)=none := by
            rw [addresses]
            rw [snapshot_transport FixedMemory.Controls.placement next.2.placement preserved.2.1 addresses]
            rw [dirty_snapshot]
            rfl
          have rejected := snapshotStep_reject_fixed FixedMemory.Controls.placement next.1 next.2 covered
            0 FixedMemory.Controls.f (some 2) typed dirty bad
          exact ⟨next,step,same,rejected,runSnapshots_rejected _ _ _ _ _ rejected⟩

/-- The full chronological input retains the changed state and stops at the
second map. The third map would restore old values if incorrectly executed. -/
theorem late_failure_prefix : ∃ next,
    runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [FixedMemory.Controls.changedRaw,dirty,FixedMemory.Controls.raw]=⟨next,[dirty,FixedMemory.Controls.raw]⟩ ∧
    next.1=expectedState ∧
    next.1≠FixedMemory.Controls.state ∧
    ReplayControls.freshRead next.1 .here=(.ok (FixedMemory.Controls.changedValues 0),expectedState) ∧
    ReplayControls.freshRead next.1 (.there .here)=(.ok (FixedMemory.Controls.changedValues 0),expectedState) := by
  first | solve | simp only
        | obtain ⟨next,step,same,rejected,tail⟩ := changed_then_rejected
          have completed : (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
              [FixedMemory.Controls.changedRaw]).pending=[] := by
            rw [runSnapshots_single _ _ _ _ _ step]
          have full : runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
              ([FixedMemory.Controls.changedRaw]++[dirty,FixedMemory.Controls.raw])=⟨next,[dirty,FixedMemory.Controls.raw]⟩ := by
            rw [runSnapshots_resume _ _ _ _ _ completed,runSnapshots_single _ _ _ _ _ step]
            exact tail
          refine ⟨next,full,same,?_,?_,?_⟩
          · rw [same]; exact ReplayControls.replay_state_not_original
          · rw [same]; rfl
          · rw [same]; rfl

end Solidity.Yul.Views.FixedInventory.RejectionControls
