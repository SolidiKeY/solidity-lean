import Solidity.Yul.Views.FixedNominalInventoryRejection
import Solidity.Yul.Views.FixedNominalTransportControls

/-! A real changed fixed snapshot is followed by noncanonical preparation.
The successful mutation and both aliases survive, the exact rejected suffix is
retained, and later snapshots are not run. No Source halt is manufactured. -/
namespace Solidity.Yul.Views.FixedNominalInventory.RejectionControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalInventory.Controls
open Solidity.Yul.Views.FixedNominalInventory.CursorControls

def dirty : ByteView := mstore FixedNominalMemory.Controls.raw
  (FixedNominalMemory.Controls.placement.address 0) 65411

theorem dirty_snapshot : snapshot FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.name (some 2)
    dirty (FixedNominalMemory.Controls.placement.address 0)=none := by
  first | solve | simp only [snapshot]
        | solve | decide
        | solve | rfl

theorem changed_then_rejected : ∃ next,
    snapshotStep FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial FixedNominalMemory.Controls.changed=some next ∧
    next.1=expectedState ∧
    snapshotStep FixedNominalMemory.Controls.placement next.1 next.2 dirty=none ∧
    runSnapshots FixedNominalMemory.Controls.placement next.1 next.2 [dirty,FixedNominalMemory.Controls.raw]=
      ⟨next,[dirty,FixedNominalMemory.Controls.raw]⟩ := by
  first | solve | simp only
        | obtain ⟨next,step,same,covered,addresses,_,_⟩ := actual_step
          have preserved := snapshotStep_preserves FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
            FixedNominalMemory.Controls.changed next step
          have typed : next.1.2.heap.ty 0=some FixedNominalMemory.Controls.ty := by
            rw [preserved.2.1]
            rfl
          have bad : snapshot next.2.placement FixedNominalMemory.Controls.name (some 2) dirty
              (next.2.placement.address 0)=none := by
            rw [addresses]
            rw [snapshot_transport FixedNominalMemory.Controls.placement next.2.placement preserved.2.1 addresses]
            rw [dirty_snapshot]
            rfl
          have rejected := snapshotStep_reject_nominal FixedNominalMemory.Controls.placement next.1 next.2 covered
            0 FixedNominalMemory.Controls.name (some 2) typed dirty bad
          exact ⟨next,step,same,rejected,runSnapshots_rejected _ _ _ _ _ rejected⟩

/-- The full chronological input retains the changed state and stops at the
second map. The third map would restore old values if incorrectly executed. -/
theorem late_failure_prefix : ∃ next,
    runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
      [FixedNominalMemory.Controls.changed,dirty,FixedNominalMemory.Controls.raw]=⟨next,[dirty,FixedNominalMemory.Controls.raw]⟩ ∧
    next.1=expectedState ∧
    next.1≠FixedNominalMemory.Controls.state ∧
    RealizationControls.readFirst next.1 .here=(.ok (FixedNominalMemory.Controls.newValues 0),expectedState) ∧
    RealizationControls.readFirst next.1 (.there .here)=(.ok (FixedNominalMemory.Controls.newValues 0),expectedState) := by
  first | solve | simp only
        | obtain ⟨next,step,same,rejected,tail⟩ := changed_then_rejected
          have completed : (runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
              [FixedNominalMemory.Controls.changed]).pending=[] := by
            rw [runSnapshots_single _ _ _ _ _ step]
          have full : runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
              ([FixedNominalMemory.Controls.changed]++[dirty,FixedNominalMemory.Controls.raw])=⟨next,[dirty,FixedNominalMemory.Controls.raw]⟩ := by
            rw [runSnapshots_resume _ _ _ _ _ completed,runSnapshots_single _ _ _ _ _ step]
            exact tail
          refine ⟨next,full,same,?_,?_,?_⟩
          · rw [same]; exact RealizationControls.stale_state_rejected
          · rw [same]; rfl
          · rw [same]; rfl

theorem stopped_replay (residual : ByteView) : ∃ next,
    runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
      [FixedNominalMemory.Controls.changed,dirty,FixedNominalMemory.Controls.raw]=⟨next,[dirty,FixedNominalMemory.Controls.raw]⟩ ∧
    next.1=expectedState ∧
    writeback next.1 FixedNominalMemory.Controls.placement next.2.placement next.2.history next.2.entries
      (encodeMixedHeap next.2.placement next.2.entries residual)=some (.ok (),expectedState) := by
  first | solve | simp only
        | obtain ⟨next,run,same,_⟩ := late_failure_prefix
          have replay := every_reached_prefix_replays
            [FixedNominalMemory.Controls.changed,dirty,FixedNominalMemory.Controls.raw] residual
          rw [run] at replay
          exact ⟨next,run,same,replay.trans (congrArg (fun s=>some ((.ok () : Except Source.Halt Unit),s)) same)⟩

end Solidity.Yul.Views.FixedNominalInventory.RejectionControls
