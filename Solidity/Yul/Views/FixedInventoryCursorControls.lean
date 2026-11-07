import Solidity.Yul.Views.FixedInventoryCursor
import Solidity.Yul.Views.FixedInventoryReplayControls

/-! The shared cursor is inhabited by actual fixed-array writes. Projection
retains the complete changed Source state, both aliases and residual bytes.
Noncanonical fixed words fail preparation rather than manufacturing a halt. -/
namespace Solidity.Yul.Views.FixedInventory.CursorControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedInventory.RealizationControls

def initial : NominalInventory.SnapshotCursor FixedMemory.Controls.placement FixedMemory.Controls.state :=
  ⟨FixedMemory.Controls.placement,.initial,[entry]⟩

theorem actual_step : ∃ next,
    snapshotStep FixedMemory.Controls.placement FixedMemory.Controls.state initial FixedMemory.Controls.changedRaw=some next ∧
    next.1=expectedState ∧
    CoversMixedHeap next.2.entries ∧
    next.2.placement.address=FixedMemory.Controls.placement.address ∧
    encodeMixedHeap next.2.placement next.2.entries FixedMemory.Controls.changedRaw=FixedMemory.Controls.changedRaw ∧
    Source.MemOK FixedMemory.Controls.env FixedMemory.Controls.heap.ty next.1 := by
  first | solve | simp only [snapshotStep_source]
        | solve | rfl
        | have source := snapshotStep_source FixedMemory.Controls.placement FixedMemory.Controls.state initial FixedMemory.Controls.changedRaw
          rw [show writeback FixedMemory.Controls.state FixedMemory.Controls.placement initial.placement
            initial.history initial.entries FixedMemory.Controls.changedRaw=some (.ok (),expectedState) from changed_source] at source
          obtain ⟨next,step,same⟩ := Option.map_eq_some_iff.mp source
          have preserved := snapshotStep_preserves FixedMemory.Controls.placement FixedMemory.Controls.state initial
            FixedMemory.Controls.changedRaw next step
          exact ⟨next,step,congrArg Prod.snd same,preserved.2.2.2.2.2.2 coverage,preserved.2.2.2.1,
            snapshotStep_reencode _ _ _ _ _ step,
            snapshotStep_MemOK _ _ _ _ _ step _ FixedMemory.Controls.actual_MemOK⟩

theorem cursor_aliases : ∃ next,
    snapshotStep FixedMemory.Controls.placement FixedMemory.Controls.state initial FixedMemory.Controls.changedRaw=some next ∧
    ReplayControls.freshRead next.1 .here=(.ok (FixedMemory.Controls.changedValues 0),expectedState) ∧
    ReplayControls.freshRead next.1 (.there .here)=(.ok (FixedMemory.Controls.changedValues 0),expectedState) := by
  first | solve | simp only
        | solve | rfl
        | obtain ⟨next,step,same,_⟩ := actual_step
          refine ⟨next,step,?_,?_⟩ <;> rw [same] <;> rfl

theorem rejects_stale_cursor : ¬ ∃ next,
    snapshotStep FixedMemory.Controls.placement FixedMemory.Controls.state initial FixedMemory.Controls.changedRaw=some next ∧
    next.1=FixedMemory.Controls.state := by
  first | solve | simp only
        | intro ⟨next,step,stale⟩
          obtain ⟨actual,run,same,_⟩ := actual_step
          have eq : actual=next := Option.some.inj (run.symm.trans step)
          exact ReplayControls.replay_state_not_original (same.symm.trans (eq ▸ stale))

theorem dirty_preparation : snapshotStep FixedMemory.Controls.placement FixedMemory.Controls.state initial
    (mstore FixedMemory.Controls.raw (FixedMemory.Controls.placement.address 0) 65411)=none := by
  first | solve | simp only [snapshotStep_eq]
        | solve | decide
        | solve | rfl

end Solidity.Yul.Views.FixedInventory.CursorControls
