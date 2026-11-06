import Solidity.Yul.Views.FixedNominalInventoryCursor
import Solidity.Yul.Views.FixedNominalInventoryTransport
import Solidity.Yul.Views.FixedNominalHistoryReplay
import Solidity.Yul.Views.FixedNominalRealizationControls

/-! The shared cursor is inhabited by actual fixed-array writes. Projection
retains the complete changed Source state, both aliases and residual bytes.
Noncanonical fixed words fail preparation rather than manufacturing a halt. -/
namespace Solidity.Yul.Views.FixedNominalInventory.CursorControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalInventory.Controls

def initial : NominalInventory.SnapshotCursor FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state :=
  ⟨FixedNominalMemory.Controls.placement,.initial,[entry]⟩

theorem actual_step : ∃ next,
    snapshotStep FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial FixedNominalMemory.Controls.changed=some next ∧
    next.1=expectedState ∧
    CoversMixedHeap next.2.entries ∧
    next.2.placement.address=FixedNominalMemory.Controls.placement.address ∧
    encodeMixedHeap next.2.placement next.2.entries FixedNominalMemory.Controls.changed=FixedNominalMemory.Controls.changed ∧
    Source.MemOK FixedNominalMemory.Controls.env FixedNominalMemory.Controls.heap.ty next.1 := by
  first | solve | simp only [snapshotStep_source]
        | solve | rfl
        | have source := snapshotStep_source FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial FixedNominalMemory.Controls.changed
          rw [show writeback FixedNominalMemory.Controls.state FixedNominalMemory.Controls.placement initial.placement
            initial.history initial.entries FixedNominalMemory.Controls.changed=some (.ok (),expectedState) from changed_source] at source
          obtain ⟨next,step,same⟩ := Option.map_eq_some_iff.mp source
          have preserved := snapshotStep_preserves FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
            FixedNominalMemory.Controls.changed next step
          exact ⟨next,step,congrArg Prod.snd same,preserved.2.2.2.2.2.2 UnchangedControls.coverage,preserved.2.2.2.1,
            snapshotStep_reencode _ _ _ _ _ step,
            snapshotStep_MemOK _ _ _ _ _ step _ GeneratedControls.actual_MemOK⟩

theorem cursor_aliases : ∃ next,
    snapshotStep FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial FixedNominalMemory.Controls.changed=some next ∧
    RealizationControls.readFirst next.1 .here=(.ok (FixedNominalMemory.Controls.newValues 0),expectedState) ∧
    RealizationControls.readFirst next.1 (.there .here)=(.ok (FixedNominalMemory.Controls.newValues 0),expectedState) := by
  first | solve | simp only
        | solve | rfl
        | obtain ⟨next,step,same,_⟩ := actual_step
          refine ⟨next,step,?_,?_⟩ <;> rw [same] <;> rfl

theorem rejects_stale_cursor : ¬ ∃ next,
    snapshotStep FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial FixedNominalMemory.Controls.changed=some next ∧
    next.1=FixedNominalMemory.Controls.state := by
  first | solve | simp only
        | intro ⟨next,step,stale⟩
          obtain ⟨actual,run,same,_⟩ := actual_step
          have eq : actual=next := Option.some.inj (run.symm.trans step)
          exact RealizationControls.stale_state_rejected (same.symm.trans (eq ▸ stale))

theorem dirty_preparation : snapshotStep FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
    (mstore FixedNominalMemory.Controls.raw (FixedNominalMemory.Controls.placement.address 0) 65411)=none := by
  first | solve | simp only [snapshotStep_eq]
        | solve | decide
        | solve | rfl

theorem changed_history :
    (runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
      [FixedNominalMemory.Controls.changed]).pending=[] ∧
    (runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
      [FixedNominalMemory.Controls.changed]).current.1=expectedState := by
  first | solve | simp only
        | obtain ⟨next,step,same,_⟩ := actual_step
          rw [runSnapshots_single _ _ _ _ _ step]
          exact ⟨rfl,same⟩

theorem rejected_suffix :
    runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
      [mstore FixedNominalMemory.Controls.raw (FixedNominalMemory.Controls.placement.address 0) 65411,
       FixedNominalMemory.Controls.changed]=
      ⟨⟨FixedNominalMemory.Controls.state,initial⟩,
       [mstore FixedNominalMemory.Controls.raw (FixedNominalMemory.Controls.placement.address 0) 65411,
        FixedNominalMemory.Controls.changed]⟩ := by
  simp only [runSnapshots,dirty_preparation]

theorem every_reached_prefix_replays (ms : List ByteView) (residual : ByteView) :
    let out := (runSnapshots FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial ms).current
    writeback out.1 FixedNominalMemory.Controls.placement out.2.placement out.2.history out.2.entries
      (encodeMixedHeap out.2.placement out.2.entries residual)=some (.ok (),out.1) := by
  first | solve | simp only
        | exact (runSnapshots_replay FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.state initial
            UnchangedControls.coverage (by decide) GeneratedControls.heap_profile ms residual).2.2

end Solidity.Yul.Views.FixedNominalInventory.CursorControls
