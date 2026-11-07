import Solidity.Yul.Views.MixedNominalInventoryTransport
import Solidity.Yul.Views.MixedNominalInventoryCursor
import Solidity.Yul.Views.MixedNominalHistoryReplay
import Solidity.Yul.Views.MixedNominalRealizationControls

/-! Actual mixed struct snapshots inhabit shared cursor/progress carriers.
Source projection, changed alias reads and arbitrary-prefix replay follow the
concrete writes. Supplied snapshots do not establish physical provenance. -/
namespace Solidity.Yul.Views.MixedNominalInventory.CursorControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMember.StructControls

def initial : NominalInventory.SnapshotCursor placement state := ⟨placement,.initial,[entry]⟩

theorem actual_step (residual : ByteView) : ∃ next,
    snapshotStep placement state initial (changed residual)=some next ∧ next.1=expected ∧
    encodeMixedHeap next.2.placement next.2.entries (changed residual)=changed residual ∧
    Source.MemOK env heap.ty next.1 := by
  first | solve | simp only [snapshotStep_source]
        | have source := snapshotStep_source placement state initial (changed residual)
          rw [show writeback state placement initial.placement initial.history initial.entries (changed residual)=
            some (.ok (),expected) from Controls.changed_source residual] at source
          obtain ⟨next,step,same⟩ := Option.map_eq_some_iff.mp source
          exact ⟨next,step,congrArg Prod.snd same,snapshotStep_reencode _ _ _ _ _ step,
            snapshotStep_MemOK _ _ _ _ _ step _ GeneratedControls.actual_MemOK⟩

theorem changed_history (residual : ByteView) :
    (runSnapshots placement state initial [changed residual]).pending=[] ∧
    (runSnapshots placement state initial [changed residual]).current.1=expected := by
  first | solve | simp only
        | obtain ⟨next,step,same,_⟩ := actual_step residual
          rw [runSnapshots_single _ _ _ _ _ step]
          exact ⟨rfl,same⟩

theorem both_aliases (residual : ByteView) : ∃ next,
    snapshotStep placement state initial (changed residual)=some next ∧
    RealizationControls.readFirst next.1 .here=some (.ok (.fixed (-32768) (by decide)),expected) ∧
    RealizationControls.readFirst next.1 (.there .here)=some (.ok (.fixed (-32768) (by decide)),expected) := by
  first | solve | simp only
        | obtain ⟨next,step,same,_⟩ := actual_step residual
          refine ⟨next,step,?_,?_⟩ <;> rw [same] <;> rfl

theorem dirty_preparation : snapshotStep placement state initial
    (mstore (fun _=>0) (placement.address 0) 65411)=none := rfl

theorem rejected_suffix : runSnapshots placement state initial
    [mstore (fun _=>0) (placement.address 0) 65411,changed (fun _=>165)]=
    ⟨⟨state,initial⟩,[mstore (fun _=>0) (placement.address 0) 65411,changed (fun _=>165)]⟩ := by
  simp only [runSnapshots,dirty_preparation]

theorem every_prefix_replays (ms : List ByteView) (residual : ByteView) :
    let out := (runSnapshots placement state initial ms).current
    writeback out.1 placement out.2.placement out.2.history out.2.entries
      (encodeMixedHeap out.2.placement out.2.entries residual)=some (.ok (),out.1) := by
  first | solve | simp only
        | exact (runSnapshots_replay placement state initial covered (by decide) GeneratedControls.heap_profile ms residual).2.2

end Solidity.Yul.Views.MixedNominalInventory.CursorControls
