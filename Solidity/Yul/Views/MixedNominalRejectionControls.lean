import Solidity.Yul.Views.MixedNominalInventoryRejection
import Solidity.Yul.Views.MixedNominalTransportControls

/-! Actual changed mixed struct followed by rejected dirty preparation keeps
the mutation, both aliases and the exact remaining suffix. Newly encoding the
stopped prefix replays its complete reached Source state. -/
namespace Solidity.Yul.Views.MixedNominalInventory.RejectionControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMember.StructControls
open Solidity.Yul.Views.MixedNominalInventory.CursorControls

def dirty : ByteView := mstore (fun _=>0) (placement.address 0) 65411
def later : ByteView := wordListView oldWords (fun _=>165) (placement.address 0)

theorem changed_then_rejected : ∃ next,
    snapshotStep placement state initial (changed (fun _=>165))=some next ∧ next.1=expected ∧
    snapshotStep placement next.1 next.2 dirty=none := by
  first | solve | simp only
        | obtain ⟨next,step,same,_⟩ := actual_step (fun _=>165)
          have preserved := snapshotStep_preserves placement state initial (changed (fun _=>165)) next step
          have addresses : next.2.placement.address=placement.address := preserved.2.2.2.1
          have typed : next.1.2.heap.ty 0=some ty := by rw [preserved.2.1]; rfl
          have bad : FixedNominalMember.snapshotStruct next.2.placement next.2.entries .memory box dirty
              (next.2.placement.address 0)=none := by
            unfold FixedNominalMember.snapshotStruct
            rw [addresses]
            have noneFields : FixedNominalMember.decodeFields next.2.placement next.2.entries
                (env.layout.fields box) dirty (placement.address 0)=none :=
              (snapshotStep_fields placement state initial (changed (fun _=>165)) next step
                (env.layout.fields box) dirty (placement.address 0)).trans rfl
            rw [Option.pmap_none' noneFields]
          exact ⟨next,step,same,snapshotStep_reject_struct placement next.1 next.2
            (preserved.2.2.2.2.2.2 covered) 0 .memory box typed dirty bad⟩

theorem late_failure : ∃ next,
    runSnapshots placement state initial [changed (fun _=>165),dirty,later]=⟨next,[dirty,later]⟩ ∧
    next.1=expected ∧ next.1≠state ∧
    RealizationControls.readFirst next.1 .here=some (.ok (.fixed (-32768) (by decide)),expected) ∧
    RealizationControls.readFirst next.1 (.there .here)=some (.ok (.fixed (-32768) (by decide)),expected) := by
  first | solve | simp only
        | obtain ⟨next,step,same,rejected⟩ := changed_then_rejected
          have complete : (runSnapshots placement state initial [changed (fun _=>165)]).pending=[] := by
            rw [runSnapshots_single _ _ _ _ _ step]
          have full : runSnapshots placement state initial ([changed (fun _=>165)]++[dirty,later])=⟨next,[dirty,later]⟩ := by
            rw [runSnapshots_resume _ _ _ _ _ complete,runSnapshots_single _ _ _ _ _ step]
            exact runSnapshots_rejected _ _ _ _ _ rejected
          refine ⟨next,full,same,?_,?_,?_⟩
          · rw [same]; exact RealizationControls.stale_state_rejected
          · rw [same]; rfl
          · rw [same]; rfl

theorem stopped_replay (residual : ByteView) : ∃ next,
    runSnapshots placement state initial [changed (fun _=>165),dirty,later]=⟨next,[dirty,later]⟩ ∧
    next.1=expected ∧
    writeback next.1 placement next.2.placement next.2.history next.2.entries
      (encodeMixedHeap next.2.placement next.2.entries residual)=some (.ok (),expected) := by
  first | solve | simp only
        | obtain ⟨next,run,same,_⟩ := late_failure
          have replay := every_prefix_replays [changed (fun _=>165),dirty,later] residual
          rw [run] at replay
          exact ⟨next,run,same,replay.trans (congrArg (fun s=>some ((.ok () : Except Source.Halt Unit),s)) same)⟩

end Solidity.Yul.Views.MixedNominalInventory.RejectionControls
