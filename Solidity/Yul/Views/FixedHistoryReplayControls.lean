import Solidity.Yul.Views.FixedHistoryReplay
import Solidity.Yul.Views.FixedInventoryRejectionControls

/-! The actual changed-then-rejected history retains a replayable physical
view. Its replay preserves the reached changed state and excludes restoration
of the original state; residual bytes remain arbitrary in the universal law. -/
namespace Solidity.Yul.Views.FixedInventory.HistoryReplayControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedInventory.RealizationControls
open Solidity.Yul.Views.FixedInventory.CursorControls
open Solidity.Yul.Views.FixedInventory.HistoryControls
open Solidity.Yul.Views.FixedInventory.RejectionControls

theorem prefix_replay (ms : List ByteView) (residual : ByteView) :
    let out := (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial ms).current
    writeback out.1 FixedMemory.Controls.placement out.2.placement out.2.history out.2.entries
      (encodeMixedHeap out.2.placement out.2.entries residual)=some (.ok (),out.1) := by
  first | solve | simp only
        | exact (runSnapshots_replay FixedMemory.Controls.placement FixedMemory.Controls.state initial
            coverage (by decide) ReplayControls.heap_profile ms residual).2.2

theorem late_rejection_replay (residual : ByteView) : ∃ next,
    runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [FixedMemory.Controls.changedRaw,dirty,FixedMemory.Controls.raw]=⟨next,[dirty,FixedMemory.Controls.raw]⟩ ∧
    next.1=expectedState ∧
    writeback next.1 FixedMemory.Controls.placement next.2.placement next.2.history next.2.entries
      (encodeMixedHeap next.2.placement next.2.entries residual)=some (.ok (),expectedState) := by
  first | solve | simp only
        | obtain ⟨next,run,same,_⟩ := late_failure_prefix
          have replay := prefix_replay [FixedMemory.Controls.changedRaw,dirty,FixedMemory.Controls.raw] residual
          rw [run] at replay
          exact ⟨next,run,same,replay.trans (congrArg
            (fun s=>some ((.ok () : Except Source.Halt Unit),s)) same)⟩

theorem replay_cannot_restore_original (residual : ByteView) : ∃ next :
    Σ s : Source.EMState FixedMemory.Controls.env [FixedMemory.Controls.ty,FixedMemory.Controls.ty],
      NominalInventory.SnapshotCursor FixedMemory.Controls.placement s,
    next.1=expectedState ∧
    writeback next.1 FixedMemory.Controls.placement next.2.placement next.2.history next.2.entries
      (encodeMixedHeap next.2.placement next.2.entries residual)≠some (.ok (),FixedMemory.Controls.state) := by
  first | solve | simp only
        | obtain ⟨next,_,same,replay⟩ := late_rejection_replay residual
          refine ⟨next,same,?_⟩
          rw [replay]
          intro wrong
          exact ReplayControls.replay_state_not_original
            (congrArg (fun result : Option (Except Source.Halt Unit × Source.EMState FixedMemory.Controls.env
              [FixedMemory.Controls.ty,FixedMemory.Controls.ty]) => result.map Prod.snd) wrong
              |> Option.some.inj)

end Solidity.Yul.Views.FixedInventory.HistoryReplayControls
