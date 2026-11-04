import Solidity.Yul.Views.FixedInventoryHistory
import Solidity.Yul.Views.FixedInventoryCursorControls

/-! Actual supplied-snapshot chronology controls: changed success, rejected
preparation retaining later input, owner safety and exact final raw map. The
supplied list is input, not a new fuel bound or physical provenance witness. -/
namespace Solidity.Yul.Views.FixedInventory.HistoryControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedInventory.RealizationControls
open Solidity.Yul.Views.FixedInventory.CursorControls

def dirty : ByteView := mstore FixedMemory.Controls.raw (FixedMemory.Controls.placement.address 0) 65411

theorem changed_complete :
    (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [FixedMemory.Controls.changedRaw]).pending=[] ∧
    (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [FixedMemory.Controls.changedRaw]).current.1=expectedState := by
  first | solve | simp only [runSnapshots]
        | obtain ⟨next,step,same,_⟩ := actual_step
          simp only [runSnapshots,step]
          exact ⟨trivial,same⟩

theorem rejected_keeps_suffix :
    runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [dirty,FixedMemory.Controls.changedRaw]=
      ⟨⟨FixedMemory.Controls.state,initial⟩,[dirty,FixedMemory.Controls.changedRaw]⟩ := by
  first | solve | simp only [runSnapshots,show snapshotStep FixedMemory.Controls.placement
            FixedMemory.Controls.state initial dirty=none from dirty_preparation]
        | solve | rfl

theorem rejected_does_not_apply_later :
    (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [dirty,FixedMemory.Controls.changedRaw]).current.1≠expectedState := by
  first | solve | simp only [rejected_keeps_suffix]
        | rw [rejected_keeps_suffix]
          exact Ne.symm ReplayControls.replay_state_not_original

theorem changed_last_raw :
    let out := (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [FixedMemory.Controls.changedRaw]).current
    encodeMixedHeap out.2.placement out.2.entries FixedMemory.Controls.changedRaw=FixedMemory.Controls.changedRaw := by
  obtain ⟨next,step,_,_,_,raw,_⟩ := actual_step
  rw [runSnapshots_single _ _ _ _ _ step]
  exact raw

theorem all_prefixes_safe (ms : List ByteView) :
    Source.MemOK FixedMemory.Controls.env FixedMemory.Controls.heap.ty
      (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial ms).current.1 := by
  first | solve | simp only
        | exact runSnapshots_MemOK _ _ _ ms _ FixedMemory.Controls.actual_MemOK

theorem changed_aliases :
    ReplayControls.freshRead (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [FixedMemory.Controls.changedRaw]).current.1 .here=(.ok (FixedMemory.Controls.changedValues 0),expectedState) ∧
    ReplayControls.freshRead (runSnapshots FixedMemory.Controls.placement FixedMemory.Controls.state initial
      [FixedMemory.Controls.changedRaw]).current.1 (.there .here)=(.ok (FixedMemory.Controls.changedValues 0),expectedState) := by
  first | solve | simp only [changed_complete.2]
        | rw [changed_complete.2]
          exact ⟨rfl,rfl⟩

end Solidity.Yul.Views.FixedInventory.HistoryControls
