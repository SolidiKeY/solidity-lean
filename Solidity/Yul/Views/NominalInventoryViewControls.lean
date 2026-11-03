import Solidity.Yul.Views.NominalInventoryView
import Solidity.Yul.Views.NominalInventoryControls

/-! An inhabited changed-source result with constructed physical output view
and retained allocation history, using the existing canonical nominal fixture. -/
namespace Solidity.Yul.Views.NominalInventory.ViewControls
open Solidity.Yul.Views

theorem coverage : CoversMixedHeap [NominalInventory.Controls.entry] := by
  intro a present
  have bound : a<NominalMemory.Controls.heap.next := by
    apply Nat.lt_of_not_le
    intro high
    rw [NominalMemory.Controls.heap.bounded a high] at present
    cases present
  change a<1 at bound
  have zero : a=0 := by omega
  subst a
  exact ⟨NominalInventory.Controls.entry,List.mem_cons_self,rfl⟩

/-- Exact actual source output and every raw byte have the same realized heap.
The witness carries the constructed Placement and RetainedAllocation. -/
theorem changed_view : ∃ realized : InventoryRealization NominalMemory.Controls.placement,
    withSourceHeap NominalMemory.Controls.state realized.heap=NominalMemory.Controls.newState ∧
    CoversMixedHeap realized.entries ∧ (realized.entries.map MixedHeapEntry.id).Nodup ∧
    realized.heap.ty=NominalMemory.Controls.heap.ty ∧ realized.heap.next=1 ∧
    realized.placement.address=NominalMemory.Controls.placement.address ∧
    realized.placement.free=NominalMemory.Controls.placement.free ∧
    encodeMixedHeap realized.placement realized.entries NominalMemory.Controls.newRaw=
      NominalMemory.Controls.newRaw := by
  obtain ⟨realized,run,covered,distinct,types,next,addresses,free,raw⟩ :=
    writeback_view NominalMemory.Controls.state NominalMemory.Controls.placement
      NominalMemory.Controls.placement .initial [NominalInventory.Controls.entry] coverage (by decide)
      NominalMemory.Controls.newRaw _ NominalInventory.Controls.changed_source
  exact ⟨realized,(congrArg Prod.snd run).symm,covered,distinct,types,next,addresses,free,raw⟩

theorem changed_owner : Source.MemOK NominalMemory.Controls.env NominalMemory.Controls.heap.ty
    NominalMemory.Controls.newState := NominalInventory.Controls.changed_MemOK

end Solidity.Yul.Views.NominalInventory.ViewControls
