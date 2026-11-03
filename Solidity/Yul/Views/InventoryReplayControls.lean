import Solidity.Yul.Views.InventoryReplay
import Solidity.Yul.Views.HeapEnumerationControls

/-! Actual changed and shrink-to-zero snapshots construct replay certificates.
Retained original capacity and current minimal capacity remain distinguishable;
replay does not reset the allocation origin to a smaller current shape. -/
namespace Solidity.Yul.Views.Controls

theorem changed_snapshot_replay : ∃ r : InventoryRealization mixedPlacement,
    inventoryAfter=withSourceHeap mixedState r.heap ∧
    RetainedAllocation mixedPlacement r.placement ∧
    inventoryStateWriteback (withSourceHeap mixedState r.heap) mixedPlacement r.placement r.history r.entries.reverse
      inventoryPhysical=some (.ok (),withSourceHeap mixedState r.heap) ∧
    Source.MemOK mixedEnv mixedHeap.ty (withSourceHeap mixedState r.heap) := by
  obtain ⟨r,run,types,covers,nodup,raw,safe,replay⟩ := inventoryStateWriteback_replay mixedState mixedPlacement
    mixedPlacement (retainInitial _ _) mixedEntries mixed_coverage mixed_distinct generated_mixed_types_supported
    inventoryPhysical (.ok (),inventoryAfter) inventory_source_step
  exact ⟨r,congrArg Prod.snd run,r.history,replay _ (List.reverse_perm _).symm,safe _ mixed_actual_MemOK⟩

theorem zero_snapshot_replay : ∃ r : InventoryRealization mixedPlacement,
    inventoryZeroAfter=withSourceHeap mixedState r.heap ∧
    RetainedAllocation mixedPlacement r.placement ∧
    inventoryStateWriteback (withSourceHeap mixedState r.heap) mixedPlacement r.placement r.history r.entries.reverse
      inventoryZeroPhysical=some (.ok (),withSourceHeap mixedState r.heap) ∧
    Source.MemOK mixedEnv mixedHeap.ty (withSourceHeap mixedState r.heap) := by
  obtain ⟨r,run,types,covers,nodup,raw,safe,replay⟩ := inventoryStateWriteback_replay mixedState mixedPlacement
    mixedPlacement (retainInitial _ _) mixedEntries mixed_coverage mixed_distinct generated_mixed_types_supported
    inventoryZeroPhysical (.ok (),inventoryZeroAfter) inventory_zero_source
  exact ⟨r,congrArg Prod.snd run,r.history,replay _ (List.reverse_perm _).symm,safe _ mixed_actual_MemOK⟩

private def replayObserved : List Nat :=
  match inventoryStateWriteback inventoryAfter mixedPlacement inventoryRealized.placement inventoryRealized.history
      inventoryRealized.entries.reverse inventoryPhysical with
  | some (.ok (),out)=>
    let a:=((Source.heapBytes (E:=mixedEnv) (Γ:=_) 0).run out).1.toOption.getD []
    let b:=((Source.heapBytes (E:=mixedEnv) (Γ:=_) 1).run out).1.toOption.getD []
    [out.2.heap.next]++a.map UInt8.toNat++b.map UInt8.toNat
  | _=>[]
/-- info: [6, 255, 0, 128, 254, 171, 97, 0] -/
#guard_msgs in #eval replayObserved
/-- info: (true, false) -/
#guard_msgs in #eval
  ((decodeInventoryUpdates mixedPlacement inventoryZeroRealized.placement inventoryZeroRealized.entries
      inventoryZeroRealized.entries inventoryPhysical).isSome,
   (decodeInventoryUpdates inventoryZeroRealized.placement inventoryZeroRealized.placement inventoryZeroRealized.entries
      inventoryZeroRealized.entries inventoryPhysical).isSome)
/-- info: true -/
#guard_msgs in #eval
  (inventoryStateWriteback inventoryZeroAfter mixedPlacement inventoryZeroRealized.placement inventoryZeroRealized.history
    inventoryZeroRealized.entries.reverse inventoryZeroPhysical).isSome
/-- info: false -/
#guard_msgs in #eval replayObserved==[6,17,34,51,255,97]
end Solidity.Yul.Views.Controls
