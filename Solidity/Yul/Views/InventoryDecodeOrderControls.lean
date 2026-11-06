import Solidity.Yul.Views.InventoryDecodeOrder
import Solidity.Yul.Views.InventoryErrorControls

/-! Reverse visits of a genuinely changed six-root snapshot retain complete
source results and refreshed sequential realization. Canonical preparation
failure is distinguished from an actual wrong-typing source error prefix. -/
namespace Solidity.Yul.Views.Controls

theorem changed_reverse_source :
    (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries.reverse inventoryPhysical).map
      (fun us=>(runInventoryUpdates us).run mixedState)=some (.ok (),inventoryAfter) :=
  (inventoryStateWriteback_visit_perm mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries mixedEntries.reverse (List.reverse_perm _).symm mixed_distinct inventoryPhysical).symm.trans inventory_source_step

theorem changed_reverse_sequential :
    (sequentialInventory mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries.reverse mixedHeap
      mixedPlacement (retainInitial _ _) rfl mixedEntries inventoryPhysical).map
      (fun result=>((.ok () : Except Source.Halt Unit),withSourceHeap mixedState result.heap))=
      some (.ok (),inventoryAfter) :=
  (inventoryStateWriteback_sequential_perm mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries mixedEntries.reverse (List.reverse_perm _).symm mixed_distinct inventoryPhysical).symm.trans inventory_source_step

theorem changed_reverse_alias_state :
    (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries.reverse inventoryPhysical).map
      (fun us=>(runInventoryUpdates us).run jointAliasState)=some (.ok (),inventoryAliasAfter) := by
  have perm := decodedInventory_runs_perm mixedPlacement mixedPlacement mixedEntries
    (List.reverse_perm mixedEntries).symm mixed_distinct inventoryPhysical jointAliasState rfl
  rw [← perm,inventory_decoded,Option.map_some]
  exact congrArg some (realizeInventory_run mixedPlacement mixedPlacement (retainInitial _ _)
    inventoryUpdates jointAliasState mixedPlacement (retainInitial _ _) rfl mixedEntries)

private def invalid := mstore inventoryPhysical 896 2

theorem invalid_forward : decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries invalid=none := by
  apply Option.isNone_iff_eq_none.mp
  decide

theorem invalid_reverse : decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries.reverse invalid=none :=
  (decodeInventoryUpdates_perm mixedPlacement mixedPlacement mixedEntries (List.reverse_perm mixedEntries).symm invalid).1.mp invalid_forward

/-- The order theorem requires the actual original heap typing: the existing
wrong-typing fixture instead has a genuine source failure after caller writes. -/
theorem wrong_typing_prefix : (runInventoryUpdates [inventoryManual0,inventoryManual1,inventoryManual2]).run inventoryFaultState=
    (.error (.stuck "memory write type"),inventoryFaultPrefix) := inventory_actual_late_source_error

private def observed : List Nat :=
  match (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries.reverse inventoryPhysical).map
      (fun us=>(runInventoryUpdates us).run mixedState) with
  | some (.ok (),out)=>
    let a:=((Source.heapBytes (E:=mixedEnv) (Γ:=_) 0).run out).1.toOption.getD []
    let b:=((Source.heapBytes (E:=mixedEnv) (Γ:=_) 1).run out).1.toOption.getD []
    [out.2.heap.next]++a.map UInt8.toNat++b.map UInt8.toNat
  | _=>[]
/-- info: [6, 255, 0, 128, 254, 171, 97, 0] -/
#guard_msgs in #eval observed
/-- info: (true, true) -/
#guard_msgs in #eval ((decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries invalid).isNone,
  (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries.reverse invalid).isNone)
/-- info: false -/
#guard_msgs in #eval observed==[6,17,34,51,255,97]
end Solidity.Yul.Views.Controls
