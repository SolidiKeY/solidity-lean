import Solidity.Yul.Views.InventoryAliasControls
import Solidity.Yul.Views.InventoryErrorControls

namespace Solidity.Yul.Views.Controls

def inventoryZeroPhysical := mstore inventoryPhysical 1152 0

theorem inventory_zero_decode_exists : (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries inventoryZeroPhysical).isSome := by decide

def inventoryZeroUpdates := (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries inventoryZeroPhysical).get inventory_zero_decode_exists

theorem inventory_zero_decoded : decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries inventoryZeroPhysical = some inventoryZeroUpdates :=
  (Option.some_get inventory_zero_decode_exists).symm

def inventoryZeroRealized := realizeInventory mixedPlacement mixedPlacement (retainInitial _ _) inventoryZeroUpdates mixedHeap mixedPlacement (retainInitial _ _) rfl mixedEntries
def inventoryZeroAfter := withSourceHeap mixedState inventoryZeroRealized.heap

theorem inventory_zero_source : inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries inventoryZeroPhysical = some (.ok (),inventoryZeroAfter) := by
  unfold inventoryStateWriteback
  rw [inventory_zero_decoded,Option.map_some]
  exact congrArg some (realizeInventory_run mixedPlacement mixedPlacement (retainInitial _ _) inventoryZeroUpdates mixedState mixedPlacement (retainInitial _ _) rfl mixedEntries)

theorem inventory_zero_types : inventoryZeroRealized.heap.ty = mixedHeap.ty := realizeInventory_types _ _ _ inventoryZeroUpdates _ _ _ rfl mixedEntries

def inventoryRegrown := realizeInventory mixedPlacement mixedPlacement (retainInitial _ _) inventoryUpdates inventoryZeroRealized.heap
  inventoryZeroRealized.placement inventoryZeroRealized.history inventory_zero_types inventoryZeroRealized.entries

def inventoryRegrownState := withSourceHeap inventoryZeroAfter inventoryRegrown.heap

/-- Decode against the ACTUAL zero-shape current placement/candidates. The full
original owned inventory is transported by its proved invariant types/IDs. -/
theorem inventory_actual_regrow_preparation : sequentialInventory mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries inventoryZeroRealized.heap
    inventoryZeroRealized.placement inventoryZeroRealized.history inventory_zero_types inventoryZeroRealized.entries inventoryPhysical = some inventoryRegrown := by
  have seq := sequentialInventory_snapshot_aux mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries mixedEntries inventoryZeroRealized.heap
    inventoryZeroRealized.placement inventoryZeroRealized.history inventory_zero_types inventoryZeroRealized.entries
    (realizeInventory_choices _ _ _ inventoryZeroUpdates _ _ _ rfl mixedEntries).1
    (realizeInventory_decoder _ _ _ inventoryZeroUpdates _ _ _ rfl mixedEntries) inventoryPhysical
  rw [inventory_decoded,Option.map_some] at seq
  exact seq

theorem inventory_actual_regrow_source : (runInventoryUpdates inventoryUpdates).run inventoryZeroAfter = (.ok (),inventoryRegrownState) :=
  realizeInventory_run mixedPlacement mixedPlacement (retainInitial _ _) inventoryUpdates inventoryZeroAfter inventoryZeroRealized.placement
    inventoryZeroRealized.history inventory_zero_types inventoryZeroRealized.entries

theorem inventory_regrow_all_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H inventoryRegrownState := by
  have zero := inventoryStateWriteback_MemOK H mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries inventoryZeroPhysical _ inventory_zero_source ok
  have values (u : OwnedInventoryUpdate mixedPlacement mixedPlacement) (_ : u ∈ inventoryUpdates) : Source.DataOK mixedEnv inventoryZeroAfter.2.heap.ty u.object.data := by
    change Source.DataOK mixedEnv inventoryZeroRealized.heap.ty u.object.data
    rw [inventory_zero_types]
    exact u.object.image.dataOK
  have keep := runInventoryUpdates_MemOK inventoryUpdates H inventoryZeroAfter values zero
  rw [inventory_actual_regrow_source] at keep
  exact keep

theorem inventory_regrow_inhabited : Source.MemOK mixedEnv mixedHeap.ty inventoryRegrownState := inventory_regrow_all_H _ mixed_actual_MemOK

theorem inventory_zero_shape_history : inventoryZeroRealized.placement.shape 4 = .array true 0 ∧ RetainedAllocation mixedPlacement inventoryZeroRealized.placement := ⟨rfl,inventoryZeroRealized.history⟩

theorem inventory_regrow_shape_history : inventoryRegrown.placement.shape 4 = .array true 2 ∧ RetainedAllocation mixedPlacement inventoryRegrown.placement := ⟨rfl,inventoryRegrown.history⟩

def inventoryZeroAlias := withSourceHeap jointAliasState inventoryZeroRealized.heap
def inventoryRegrowAlias := withSourceHeap jointAliasState inventoryRegrown.heap

theorem inventory_zero_alias_panic (horizon : Nat) : (readJointAlias false 0 horizon).run inventoryZeroAlias =
    (.error (.revert (Source.panicData .index)),inventoryZeroAlias) := rfl

theorem inventory_regrow_cell1 : inventoryRegrown.heap.get 1 = some ⟨.string .memory,.string inventoryNewString⟩ := by
  have symbolic : inventoryRegrown.heap.get 1 = some ⟨.string .memory,decodeStringObject mixedLayout inventoryPhysical 384⟩ := rfl
  rw [inventory_string_decode] at symbolic
  exact symbolic

theorem inventory_regrow_cell4 : inventoryRegrown.heap.get 4 = some ⟨mixedArrayTy,dynamicMemberData mixedLayout (.bytes .memory) 2 inventoryRValues⟩ := rfl

theorem inventory_regrown_true_aliases (horizon : Nat) :
    (readJointAlias true 0 horizon).run inventoryRegrowAlias = (.ok inventoryNewString,inventoryRegrowAlias) ∧
    (readJointAlias false 1 horizon).run inventoryRegrowAlias = (.ok inventoryNewString,inventoryRegrowAlias) :=
  ⟨readJointAlias_known inventoryRegrowAlias true 0 horizon 4 1 2 inventoryRValues inventoryNewString rfl inventory_regrow_cell4 (by decide) rfl inventory_regrow_cell1,
   readJointAlias_known inventoryRegrowAlias false 1 horizon 4 1 2 inventoryRValues inventoryNewString rfl inventory_regrow_cell4 (by decide) rfl inventory_regrow_cell1⟩

theorem inventory_repeated_owned_candidate : (runInventoryUpdates [inventoryManual0,inventoryManual0,inventoryManual1,inventoryManual2]).run mixedState =
    (runInventoryUpdates [inventoryManual0,inventoryManual1,inventoryManual2]).run mixedState :=
  runInventoryUpdates_repeat inventoryManual0 [inventoryManual1,inventoryManual2] mixedState rfl

end Solidity.Yul.Views.Controls
