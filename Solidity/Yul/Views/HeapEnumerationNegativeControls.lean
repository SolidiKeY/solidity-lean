import Solidity.Yul.Views.HeapEnumerationControls
import Solidity.Yul.Views.GeneratedRetainedControls

namespace Solidity.Yul.Views.Controls

def generatedDirtyBoolSnapshot := mstore inventoryPhysical 896 2

theorem generated_dirty_snapshot_none : (decodeInventoryUpdates mixedPlacement mixedPlacement
    (generatedHeapEntries mixedPlacement) (generatedHeapEntries mixedPlacement) generatedDirtyBoolSnapshot).isNone := by decide

/-- This is unsupported canonical PREPARATION, not Yul refusal/no-op semantics. -/
theorem generated_dirty_snapshot_result : enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) generatedDirtyBoolSnapshot = .ok none := by
  unfold enumeratedMemoryWriteback
  rw [generated_mixed_prepared]
  change Except.ok ((decodeInventoryUpdates _ _ _ _ _).map _) = _
  rw [Option.isNone_iff_eq_none.mp generated_dirty_snapshot_none]
  rfl

def generatedOutsideCapacity := mstore generatedSparsePhysical 256 33

theorem generated_actual_extent_guard : (decodeInventoryUpdates enumerationSparsePlacement enumerationSparsePlacement
    (generatedHeapEntries enumerationSparsePlacement) (generatedHeapEntries enumerationSparsePlacement) generatedOutsideCapacity).isNone := by decide

theorem generated_missing_is_not_unsupported : missingHeapCells enumerationSparsePlacement = [0,1,3,4] ∧
    unsupportedHeapCells enumerationSparsePlacement = [] ∧
    unsupportedHeapCells enumerationDanglingPlacement = [2] := by decide

end Solidity.Yul.Views.Controls
