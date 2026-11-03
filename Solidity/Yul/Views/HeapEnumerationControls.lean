import Solidity.Yul.Views.EnumeratedMemory
import Solidity.Yul.Views.HeapPreparationMemOK
import Solidity.Yul.Views.InventoryRetainedControls

namespace Solidity.Yul.Views.Controls

theorem generated_mixed_no_unsupported : unsupportedHeapCells mixedPlacement = [] := by decide

theorem generated_mixed_no_holes : missingHeapCells mixedPlacement = [] := by decide

theorem generated_mixed_ids : (generatedHeapEntries mixedPlacement).map MixedHeapEntry.id = [0,1,2,3,4,5] := by decide

theorem generated_mixed_prepared : prepareHeapInventory mixedPlacement = .ok (generatedHeapEntries mixedPlacement) := by
  unfold prepareHeapInventory
  rw [generated_mixed_no_unsupported]

theorem generated_mixed_coverage : CoversMixedHeap (generatedHeapEntries mixedPlacement) :=
  generatedHeapEntries_coverage _ generated_mixed_no_unsupported

/-- The actual source execution now starts only from Heap/Placement/snapshot:
no supplied six-entry list, image/read/coverage/output-law witness. -/
theorem generated_mixed_source : enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) inventoryPhysical =
    .ok (some (.ok (),inventoryAfter)) := by
  unfold enumeratedMemoryWriteback
  rw [generated_mixed_prepared]
  exact congrArg Except.ok inventory_source_step_generated
where
  inventory_source_step_generated : inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) (generatedHeapEntries mixedPlacement) inventoryPhysical = some (.ok (),inventoryAfter) := by
    exact inventory_source_step

theorem generated_mixed_all_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H inventoryAfter :=
  enumeratedMemoryWriteback_MemOK H mixedState mixedPlacement mixedPlacement (retainInitial _ _) inventoryPhysical _ generated_mixed_source ok

theorem generated_mixed_actual_MemOK : Source.MemOK mixedEnv mixedHeap.ty inventoryAfter := generated_mixed_all_H _ mixed_actual_MemOK

theorem generated_mixed_types_supported (a : Nat) (τ : Source.STy) (d : Source.Data mixedLayout τ)
    (found : mixedHeap.get a = some ⟨τ,d⟩) : InventoryTypeSupported mixedEnv τ := by
  have present : (mixedHeap.cells a).isSome := by rw [show mixedHeap.cells a = some ⟨τ,d⟩ from found]; rfl
  obtain ⟨e,member,same⟩ := mixed_coverage a present
  have eq := Option.some.inj (found.symm.trans (same ▸ e.found))
  cases eq
  exact inventory_mixed_support e member

theorem generated_mixed_owner_preparation : prepareHeapInventory mixedPlacement = .ok (generatedHeapEntries mixedPlacement) :=
  ownerMemOK_prepares_inventory mixedHeap.ty mixedState mixedPlacement mixed_actual_MemOK generated_mixed_types_supported

theorem generated_mixed_unchanged : enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    (encodeMixedHeap mixedPlacement (generatedHeapEntries mixedPlacement) mixedResidual) = .ok (some (.ok (),mixedState)) :=
  enumeratedMemory_unchanged mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedResidual
    generated_mixed_types_supported _ generated_mixed_owner_preparation

theorem generated_aliases (horizon : Nat) :
    (readJointAlias true 0 horizon).run inventoryAliasAfter = (.ok inventoryNewString,inventoryAliasAfter) ∧
    (readJointAlias false 1 horizon).run inventoryAliasAfter = (.ok inventoryNewString,inventoryAliasAfter) := ⟨(inventory_actual_alias_reads horizon).1,(inventory_actual_alias_reads horizon).2.1⟩

theorem generated_retained_zero : enumeratedMemoryWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) inventoryZeroPhysical =
    .ok (some (.ok (),inventoryZeroAfter)) := by
  unfold enumeratedMemoryWriteback
  rw [generated_mixed_prepared]
  exact congrArg Except.ok inventory_zero_source

theorem generated_retained_current_prepares : unsupportedHeapCells inventoryZeroRealized.placement = [] := by decide

end Solidity.Yul.Views.Controls
