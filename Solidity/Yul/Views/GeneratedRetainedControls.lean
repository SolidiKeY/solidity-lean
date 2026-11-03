import Solidity.Yul.Views.HeapEnumerationBoundaryControls
import Solidity.Yul.Views.InventorySourceReads

namespace Solidity.Yul.Views.Controls

def generatedSparseState : Source.EMState mixedEnv [.bytes .memory,.string .memory] :=
  ⟨.cons (.memRef rfl 2) (.cons (.memRef rfl 2) .nil),
    ⟨mixedState.2.ex,enumerationSparseHeap,[],[],⟨[],.nil⟩⟩⟩

theorem generated_sparse_MemOK : Source.MemOK mixedEnv enumerationSparseHeap.ty generatedSparseState := by
  obtain ⟨heap,top,inner⟩ := mixedHeap_owner_invariants enumerationSparsePlacement (generatedHeapEntries enumerationSparsePlacement) enumeration_sparse_coverage
  exact ⟨⟨⟨heap,Source.HeapTy.Le.refl _⟩,⟨⟨.bytes .memory,rfl,rfl⟩,⟨⟨.bytes .memory,rfl,rfl⟩,trivial⟩⟩⟩,top,inner⟩

def generatedSparsePhysical := encodeMixedHeap enumerationSparsePlacement (generatedHeapEntries enumerationSparsePlacement) mixedResidual
def generatedSparseZero := mstore generatedSparsePhysical 256 0

theorem generated_sparse_zero_decode : (decodeInventoryUpdates enumerationSparsePlacement enumerationSparsePlacement
    (generatedHeapEntries enumerationSparsePlacement) (generatedHeapEntries enumerationSparsePlacement) generatedSparseZero).isSome := by decide

def generatedSparseZeroUpdates := (decodeInventoryUpdates enumerationSparsePlacement enumerationSparsePlacement
  (generatedHeapEntries enumerationSparsePlacement) (generatedHeapEntries enumerationSparsePlacement) generatedSparseZero).get generated_sparse_zero_decode

def generatedSparseZeroRealized := realizeInventory enumerationSparsePlacement enumerationSparsePlacement (retainInitial _ _) generatedSparseZeroUpdates
  enumerationSparseHeap enumerationSparsePlacement (retainInitial _ _) rfl (generatedHeapEntries enumerationSparsePlacement)
def generatedSparseZeroState := withSourceHeap generatedSparseState generatedSparseZeroRealized.heap

theorem generated_sparse_zero_step : enumeratedMemoryWriteback generatedSparseState enumerationSparsePlacement enumerationSparsePlacement (retainInitial _ _) generatedSparseZero =
    .ok (some (.ok (),generatedSparseZeroState)) := by
  unfold enumeratedMemoryWriteback prepareHeapInventory
  rw [enumeration_sparse_exact.2.1]
  change Except.ok (inventoryStateWriteback generatedSparseState _ _ _ _ _) = _
  unfold inventoryStateWriteback
  rw [← Option.some_get generated_sparse_zero_decode,Option.map_some]
  exact congrArg (fun r => Except.ok (some r)) (realizeInventory_run _ _ _ generatedSparseZeroUpdates generatedSparseState _ _ rfl _)

theorem generated_sparse_zero_owner : Source.MemOK mixedEnv enumerationSparseHeap.ty generatedSparseZeroState :=
  enumeratedMemoryWriteback_MemOK _ _ _ _ _ _ _ generated_sparse_zero_step generated_sparse_MemOK

def generatedSparseRegrowPhysical := mstore generatedSparseZero 256 4

theorem generated_sparse_current_prepares : unsupportedHeapCells generatedSparseZeroRealized.placement = [] := by decide

theorem generated_sparse_regrow_decodes : (decodeInventoryUpdates enumerationSparsePlacement generatedSparseZeroRealized.placement
    (generatedHeapEntries generatedSparseZeroRealized.placement) (generatedHeapEntries generatedSparseZeroRealized.placement) generatedSparseRegrowPhysical).isSome := by decide

def generatedSparseRegrowUpdates := (decodeInventoryUpdates enumerationSparsePlacement generatedSparseZeroRealized.placement
  (generatedHeapEntries generatedSparseZeroRealized.placement) (generatedHeapEntries generatedSparseZeroRealized.placement) generatedSparseRegrowPhysical).get generated_sparse_regrow_decodes

def generatedSparseRegrown := realizeInventory enumerationSparsePlacement generatedSparseZeroRealized.placement generatedSparseZeroRealized.history generatedSparseRegrowUpdates
  generatedSparseZeroRealized.heap generatedSparseZeroRealized.placement generatedSparseZeroRealized.history rfl (generatedHeapEntries generatedSparseZeroRealized.placement)
def generatedSparseRegrownState := withSourceHeap generatedSparseZeroState generatedSparseRegrown.heap

theorem generated_sparse_regrow_step : enumeratedMemoryWriteback generatedSparseZeroState enumerationSparsePlacement generatedSparseZeroRealized.placement generatedSparseZeroRealized.history generatedSparseRegrowPhysical =
    .ok (some (.ok (),generatedSparseRegrownState)) := by
  unfold enumeratedMemoryWriteback prepareHeapInventory
  rw [generated_sparse_current_prepares]
  change Except.ok (inventoryStateWriteback generatedSparseZeroState _ _ _ _ _) = _
  unfold inventoryStateWriteback
  rw [← Option.some_get generated_sparse_regrow_decodes,Option.map_some]
  exact congrArg (fun r => Except.ok (some r)) (realizeInventory_run _ _ _ generatedSparseRegrowUpdates generatedSparseZeroState _ _ rfl _)

theorem generated_sparse_regrow_all_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H generatedSparseState) : Source.MemOK mixedEnv H generatedSparseRegrownState :=
  enumeratedMemoryWriteback_MemOK H _ _ _ _ _ _ generated_sparse_regrow_step
    (enumeratedMemoryWriteback_MemOK H _ _ _ _ _ _ generated_sparse_zero_step ok)

theorem generated_sparse_regrow_inhabited : Source.MemOK mixedEnv enumerationSparseHeap.ty generatedSparseRegrownState := generated_sparse_regrow_all_H _ generated_sparse_MemOK

theorem generated_sparse_retained_shapes : generatedSparseZeroRealized.placement.shape 2 = .bytes 0 ∧
    generatedSparseRegrown.placement.shape 2 = .bytes 4 ∧ RetainedAllocation enumerationSparsePlacement generatedSparseRegrown.placement := ⟨rfl,rfl,generatedSparseRegrown.history⟩

def generatedSparseRegrownBytes : List UInt8 := [0x11,0x22,0x33,0xa5]

theorem generated_sparse_regrow_data : generatedSparseRegrown.heap.get 2 = some ⟨.bytes .memory,.bytes generatedSparseRegrownBytes⟩ := by
  have symbolic : generatedSparseRegrown.heap.get 2 = some ⟨.bytes .memory,.bytes (readBytes generatedSparseRegrowPhysical 288 4)⟩ := rfl
  rw [show readBytes generatedSparseRegrowPhysical 288 4 = generatedSparseRegrownBytes from by decide] at symbolic
  exact symbolic

theorem generated_sparse_aliases (horizon : Nat) :
    (Source.bytesOfRV (E := mixedEnv) mixedReadFrame horizon (.val (generatedSparseRegrownState.1.get .here))).run generatedSparseRegrownState = (.ok generatedSparseRegrownBytes,generatedSparseRegrownState) ∧
    (Source.bytesOfRV (E := mixedEnv) mixedReadFrame horizon (.val (generatedSparseRegrownState.1.get (.there .here)))).run generatedSparseRegrownState = (.ok generatedSparseRegrownBytes,generatedSparseRegrownState) := by
  constructor
  · change (Source.heapBytes (E := mixedEnv) 2).run generatedSparseRegrownState = _
    exact heapBytes_known generatedSparseRegrownState 2 _ (Or.inr generated_sparse_regrow_data)
  · change (Source.heapBytes (E := mixedEnv) 2).run generatedSparseRegrownState = _
    exact heapBytes_known generatedSparseRegrownState 2 _ (Or.inr generated_sparse_regrow_data)

end Solidity.Yul.Views.Controls
