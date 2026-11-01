import Solidity.Yul.Views.AllocatedMemory
import Solidity.Yul.Views.HeapEnumerationControls
import Solidity.Yul.Views.HeapEnumerationBoundaryControls
import Solidity.Yul.Views.RetainedAllocationFurtherControls

namespace Solidity.Yul.Views.Controls

def aiBytes : List UInt8 := [0xfe,0,0xfd,0xfc]
def aiState := byteAllocatedState mixedState true aiBytes
def aiPlacement := byteAllocPlacement mixedHeap mixedPlacement true aiBytes 1665 1729
  (by decide) (heap_later_fresh mixedHeap mixedPlacement 1665 (by decide)) (by decide)

theorem ai_actual_inventory : prepareHeapInventory aiPlacement=.ok (generatedHeapEntries aiPlacement) ∧
    CoversMixedHeap (generatedHeapEntries aiPlacement) ∧
    ((generatedHeapEntries aiPlacement).map MixedHeapEntry.id).Nodup ∧
    (generatedHeapEntries aiPlacement).map MixedHeapEntry.id=[0,1,2,3,4,5,6] := by
  have facts := byteAllocated_inventory mixedHeap.ty mixedState mixedPlacement true aiBytes aiPlacement
    mixed_actual_MemOK generated_mixed_types_supported
  exact ⟨facts.1,facts.2.1,facts.2.2.1,by rw [facts.2.2.2,generated_mixed_ids]; rfl⟩

theorem ai_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H aiState :=
  byteAllocRef_MemOK mixedState true aiBytes H ok

theorem ai_unchanged_whole_state :
    enumeratedMemoryWriteback aiState aiPlacement aiPlacement (retainInitial _ _)
      (encodeMixedHeap aiPlacement (generatedHeapEntries aiPlacement) mixedResidual)=.ok (some (.ok (),aiState)) := by
  exact enumeratedMemory_unchanged aiState aiPlacement aiPlacement (retainInitial _ _) mixedResidual
    (heapAlloc_inventory_supported mixedHeap (heapByteData mixedLayout true aiBytes) trivial generated_mixed_types_supported)
    _ ai_actual_inventory.1

/-- Sparse holes are NOT allocated objects and are not silently filled. -/
def aiSparsePlacement := byteAllocPlacement enumerationSparseHeap enumerationSparsePlacement false aiBytes
  513 577 (by decide) (heap_later_fresh _ _ 513 (by decide)) (by decide)

theorem ai_sparse_exact : (generatedHeapEntries aiSparsePlacement).map MixedHeapEntry.id=[2,5] ∧
    missingHeapCells aiSparsePlacement=[0,1,3,4] ∧ unsupportedHeapCells aiSparsePlacement=[] := by decide

/-- Allocating a valid new object cannot hide a preexisting dangling reference.
This does not postulate MemOK for the malformed source heap. -/
def aiDanglingPlacement := byteAllocPlacement enumerationDanglingHeap enumerationDanglingPlacement false aiBytes
  513 577 (by decide) (heap_later_fresh _ _ 513 (by decide)) (by decide)

theorem ai_dangling_still_error : prepareHeapInventory aiDanglingPlacement=.error [2] ∧
    (generatedHeapEntries aiDanglingPlacement).map MixedHeapEntry.id=[5] := by
  have bad : unsupportedHeapCells aiDanglingPlacement=[2] := by decide
  constructor
  · unfold prepareHeapInventory; rw [bad]
  · decide

theorem ai_byte_heap_support (a : Nat) (τ : Source.STy) (d : Source.Data heapByteEnv.layout τ)
    (found : byteHeap.get a=some ⟨τ,d⟩) : InventoryTypeSupported heapByteEnv τ := by
  cases a with
  | zero =>
    change some (⟨.bytes .memory,.bytes byteOld⟩ : Sigma (Source.Data heapByteEnv.layout))=some ⟨τ,d⟩ at found
    cases found; trivial
  | succ a =>
    cases a with
    | zero =>
      change some (⟨.string .memory,.string stringOld⟩ : Sigma (Source.Data heapByteEnv.layout))=some ⟨τ,d⟩ at found
      cases found; trivial
    | succ a =>
      cases a with
      | zero =>
        change some (⟨.bytes .memory,.bytes byteOther⟩ : Sigma (Source.Data heapByteEnv.layout))=some ⟨τ,d⟩ at found
        cases found; trivial
      | succ a =>
        have empty := byteHeap.bounded (a+3) (by change 3≤a+3; omega)
        change byteHeap.cells (a+3)=some ⟨τ,d⟩ at found
        rw [empty] at found
        cases found

theorem ai_empty_support : ∀ a τ d, emptyState.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported heapByteEnv τ :=
  heapWrite_inventory_supported byteHeap 0 (Source.Data.bytes []) (by rfl) ai_byte_heap_support

theorem ai_retained_end_to_end :
    enumeratedMemoryView alPlacement alPhysical=.ok (encodeMixedHeap alPlacement (generatedHeapEntries alPlacement) alPhysical) ∧
    enumeratedMemoryWriteback alState alOriginalPlacement alPlacement alHistory
      (encodeMixedHeap alPlacement (generatedHeapEntries alPlacement) alPhysical)=.ok (some (.ok (),alState)) := by
  have linked := retainedByteAllocation_inventory byteHeap.ty emptyState (bytePlacement 0)
    retainedEmptyPlacement retainedEmpty true alBytes 512 576 (by decide) ha_fresh (by decide) alPhysical
    actual_resize_MemOK.2.2 ai_empty_support
  exact linked.2.2.2.2.2.2

theorem ai_retained_ids_and_extent : (generatedHeapEntries alPlacement).map MixedHeapEntry.id=[0,1,2,3] ∧
    alPlacement.shape 0=.bytes 0 ∧ (alOriginalPlacement.shape 0).size=64 := by decide

theorem ai_al_support : ∀ a τ d, alState.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported heapByteEnv τ :=
  heapAlloc_inventory_supported emptyState.2.heap (heapByteData heapByteEnv.layout true alBytes) trivial ai_empty_support

theorem ai_twice_support : ∀ a τ d, alTwiceState.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported heapByteEnv τ :=
  heapAlloc_inventory_supported alNewZeroState.2.heap (heapByteData heapByteEnv.layout false alNextBytes) trivial
    (heapWrite_inventory_supported alGrowHeap 3 (Source.Data.string []) (by rfl)
      (heapWrite_inventory_supported alState.2.heap 0 (Source.Data.bytes growBytes) (by rfl) ai_al_support))

theorem ai_twice_unchanged :
    enumeratedMemoryWriteback alTwiceState alTwiceOriginalPlacement alTwicePlacement alTwiceHistory
      (encodeMixedHeap alTwicePlacement (generatedHeapEntries alTwicePlacement) alTwicePhysical)=
        .ok (some (.ok (),alTwiceState)) :=
  (ownerMemory_unchanged byteHeap.ty alTwiceState alTwiceOriginalPlacement alTwicePlacement alTwiceHistory
    alTwicePhysical al_twice_MemOK ai_twice_support).2

theorem ai_twice_ids_and_capacities :
    (generatedHeapEntries alTwicePlacement).map MixedHeapEntry.id=[0,1,2,3,4] ∧
      (alTwiceOriginalPlacement.shape 0).size=64 ∧ (alTwiceOriginalPlacement.shape 3).size=64 ∧
      alTwicePlacement.shape 3=.bytes 0 := by decide

/-- The computed whole inventory keeps the physical allocation's real reserved
words and retained tails; it does not infer arbitrary residual initialization. -/
def aiRetainedView := encodeMixedHeap alPlacement (generatedHeapEntries alPlacement) alPhysical
def aiTwiceView := encodeMixedHeap alTwicePlacement (generatedHeapEntries alTwicePlacement) alTwicePhysical

theorem ai_retained_reserved_tail : (mload aiRetainedView 64).val=576 ∧ mload aiRetainedView 96=0 ∧
    mload aiRetainedView 128=0 ∧ mload aiRetainedView 512=4 ∧
    readBytes aiRetainedView 160 4=[0x11,0x22,0x33,0xa5] ∧
    readBytes aiRetainedView 544 5=[0xfe,0,0xfd,0xfc,0xa5] := by decide

theorem ai_twice_reserved_tail : (mload aiTwiceView 64).val=641 ∧ mload aiTwiceView 96=0 ∧
    mload aiTwiceView 128=4 ∧ mload aiTwiceView 512=0 ∧ mload aiTwiceView 577=2 ∧
    readBytes aiTwiceView 544 5=[0xfe,0,0xfd,0xfc,0xa5] ∧
    readBytes aiTwiceView 576 1=[0xa5] ∧ readBytes aiTwiceView 609 3=[9,8,0xa5] := by decide

theorem ai_wrong_inventory_and_holes : (generatedHeapEntries aiPlacement).map MixedHeapEntry.id≠[0,1,2,3,4,5] ∧
    (generatedHeapEntries aiSparsePlacement).map MixedHeapEntry.id≠[0,1,2,3,4,5] ∧
    (generatedHeapEntries alTwicePlacement).map MixedHeapEntry.id≠[0,1,2,4] := by decide

end Solidity.Yul.Views.Controls
