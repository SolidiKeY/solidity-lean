import Solidity.Yul.Views.AbiUintArrayWords
import Solidity.Yul.Views.ObjectAllocationRetainedControls

namespace Solidity.Yul.Views.Controls

def adInput : Roadmap.Bytes := Source.wordBytes 32++Source.wordBytes 3++
  Source.wordBytes 7++Source.wordBytes omMaxWord++Source.wordBytes 77

def adData := abiUintArrayData mixedLayout (abiArrayPayload adInput 0) (abiArrayLength adInput 0)
def adShape := abiUintArrayShape mixedLayout adInput 0

theorem ad_input_length : adInput.length=160 := by
  simp only [adInput,List.length_append,Source.wordBytes_length]

theorem ad_offset : abiArrayOffset adInput 0=32 := by decide
theorem ad_length : abiArrayLength adInput 0=3 := by
  unfold abiArrayLength
  rw [ad_offset]
  decide

theorem ad_header : abiArrayOffset adInput 0+32≤adInput.length := by rw [ad_offset,ad_input_length]; decide
theorem ad_small : abiArrayLength adInput 0<2^64 := by rw [ad_length]; decide
theorem ad_payload : abiArrayOffset adInput 0+32+32*abiArrayLength adInput 0≤adInput.length := by
  rw [ad_offset,ad_length,ad_input_length]
  decide

theorem ad_count : (abiUintValues mixedLayout (abiArrayPayload adInput 0) (abiArrayLength adInput 0)).length=3 := by
  rw [abiUintValues_length,ad_length]

def adState := objectAllocatedState mixedState adData
def adPlacement := heapAllocPlacement mixedHeap mixedPlacement adData adShape (abiUintArrayData_shape _ _ _)
  1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)

theorem ad_source : (Source.decodeArg adInput 0 (.array .memory (.int Source.IntTy.u256) none)).run mixedState=
    (.ok (Source.Val.memRef rfl 6),adState) := abiUintArray_run mixedState adInput 0 ad_header ad_small ad_payload

theorem ad_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H adState :=
  abiUintArray_alloc_MemOK H mixedState adInput 0 ok

theorem ad_ready : (objectAllocationView mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical).isSome :=
  objectAllocationView_complete mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical
    (Or.inr True.intro) (abiUintArrayData_inner (E := mixedEnv) _ _) (abiUintArrayData_valid mixedEnv mixedHeap.ty _ _)

def adRaw := (objectAllocationView mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
  1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical).get ad_ready

theorem ad_step : objectAllocationView mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical=some adRaw :=
  (Option.some_get ad_ready).symm

theorem ad_physical_writeback : enumeratedMemoryWriteback adState adPlacement adPlacement (retainInitial _ _) adRaw=
    .ok (some (.ok (),adState)) := by
  obtain ⟨raw,step,run,safe,ready,covers,distinct,same,source,spare⟩ := abiUintArray_physical mixedHeap.ty mixedState
    mixedPlacement mixedPlacement (retainInitial _ _) adInput 0 ad_header ad_small ad_payload 1665 1793
    (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical mixed_actual_MemOK
    generated_mixed_types_supported av_mixed_reads mixed_reserved
  have eq := Option.some.inj (step.symm.trans ad_step)
  subst raw
  exact source

theorem ad_whole_map : encodeMixedHeap adPlacement (generatedHeapEntries adPlacement) adRaw=adRaw :=
  (objectAllocationView_computed mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared
    mixedPhysical adRaw av_mixed_reads ad_step).2.2.2

theorem ad_header_word : mload adRaw 1665=3 := by
  have read := abiUintArray_header_word mixedLayout adPlacement.address (abiArrayPayload adInput 0)
    (abiArrayLength adInput 0) (abi_wordAt_bound _ _)
  exact objectAllocationView_source_word mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared mixedPhysical
    adRaw av_mixed_reads ad_step 6 _ adData (Source.Heap.alloc_get mixedHeap _) 0 3 read

theorem ad_first_word : mload adRaw 1697=7 :=
  objectAllocationView_source_word mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared mixedPhysical
    adRaw av_mixed_reads ad_step 6 _ adData (Source.Heap.alloc_get mixedHeap _) 32 7
    (abiUintArray_element_word mixedLayout adPlacement.address (abiArrayPayload adInput 0) (abiArrayLength adInput 0) ⟨0,by decide⟩)

theorem ad_last_word : mload adRaw 1761=77 :=
  objectAllocationView_source_word mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared mixedPhysical
    adRaw av_mixed_reads ad_step 6 _ adData (Source.Heap.alloc_get mixedHeap _) 96 77
    (abiUintArray_element_word mixedLayout adPlacement.address (abiArrayPayload adInput 0) (abiArrayLength adInput 0) ⟨2,by decide⟩)

theorem ad_MAX_word : mload adRaw 1729=omMaxWord :=
  objectAllocationView_source_word mixedHeap mixedPlacement adData rfl adShape (abiUintArrayData_shape _ _ _)
    1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared mixedPhysical
    adRaw av_mixed_reads ad_step 6 _ adData (Source.Heap.alloc_get mixedHeap _) 64 omMaxWord
    (abiUintArray_element_word mixedLayout adPlacement.address (abiArrayPayload adInput 0) (abiArrayLength adInput 0) ⟨1,by decide⟩)

theorem ad_reserved : ReservedOK adRaw 1793 := objectAllocationView_reserved mixedHeap mixedPlacement adData rfl adShape
  (abiUintArrayData_shape _ _ _) 1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)
  mixedPhysical adRaw mixed_reserved ad_step

theorem ad_gap_tail : adRaw 1664=mixedPhysical 1664 ∧ adRaw 1793=mixedPhysical 1793 := by
  obtain ⟨image,ready,span,encoded,outside⟩ := objectAllocationView_region mixedHeap mixedPlacement adData rfl adShape
    (abiUintArrayData_shape _ _ _) 1665 1793 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)
    mixedPhysical adRaw ad_step
  exact ⟨outside 1664 (Or.inl (by decide)) (Or.inr (by decide)),outside 1793 (Or.inr (by
    have size : adShape.size≤128 := by decide
    have tight := Nat.le_trans span size
    exact Nat.add_le_add_left tight 1665)) (Or.inr (by decide))⟩

end Solidity.Yul.Views.Controls
