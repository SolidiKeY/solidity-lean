import Solidity.Yul.Views.AllocatedObjectMemory
import Solidity.Yul.Views.AllocationPhysicalControls

namespace Solidity.Yul.Views.Controls

def omStructState := objectAllocatedState mixedState mixedStruct
def omStructPlacement := heapAllocPlacement mixedHeap mixedPlacement mixedStruct (.strct 5) (.strct _)
  1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)

theorem om_struct_valid : Source.DataOK mixedEnv mixedHeap.ty mixedStruct :=
  mixed_actual_MemOK.1.1.heap 3 ⟨_,mixedStruct⟩ rfl

theorem om_struct_inner : Source.Data.Inner (E := mixedEnv) mixedStruct :=
  mixed_actual_MemOK.2.2 3 ⟨_,mixedStruct⟩ rfl

theorem om_struct_support : InventoryTypeSupported mixedEnv (.struct .memory mixedName) :=
  generated_mixed_types_supported 3 _ mixedStruct rfl

theorem om_struct_ready : (objectAllocationView mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical).isSome :=
  objectAllocationView_complete mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical
    om_struct_support om_struct_inner om_struct_valid

def omStructRaw := (objectAllocationView mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
  1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical).get om_struct_ready

theorem om_struct_step : objectAllocationView mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical=some omStructRaw :=
  (Option.some_get om_struct_ready).symm

theorem om_struct_source : (Source.allocRef mixedStruct).run mixedState=
    (.ok (Source.Val.memRef rfl 6),omStructState) := objectAllocRef_run mixedState mixedStruct rfl

theorem om_struct_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H omStructState :=
  (objectAllocRef_MemOK H mixedState mixedStruct rfl trivial om_struct_inner om_struct_valid ok).1

theorem om_struct_full_map : encodeMixedHeap omStructPlacement (generatedHeapEntries omStructPlacement) omStructRaw=omStructRaw :=
  (objectAllocationView_computed mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared
    mixedPhysical omStructRaw av_mixed_reads om_struct_step).2.2.2

theorem om_struct_writeback : enumeratedMemoryWriteback omStructState omStructPlacement omStructPlacement (retainInitial _ _) omStructRaw=
    .ok (some (.ok (),omStructState)) := by
  obtain ⟨raw,step,run,safe,ready,covers,distinct,same,source,reserved⟩ := retainedObjectAllocation_physical mixedHeap.ty mixedState
    mixedPlacement mixedPlacement (retainInitial _ _) mixedStruct rfl (.strct 5) (.strct _) om_struct_inner om_struct_valid
    om_struct_support 1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical
    mixed_actual_MemOK generated_mixed_types_supported av_mixed_reads mixed_reserved
  have eq := Option.some.inj (step.symm.trans om_struct_step)
  subst raw
  exact source

theorem om_struct_reserved : ReservedOK omStructRaw 1825 :=
  objectAllocationView_reserved mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical omStructRaw mixed_reserved om_struct_step

def omArrayTy : Source.STy := .array .memory (.struct .memory mixedName) none
def omArrayData : Source.Data mixedLayout omArrayTy := .array 2 (fun _ e => nomatch e) (fun _ => .val (.memRef rfl 6))
def omArrayState := objectAllocatedState omStructState omArrayData
def omArrayPlacement := heapAllocPlacement omStructState.2.heap omStructPlacement omArrayData (.array true 2) (.array 2 _ _)
  1826 1922 (by decide) (heap_later_fresh _ _ 1826 (by decide)) (by decide)

theorem om_array_valid : Source.DataOK mixedEnv omStructState.2.heap.ty omArrayData :=
  .array (fun _ => .val ⟨.struct .memory mixedName,rfl,rfl⟩)

theorem om_array_inner : Source.Data.Inner (E := mixedEnv) omArrayData := fun _ => ⟨.memRef rfl 6,rfl⟩
theorem om_array_support : InventoryTypeSupported mixedEnv omArrayTy := Or.inl (Or.inr (Or.inr rfl))
theorem om_struct_heap_support : ∀ a τ d, omStructState.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported mixedEnv τ :=
  heapAlloc_inventory_supported mixedHeap mixedStruct om_struct_support generated_mixed_types_supported

theorem om_array_ready : (objectAllocationView omStructState.2.heap omStructPlacement omArrayData rfl (.array true 2) (.array 2 _ _)
    1826 1922 (by decide) (heap_later_fresh _ _ 1826 (by decide)) (by decide) omStructRaw).isSome :=
  objectAllocationView_complete _ _ _ rfl _ (.array 2 _ _) 1826 1922 (by decide)
    (heap_later_fresh _ _ 1826 (by decide)) (by decide) omStructRaw om_array_support om_array_inner om_array_valid

def omArrayRaw := (objectAllocationView omStructState.2.heap omStructPlacement omArrayData rfl (.array true 2) (.array 2 _ _)
  1826 1922 (by decide) (heap_later_fresh _ _ 1826 (by decide)) (by decide) omStructRaw).get om_array_ready

theorem om_array_step : objectAllocationView omStructState.2.heap omStructPlacement omArrayData rfl (.array true 2) (.array 2 _ _)
    1826 1922 (by decide) (heap_later_fresh _ _ 1826 (by decide)) (by decide) omStructRaw=some omArrayRaw :=
  (Option.some_get om_array_ready).symm

theorem om_array_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H omArrayState :=
  (objectAllocRef_MemOK H omStructState omArrayData rfl trivial om_array_inner om_array_valid (om_struct_every_H H ok)).1

theorem om_array_full_map_state_reserved : encodeMixedHeap omArrayPlacement (generatedHeapEntries omArrayPlacement) omArrayRaw=omArrayRaw ∧
    enumeratedMemoryWriteback omArrayState omArrayPlacement omArrayPlacement (retainInitial _ _) omArrayRaw=
      .ok (some (.ok (),omArrayState)) ∧ ReservedOK omArrayRaw 1922 := by
  have before := ownerMemOK_prepares_inventory mixedHeap.ty omStructState omStructPlacement
    (om_struct_every_H _ mixed_actual_MemOK) om_struct_heap_support
  have reads := objectAllocationView_image_reads mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared
    mixedPhysical omStructRaw av_mixed_reads om_struct_step
  obtain ⟨raw,step,run,safe,ready,covers,distinct,same,source,reserved⟩ := retainedObjectAllocation_physical mixedHeap.ty omStructState
    omStructPlacement omStructPlacement (retainInitial _ _) omArrayData rfl (.array true 2) (.array 2 _ _) om_array_inner om_array_valid
    om_array_support 1826 1922 (by decide) (heap_later_fresh _ _ 1826 (by decide)) (by decide) omStructRaw
    (om_struct_every_H _ mixed_actual_MemOK) om_struct_heap_support (fun e _ => reads e) om_struct_reserved
  have eq := Option.some.inj (step.symm.trans om_array_step)
  subst raw
  exact ⟨same,source,reserved⟩

theorem om_struct_raw_reads (e : MixedHeapEntry omStructPlacement) : e.image.Reads omStructRaw (omStructPlacement.address e.id) :=
  objectAllocationView_image_reads mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared
    mixedPhysical omStructRaw av_mixed_reads om_struct_step e

theorem om_array_observer (off : Nat) (w : Roadmap.Word) (read : ObjectWord omArrayPlacement.address omArrayData off w) :
    mload omArrayRaw (1826+off)=w :=
  objectAllocationView_source_word omStructState.2.heap omStructPlacement omArrayData rfl (.array true 2) (.array 2 _ _)
    1826 1922 (by decide) (heap_later_fresh _ _ 1826 (by decide)) (by decide) _
    (ownerMemOK_prepares_inventory mixedHeap.ty omStructState omStructPlacement (om_struct_every_H _ mixed_actual_MemOK) om_struct_heap_support)
    omStructRaw omArrayRaw (fun e _ => om_struct_raw_reads e) om_array_step 7 omArrayTy omArrayData rfl off w read

theorem om_struct_residual (i : Nat) (outside : i<1665 ∨ 1825≤i) (notFree : i<64 ∨ 96≤i) : omStructRaw i=mixedPhysical i := by
  obtain ⟨image,ready,bound,same,keep⟩ := objectAllocationView_region mixedHeap mixedPlacement mixedStruct rfl (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical omStructRaw om_struct_step
  have span : image.span≤160 := bound
  exact keep i (by omega) notFree

theorem om_array_residual (i : Nat) (outside : i<1826 ∨ 1922≤i) (notFree : i<64 ∨ 96≤i) : omArrayRaw i=omStructRaw i := by
  obtain ⟨image,ready,bound,same,keep⟩ := objectAllocationView_region omStructState.2.heap omStructPlacement omArrayData rfl
    (.array true 2) (.array 2 _ _) 1826 1922 (by decide) (heap_later_fresh _ _ 1826 (by decide)) (by decide)
    omStructRaw omArrayRaw om_array_step
  have span : image.span≤96 := bound
  exact keep i (by omega) notFree

theorem om_exact_pointer_words : mload omStructRaw 1665=1 ∧ mload omStructRaw 1697=7 ∧ mload omStructRaw 1729=128 ∧
    mload omStructRaw 1761=128 ∧ mload omStructRaw 1793=1152 ∧
    mload omArrayRaw 1826=2 ∧ mload omArrayRaw 1858=1665 ∧ mload omArrayRaw 1890=1665 ∧
    mload omArrayRaw 64=1922 ∧ mload omArrayRaw 96=0 ∧ omArrayRaw 163=0xa5 ∧ omArrayRaw 1825=0xa5 := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,?_,?_,?_,?_,?_,?_,?_⟩
  · exact om_array_observer 0 2 (.arrayLength 2 (by decide) _ _)
  · exact om_array_observer 32 1665 (.arrayElement 2 _ _ ⟨0,by decide⟩ (.memRef rfl 6) _ rfl (.reference rfl 6 (by decide)))
  · exact om_array_observer 64 1665 (.arrayElement 2 _ _ ⟨1,by decide⟩ (.memRef rfl 6) _ rfl (.reference rfl 6 (by decide)))
  · exact Fin.ext om_array_full_map_state_reserved.2.2.1
  · have eq := mload_congr omArrayRaw (fun _ => 0) 96 om_array_full_map_state_reserved.2.2.2
    exact eq.trans (by decide)
  · rw [om_array_residual 163 (Or.inl (by decide)) (Or.inr (by decide)),om_struct_residual 163 (Or.inl (by decide)) (Or.inr (by decide))]
    decide
  · rw [om_array_residual 1825 (Or.inl (by decide)) (Or.inr (by decide)),om_struct_residual 1825 (Or.inr (by decide)) (Or.inr (by decide))]
    decide

theorem om_source_array_alias (i : Fin 2) :
    (Source.readLoc mixedReadFrame (τ := .struct .memory mixedName) (.mem 7 i.val)).run omArrayState=
      (.ok (Source.Val.memRef rfl 6),omArrayState) :=
  readLoc_array_known omArrayState mixedReadFrame 7 i.val 2 (.struct .memory mixedName) (fun _ => .memRef rfl 6) rfl i.isLt

theorem om_source_struct_alias (j : Fin 2) :
    (Source.readLoc mixedReadFrame (τ := .bytes .memory) (.mem 6 (2+j.val))).run omArrayState=
      (.ok (Source.Val.memRef rfl 0),omArrayState) := by
  apply readLoc_struct_known omArrayState mixedReadFrame 6 (2+j.val) mixedName mixedFields (.bytes .memory) (.memRef rfl 0) rfl
  have choices : j.val=0 ∨ j.val=1 := by have bound := j.isLt; omega
  rcases choices with same | same <;> rw [same] <;> rfl

end Solidity.Yul.Views.Controls
