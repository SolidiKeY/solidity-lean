import Solidity.Yul.Views.ObjectAllocationBoundaryControls

namespace Solidity.Yul.Views.Controls

def omShrunkState := withSourceHeap mixedState (mixedHeap.write 0 (Source.Data.bytes []) (by rfl))
def omShrunkPlacement := retainedWritePlacement mixedPlacement mixedPlacement (retainInitial _ _)
  0 (Source.Data.bytes []) (by rfl) (.bytes 0) (.bytes _) (by decide)
def omShrunkHistory : RetainedAllocation mixedPlacement omShrunkPlacement :=
  retainWritten mixedPlacement mixedPlacement (retainInitial _ _) 0 (Source.Data.bytes []) (by rfl) (.bytes 0) (.bytes _) (by decide)
def omShrunkRaw := encodeMixedHeap omShrunkPlacement (generatedHeapEntries omShrunkPlacement) (mstore mixedPhysical 128 0)
def omRetainedPlacement := retainedAllocationPlacement mixedPlacement omShrunkPlacement omShrunkHistory mixedStruct (.strct 5) (.strct _)
  1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)
def omRetainedOrigin := heapAllocPlacement mixedHeap mixedPlacement mixedStruct (.strct 5) (.strct _)
  1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)
def omRetainedHistory : RetainedAllocation omRetainedOrigin omRetainedPlacement :=
  retainAllocated mixedPlacement omShrunkPlacement omShrunkHistory mixedStruct (.strct 5) (.strct _)
    1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)

theorem om_shrunk_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H omShrunkState :=
  heapByte_write_MemOK mixedEnv H mixedState 0 false [] (by rfl) ok

theorem om_shrunk_support : ∀ a τ d, omShrunkState.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported mixedEnv τ :=
  heapWrite_inventory_supported mixedHeap 0 (Source.Data.bytes []) (by rfl) generated_mixed_types_supported

theorem om_shrunk_struct_valid : Source.DataOK mixedEnv omShrunkState.2.heap.ty mixedStruct := by
  have types : omShrunkState.2.heap.ty=mixedHeap.ty := funext (fun a => Source.Heap.write_ty _ 0 a (Source.Data.bytes []) (by rfl))
  rw [types]
  exact om_struct_valid

theorem om_shrunk_reserved : ReservedOK omShrunkRaw 1664 :=
  encodeMixedHeap_reserved _ _ _ (mstore_object_header_reserved mixedPhysical 128 0 1664 (by decide) mixed_reserved)

theorem om_prior_write_allocation : ∃ raw,
    objectAllocationView omShrunkState.2.heap omShrunkPlacement mixedStruct rfl (.strct 5) (.strct _)
      1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) omShrunkRaw=some raw ∧
    encodeMixedHeap omRetainedPlacement (generatedHeapEntries omRetainedPlacement) raw=raw ∧
    enumeratedMemoryWriteback (objectAllocatedState omShrunkState mixedStruct) omRetainedOrigin omRetainedPlacement omRetainedHistory raw=
      .ok (some (.ok (),objectAllocatedState omShrunkState mixedStruct)) ∧ ReservedOK raw 1825 := by
  have prepared := ownerMemOK_prepares_inventory mixedHeap.ty omShrunkState omShrunkPlacement
    (om_shrunk_every_H _ mixed_actual_MemOK) om_shrunk_support
  have facts := prepareHeapInventory_ok omShrunkPlacement _ prepared
  obtain ⟨raw,step,run,safe,ready,covers,distinct,same,source,reserved⟩ := retainedObjectAllocation_physical mixedHeap.ty omShrunkState
    mixedPlacement omShrunkPlacement omShrunkHistory mixedStruct rfl (.strct 5) (.strct _) om_struct_inner om_shrunk_struct_valid
    om_struct_support 1665 1825 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) omShrunkRaw
    (om_shrunk_every_H _ mixed_actual_MemOK) om_shrunk_support (encodeMixedHeap_reads _ _ facts.2.2 _) om_shrunk_reserved
  exact ⟨raw,step,same,source,reserved⟩

theorem om_prior_write_capacity : omRetainedPlacement.shape 0=.bytes 0 ∧
    (omRetainedOrigin.shape 0).size=64 ∧ omRetainedPlacement.address 0=128 ∧
    omRetainedPlacement.address 6=1665 := ⟨rfl,rfl,rfl,rfl⟩

def omMax : Source.Val mixedLayout (.int Source.IntTy.u256) := Source.intWrap Source.IntTy.u256 (-1)
def omStaticValues (i : Fin 2) : Source.Val mixedLayout (.int Source.IntTy.u256) := if i.val=0 then .int 0 (by decide) else omMax
def omStaticData : Source.Data mixedLayout (.array .memory (.int Source.IntTy.u256) (some 2)) :=
  .array 2 (fun _ eq => (Option.some.inj eq).symm) (fun i => .val (omStaticValues i))
def omStaticPlacement := heapAllocPlacement mixedHeap mixedPlacement omStaticData (.array false 2) (.array 2 _ _)
  1665 1729 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)

theorem om_static_valid : Source.DataOK mixedEnv mixedHeap.ty omStaticData := .array (fun _ => .val (Source.Val.refOK_of_loc rfl _))
theorem om_static_inner : Source.Data.Inner (E := mixedEnv) omStaticData := fun i => ⟨omStaticValues i,rfl⟩
theorem om_static_support : InventoryTypeSupported mixedEnv (.array .memory (.int Source.IntTy.u256) (some 2)) := Or.inl (Or.inr (Or.inl rfl))
theorem om_static_ready : (objectAllocationView mixedHeap mixedPlacement omStaticData rfl (.array false 2) (.array 2 _ _)
    1665 1729 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical).isSome :=
  objectAllocationView_complete _ _ _ rfl _ (.array 2 _ _) 1665 1729 (by decide)
    (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical om_static_support om_static_inner om_static_valid

def omStaticRaw := (objectAllocationView mixedHeap mixedPlacement omStaticData rfl (.array false 2) (.array 2 _ _)
  1665 1729 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical).get om_static_ready

theorem om_static_step : objectAllocationView mixedHeap mixedPlacement omStaticData rfl (.array false 2) (.array 2 _ _)
    1665 1729 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) mixedPhysical=some omStaticRaw :=
  (Option.some_get om_static_ready).symm

def omMaxWord : Roadmap.Word := ⟨2^256-1,by decide⟩

theorem om_static_observer (i : Fin 2) : mload omStaticRaw (1665+i.val*32)=if i.val=0 then 0 else omMaxWord := by
  have scalar : (omStaticValues i).word=some (if i.val=0 then 0 else omMaxWord) := by
    unfold omStaticValues
    split
    · rfl
    · rfl
  have read := ObjectWord.arrayElement (address := omStaticPlacement.address) (l := .memory) (n := some 2)
    2 (fun _ eq => (Option.some.inj eq).symm) (fun j => Source.Data.val (omStaticValues j)) i (omStaticValues i)
      (if i.val=0 then 0 else omMaxWord) rfl (ElementWord.scalar _ _ scalar)
  apply objectAllocationView_source_word mixedHeap mixedPlacement omStaticData rfl (.array false 2) (.array 2 _ _)
    1665 1729 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared
    mixedPhysical omStaticRaw av_mixed_reads om_static_step 6 _ omStaticData rfl (i.val*32) _
  simpa only [Option.isNone_some,Bool.false_eq_true,if_false,Nat.zero_add] using read

end Solidity.Yul.Views.Controls
