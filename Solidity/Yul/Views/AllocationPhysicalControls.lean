import Solidity.Yul.Views.AllocatedPhysicalMemory
import Solidity.Yul.Views.AllocationInventoryControls

namespace Solidity.Yul.Views.Controls

def avMixedPhysical := byteAllocationView aiBytes 1665 1729 (by decide) mixedPhysical

theorem av_mixed_reads : ∀ e ∈ generatedHeapEntries mixedPlacement,
    e.image.Reads mixedPhysical (mixedPlacement.address e.id) :=
  fun e _ => mixedImage_reads_of_coverage mixedPlacement mixedEntries mixed_coverage mixedPhysical mixed_all_reads e

theorem av_mixed_whole_map : encodeMixedHeap aiPlacement (generatedHeapEntries aiPlacement) avMixedPhysical=avMixedPhysical :=
  (byteAllocation_computed_view mixedHeap mixedPlacement true aiBytes 1665 1729 (by decide)
    (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared mixedPhysical av_mixed_reads).2.2.2

theorem av_mixed_source_and_reserved : enumeratedMemoryWriteback aiState aiPlacement aiPlacement (retainInitial _ _)
    avMixedPhysical=.ok (some (.ok (),aiState)) ∧ ReservedOK avMixedPhysical 1729 := by
  have facts := retainedByteAllocation_physical mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    true aiBytes 1665 1729 (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)
    mixedPhysical mixed_actual_MemOK generated_mixed_types_supported av_mixed_reads mixed_reserved
  exact ⟨facts.2.2.2.2.2.2.1,facts.2.2.2.2.2.2.2.1⟩

theorem av_mixed_every_H (H) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H aiState :=
  byteAllocRef_MemOK mixedState true aiBytes H ok

theorem av_mixed_alias_and_unknown : mload avMixedPhysical 960=128 ∧ mload avMixedPhysical 992=128 ∧
    mload avMixedPhysical (mload avMixedPhysical 960).val=3 ∧
    avMixedPhysical ((mload avMixedPhysical 992).val+32)=0x11 ∧
    mload avMixedPhysical 1184=128 ∧ mload avMixedPhysical 1216=128 ∧
    mload avMixedPhysical 1665=4 ∧ readBytes avMixedPhysical 1697 5=[0xfe,0,0xfd,0xfc,0xa5] ∧
    avMixedPhysical 163=0xa5 ∧ avMixedPhysical 704=0xa5 ∧ avMixedPhysical 1664=0xa5 ∧
    mload avMixedPhysical 64=1729 ∧ mload avMixedPhysical 96=0 := by decide

/-- New owned candidates can turn a previously unsupported raw pointer into a
valid pointer. This explicitly rules out an unjustified decoder-equality claim. -/
theorem av_decoder_extension_not_equality :
    decodeExtendedMemoryMember mixedPlacement (generatedHeapEntries mixedPlacement) (.string .memory) 1665=none ∧
    decodeExtendedMemoryMember aiPlacement (generatedHeapEntries aiPlacement) (.string .memory) 1665=
      some (Source.Val.memRef rfl 6) := ⟨rfl,rfl⟩

/-- Construct an actual initial physical image of the shrunken heap. Its tail
bytes come from the unchanged supplied residual; no capacity is reconstructed
from a gap or free pointer. -/
def avBeforeRetained := encodeMixedHeap retainedEmptyPlacement (generatedHeapEntries retainedEmptyPlacement) emptyPhysical
def avRetainedPhysical := byteAllocationView alBytes 512 576 (by decide) avBeforeRetained

theorem av_retained_before_prepared : prepareHeapInventory retainedEmptyPlacement=.ok (generatedHeapEntries retainedEmptyPlacement) :=
  ownerMemOK_prepares_inventory byteHeap.ty emptyState retainedEmptyPlacement actual_resize_MemOK.2.2 ai_empty_support

theorem av_retained_before_reserved : ReservedOK avBeforeRetained 512 :=
  encodeMixedHeap_reserved _ _ _ raw_resize_reserved.2.2

theorem av_retained_whole_map_and_state : encodeMixedHeap alPlacement (generatedHeapEntries alPlacement) avRetainedPhysical=avRetainedPhysical ∧
    enumeratedMemoryWriteback alState alOriginalPlacement alPlacement alHistory avRetainedPhysical=.ok (some (.ok (),alState)) ∧
    ReservedOK avRetainedPhysical 576 := by
  have before := prepareHeapInventory_ok retainedEmptyPlacement _ av_retained_before_prepared
  have facts := retainedByteAllocation_physical byteHeap.ty emptyState (bytePlacement 0) retainedEmptyPlacement retainedEmpty
    true alBytes 512 576 (by decide) ha_fresh (by decide) avBeforeRetained actual_resize_MemOK.2.2 ai_empty_support
    (encodeMixedHeap_reads _ _ before.2.2 emptyPhysical) av_retained_before_reserved
  exact ⟨facts.2.2.2.2.2.1,facts.2.2.2.2.2.2.1,facts.2.2.2.2.2.2.2.1⟩

theorem av_retained_exact_tail : mload avRetainedPhysical 128=0 ∧
    readBytes avRetainedPhysical 160 4=[0x11,0x22,0x33,0xa5] ∧
    readBytes avRetainedPhysical 544 5=[0xfe,0,0xfd,0xfc,0xa5] ∧
    (alOriginalPlacement.shape 0).size=64 ∧ (alPlacement.shape 0).size=32 := by decide

def avBeforeTwice := encodeMixedHeap alNewZeroPlacement (generatedHeapEntries alNewZeroPlacement) alNewZeroPhysical
def avTwicePhysical := byteAllocationView alNextBytes 577 641 (by decide) avBeforeTwice

theorem av_before_twice_support : ∀ a τ d, alNewZeroState.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported heapByteEnv τ :=
  heapWrite_inventory_supported alGrowHeap 3 (Source.Data.string []) (by rfl)
    (heapWrite_inventory_supported alState.2.heap 0 (Source.Data.bytes growBytes) (by rfl) ai_al_support)

theorem av_twice_whole_map_and_state : encodeMixedHeap alTwicePlacement (generatedHeapEntries alTwicePlacement) avTwicePhysical=avTwicePhysical ∧
    enumeratedMemoryWriteback alTwiceState alTwiceOriginalPlacement alTwicePlacement alTwiceHistory avTwicePhysical=
      .ok (some (.ok (),alTwiceState)) ∧ ReservedOK avTwicePhysical 641 := by
  have prepared := ownerMemOK_prepares_inventory byteHeap.ty alNewZeroState alNewZeroPlacement al_new_zero_MemOK av_before_twice_support
  have facts := prepareHeapInventory_ok alNewZeroPlacement _ prepared
  have allocatedReserved : ReservedOK alPhysical 576 :=
    byteAllocation_reserved alBytes 512 576 512 (by decide) emptyPhysical (by decide) raw_resize_reserved.2.2
  have grownReserved : ReservedOK alGrowPhysical 576 :=
    mstore_object_header_reserved alPhysical 128 4 576 (by decide) allocatedReserved
  have reserved : ReservedOK alNewZeroPhysical 576 :=
    mstore_object_header_reserved alGrowPhysical 512 0 576 (by decide) grownReserved
  have result := retainedByteAllocation_physical byteHeap.ty alNewZeroState alOriginalPlacement alNewZeroPlacement alNewZeroHistory
    false alNextBytes 577 641 (by decide) (heap_later_fresh _ _ 577 (by decide)) (by decide)
    avBeforeTwice al_new_zero_MemOK av_before_twice_support
    (encodeMixedHeap_reads _ _ facts.2.2 alNewZeroPhysical) (encodeMixedHeap_reserved _ _ _ reserved)
  exact ⟨result.2.2.2.2.2.1,result.2.2.2.2.2.2.1,result.2.2.2.2.2.2.2.1⟩

theorem av_twice_exact_tail_and_capacity : mload avTwicePhysical 128=4 ∧ mload avTwicePhysical 512=0 ∧
    mload avTwicePhysical 577=2 ∧ readBytes avTwicePhysical 544 5=[0xfe,0,0xfd,0xfc,0xa5] ∧
    readBytes avTwicePhysical 609 3=[9,8,0xa5] ∧ avTwicePhysical 576=0xa5 ∧
    (alTwiceOriginalPlacement.shape 0).size=64 ∧ (alTwiceOriginalPlacement.shape 3).size=64 := by decide

def avEmptyPlacement := byteAllocPlacement mixedHeap mixedPlacement true [] 1665 1697
  (by decide) (heap_later_fresh _ _ 1665 (by decide)) (by decide)
def avEmptyPhysical := byteAllocationView [] 1665 1697 (by decide) mixedPhysical

theorem av_ordinary_empty_whole_map :
    encodeMixedHeap avEmptyPlacement (generatedHeapEntries avEmptyPlacement) avEmptyPhysical=avEmptyPhysical :=
  (byteAllocation_computed_view mixedHeap mixedPlacement true [] 1665 1697 (by decide)
    (heap_later_fresh _ _ 1665 (by decide)) (by decide) _ generated_mixed_prepared mixedPhysical av_mixed_reads).2.2.2

theorem av_ordinary_empty_header_and_padding : mload avEmptyPhysical 1665=0 ∧ mload avEmptyPhysical 64=1697 ∧
    avEmptyPlacement.address 6=1665 ∧ (avEmptyPlacement.shape 6).size=32 ∧
    avEmptyPhysical 1697=0xa5 ∧ avEmptyPhysical 1664=0xa5 := by decide

theorem av_no_fake_final_read :
    ¬ mixedStructImage.Reads (mstore mixedPhysical 960 1665) (mixedPlacement.address 3) := by
  intro reads
  have word := reads 2 mixedPointer (by rfl)
  have actual : mload (mstore mixedPhysical 960 1665) (mixedPlacement.address 3+2*32)=1665 := by
    exact mload_mstore mixedPhysical 960 1665
  rw [actual] at word
  cases word

end Solidity.Yul.Views.Controls
