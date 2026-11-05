import Solidity.Yul.Views.RetainedArrayHeader
import Solidity.Yul.Views.ReferenceDeleteRetainedControls

/-! Whole-map closure of shrink2->0, allocating reference deletion, then
regrowth0->2. Dormant alias words are decoded at the same actual coordinates;
whole Source writeback retains the extended original allocation history. -/
namespace Solidity.Yul.Views.RetainedArrayHeader.Controls
open Solidity.Yul.Views.Controls
open ReferenceDeleteRetained.Controls

theorem whole_regrowth :
    ∃ (current : Placement post.2.heap) (q : Placement regrown.2.heap)
      (history : RetainedAllocation snapshot current) (next : RetainedAllocation snapshot q),
      canonicalRetainedState post snapshot current history (generatedHeapEntries current) 4 (.bytes .memory) regrow=
        some (.ok (),regrown) ∧
      (Source.heapPut 4 ⟨_,dynamicMemberData mixedLayout (.bytes .memory) 2 retainedRefOld⟩).run post=(.ok (),regrown) ∧
      Source.MemOK mixedEnv mixedHeap.ty regrown ∧
      encodeMixedHeap q (generatedHeapEntries q) regrow=regrow ∧
      enumeratedMemoryWriteback regrown snapshot q next regrow=.ok (some (.ok (),regrown)) ∧
      ReservedOK regrow q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  obtain ⟨_,current,addresses,free,safe,full,history,wb,reserved⟩ := source_and_retained
  have supportAllocated := heapAlloc_inventory_supported retainedRefZeroHeap (Source.Data.bytes (l:=.memory) []) trivial support
  have supportOut := heapWrite_inventory_supported allocated.2.heap 3 (.struct MemoryDelete.Controls.refFields) (by rfl) supportAllocated
  have ready := ownerMemOK_prepares_inventory mixedHeap.ty post current safe supportOut
  have coverage := (prepareHeapInventory_ok current _ ready).2.1
  have address0 : current.address 0=128 := by rw [addresses];rfl
  have address4 : current.address 4=1152 := by rw [addresses];rfl
  have childType : post.2.heap.ty 0=some (.bytes .memory) := rfl
  have word : ownedPointerWord current 0 (.bytes .memory) childType=128 := Fin.ext address0
  have element : MemoryElement current (Source.Val.memRef (τ:=.bytes .memory) rfl 0) 128 := by
    rw [←word]
    exact .pointer rfl 0 (.bytes .memory) childType rfl
  have currentReads : ∀ e∈generatedHeapEntries current,e.image.Reads patch (current.address e.id) := by
    have encoded := encodeMixedHeap_reads current _ (prepareHeapInventory_ok current _ ready).2.2 patch
    rw [full] at encoded
    exact encoded
  have tail : ∀ i : Fin (2 : Roadmap.Word).val,mload patch (current.address 4+32+i.val*32)=128 := by
    change ∀ i : Fin 2,mload patch (current.address 4+32+i.val*32)=128
    intro i
    rw [address4]
    have choices : i=0 ∨ i=1 := by have small:=i.isLt;apply Or.imp Fin.ext Fin.ext;omega
    rcases choices with rfl | rfl <;> decide
  let q : Placement regrown.2.heap := retainedMemberArrayPlacement (h:=post.2.heap) snapshot current history 4
    (.bytes .memory) 0 Fin.elim0 rfl 2 retainedRefOld (by decide)
  let next := retainedMemberArray_history snapshot current history 4 (.bytes .memory) 0 Fin.elim0 rfl 2 retainedRefOld (by decide)
  have result := whole mixedHeap.ty post snapshot current history safe supportOut 4 (.bytes .memory)
    (Or.inl (Or.inr (Or.inr rfl))) 0 Fin.elim0 rfl 2 retainedRefOld (fun _ => 128) (fun _ => element)
    (by decide) patch currentReads tail reserved
  rcases result with ⟨prepared,source,safeAfter,addressesAfter,freeAfter,fullAfter,writeback,reservedAfter⟩
  rw [address4] at prepared fullAfter writeback reservedAfter
  exact ⟨current,q,history,next,prepared,source,safeAfter,fullAfter,writeback,reservedAfter⟩

theorem aliases_after_regrowth :
    (readDynamicArrayBytes 0 2).run regrown=(.ok mixedChild,regrown) ∧
    (readDynamicArrayBytes 1 2).run regrown=(.ok mixedChild,regrown) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run regrown=(.ok (.memRef rfl 6),regrown) ∧
    (Source.heapBytes (E:=mixedEnv) (Γ:=_) 6).run regrown=(.ok [],regrown) := ⟨rfl,rfl,rfl,rfl⟩

theorem unrelated_words_and_padding : (mload regrow 960).val=1664 ∧ (mload regrow 992).val=128 ∧
    (mload regrow 1184).val=128 ∧ (mload regrow 1216).val=128 ∧
    (mload regrow 1664).val=0 ∧ regrow 163=0xa5 ∧ regrow 1696=0xa5 := by decide

theorem beyond_original_none (current : Placement post.2.heap) (history : RetainedAllocation snapshot current)
    (address : current.address 4=1152) :
    canonicalRetainedState post snapshot current history (generatedHeapEntries current) 4 (.bytes .memory)
      (mstore patch 1152 3)=none := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold canonicalRetainedState
  rw [address,mload_mstore,if_neg (by decide)]

theorem missing_header_negative : (mload regrow 1152).val≠(mload patch 1152).val := by decide
end Solidity.Yul.Views.RetainedArrayHeader.Controls
