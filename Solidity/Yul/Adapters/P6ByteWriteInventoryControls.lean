import Solidity.Yul.Adapters.P6ByteWriteInventory
import Solidity.Yul.Adapters.P6ByteReferenceWriteControls

/-! Two chronological Source byte writes refresh the same complete three-root
inventory. The second write consumes the first actual source state, frame and
retained history. These synthetic frames are not allocation-provenance proofs. -/
namespace Solidity.Yul.Adapters.P6ByteWriteInventory.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteFamilyCopy.Controls (placement entries residual carrier fits)
open P6ByteReferenceWrite (payloadOffset byteWord)
open P6ByteReferenceWrite.Controls (image reached)

def secondFrame (r : InventoryRealization placement)
    (found : r.heap.get 1=some ⟨.string .memory,Source.Data.string (stringOld.set 32 0xff)⟩)
    (addresses : r.placement.address=placement.address) :=
  P6ByteMemory.store8 reached (payloadOffset r.placement 1 true (stringOld.set 32 0xff) found 32 (by decide))
    (byteWord 7) (by change r.placement.address 1+32+32+1≤reached.capacity;rw [addresses];change 321≤512;decide)

/-- Both Source runs and both whole-map reconstructions use the same computed
intermediate inventory; no independent projection or postulated second run. -/
theorem kernel_twice : ∃ r : InventoryRealization placement,
    ∃ found : r.heap.get 1=some ⟨.string .memory,Source.Data.string (stringOld.set 32 0xff)⟩,
    ∃ addresses : r.placement.address=placement.address,
    ∃ next : InventoryRealization placement,
      (Source.writeLoc byteReadFrame 0 (.memByte 1 32)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)).run byteState=
        (.ok (),withSourceHeap byteState r.heap) ∧
      encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
      (Source.writeLoc byteReadFrame 0 (.memByte 1 32)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [7] rfl)).run (withSourceHeap byteState r.heap)=
        (.ok (),withSourceHeap byteState next.heap) ∧
      encodeMixedHeap next.placement next.entries (frameBytes (secondFrame r found addresses))=
        frameBytes (secondFrame r found addresses) ∧
      CoversMixedHeap next.entries ∧ next.entries.map MixedHeapEntry.id=[0,1,2] ∧
      next.heap.get 1=some ⟨.string .memory,Source.Data.string ((stringOld.set 32 0xff).set 32 7)⟩ ∧
      next.heap.get 0=byteState.2.heap.get 0 ∧ next.heap.get 2=byteState.2.heap.get 2 ∧
      (∀ H,Source.MemOK heapByteEnv H byteState → Source.MemOK heapByteEnv H (withSourceHeap byteState next.heap)) := by
  have initial : frameBytes image=encodeMixedHeap placement entries residual := FrameHeap.frameOf_bytes _ _ _ _ _ _
  have first := write byteReadFrame 0 byteState placement placement .initial entries
    P6ByteFamilyCopy.Controls.coverage (by decide) image residual initial 1 true stringOld rfl 32 (by decide) 0xff (by decide)
  dsimp only at first
  obtain ⟨r,run,selected,encoded,covered,ids,other,safe,found,types,count,addresses,free⟩ := first
  have distinct : (r.entries.map MixedHeapEntry.id).Nodup := by rw [ids];decide
  have second := write byteReadFrame 0 (withSourceHeap byteState r.heap) placement r.placement r.history r.entries
    covered distinct reached (frameBytes reached) encoded.symm 1 true (stringOld.set 32 0xff) found
    32 (by decide) 7 (by rw [addresses];change 321≤512;decide)
  dsimp only at second
  obtain ⟨next,run2,selected2,encoded2,covered2,ids2,other2,safe2,found2,types2,count2,addresses2,free2⟩ := second
  refine ⟨r,found,addresses,next,run,encoded,run2,encoded2,covered2,?_,found2,?_,?_,?_⟩
  · rw [ids2,ids];rfl
  · exact (other2 0 (by decide)).trans (other 0 (by decide))
  · exact (other2 2 (by decide)).trans (other 2 (by decide))
  · intro H ok
    exact safe2 H (safe H ok)

/-- Both sibling cells and all source locals are actual, typed values. -/
theorem inhabited_initial : Source.MemOK heapByteEnv byteState.2.heap.ty byteState := actual_initial_MemOK

/-- First changed byte and retained nonzero padding from the real frame control. -/
theorem physical_seed : frameBytes reached 320=255 ∧ frameBytes reached 328=165 :=
  ⟨P6ByteReferenceWrite.Controls.physical_bytes.1,P6ByteReferenceWrite.Controls.physical_bytes.2.1⟩

/-- Omitting a registered sibling cannot cover this actual source heap. -/
theorem missing_entry : ¬ CoversMixedHeap
    [P6ByteFamilyCopy.Controls.first,P6ByteFamilyCopy.Controls.string] := by
  intro covered
  obtain ⟨e,member,identity⟩ := covered 2 (by rfl)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with first | second
  · subst e;exact (by decide : (0:Nat)≠2) identity
  · subst e;exact (by decide : (1:Nat)≠2) identity

/-- Keeping the old images after the physical write overwrites its new byte. -/
theorem stale_images : encodeMixedHeap placement entries (frameBytes reached)≠frameBytes reached := by
  intro same
  have atByte := congrFun same 320
  have stale : encodeMixedHeap placement entries (frameBytes reached) 320=0x61 := by decide
  have wrong : (0x61:UInt8)=255 := stale.symm.trans (atByte.trans P6ByteReferenceWrite.Controls.physical_bytes.1)
  exact (by decide : (0x61:UInt8)≠255) wrong
end Solidity.Yul.Adapters.P6ByteWriteInventory.Controls
