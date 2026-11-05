import Solidity.Yul.Views.RetainedByteHeader
import Solidity.Yul.Views.RetainedByteControls

/-! Three objects and four aliases witness sequential bytes/string regrowth.
Payload comes from the actual old complete map, including nonzero padding made
live by growth. Each new whole-map result supplies the next step's reads. -/
namespace Solidity.Yul.Views.RetainedByteHeader.Controls
open Solidity.Yul.Views.Controls

def p := retainedBothZeroPlacement
def entry0 : MixedHeapEntry p := ⟨0,_,.bytes [],rfl,.bytes _ (by decide)⟩
def entry1 : MixedHeapEntry p := ⟨1,_,.string [],rfl,.string _ (by decide)⟩
def entry2 : MixedHeapEntry p := ⟨2,_,.bytes byteOther,rfl,.bytes _ (by decide)⟩
def entries := [entry0,entry1,entry2]
def memory := encodeMixedHeap p entries bytePhysical

theorem coverage : CoversMixedHeap entries := by
  intro a present
  rw [retainedBothZero.occupancy a] at present
  have small := byteHeap_present_lt a present
  have choices : a=0 ∨ a=1 ∨ a=2 := by omega
  rcases choices with rfl | rfl | rfl
  · exact ⟨entry0,List.mem_cons_self,rfl⟩
  · exact ⟨entry1,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · exact ⟨entry2,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩

theorem support : ∀ a τ d,retainedBothZeroHeap.get a=some ⟨τ,d⟩ → InventoryTypeSupported heapByteEnv τ := by
  intro a τ d found
  have present : (retainedBothZeroHeap.cells a).isSome := by change (retainedBothZeroHeap.get a).isSome=true;rw [found];rfl
  rw [retainedBothZero.occupancy a] at present
  have small := byteHeap_present_lt a present
  have choices : a=0 ∨ a=1 ∨ a=2 := by omega
  rcases choices with rfl | rfl | rfl <;> cases found <;> trivial

theorem oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id) := by
  intro e _
  exact mixedImage_reads_of_coverage p entries coverage memory (encodeMixedHeap_reads p entries (by decide) bytePhysical) e

def rawA := mstore memory 128 4
def stateA := withSourceHeap retainedBothZeroState (retainedBothZeroHeap.write 0 (.bytes (readBytes memory 160 4)) (by rfl))
def qA : Placement stateA.2.heap := placement retainedBothZeroHeap (bytePlacement 0) p retainedBothZero
  0 false [] rfl memory 4 (by decide)
def hA : RetainedAllocation (bytePlacement 0) qA := history retainedBothZeroHeap (bytePlacement 0) p retainedBothZero
  0 false [] rfl memory 4 (by decide)

theorem first_whole :
    retainedByteStateWriteback retainedBothZeroState (bytePlacement 0) p retainedBothZero 0 false [] rfl rawA=some stateA ∧
    Source.MemOK heapByteEnv byteHeap.ty stateA ∧ encodeMixedHeap qA (generatedHeapEntries qA) rawA=rawA ∧
    enumeratedMemoryWriteback stateA (bytePlacement 0) qA hA rawA=.ok (some (.ok (),stateA)) ∧
    ReservedOK rawA qA.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have initialReserved : ReservedOK memory p.free := encodeMixedHeap_reserved p entries bytePhysical resize_initial_reserved
  obtain ⟨prepared,source,safe,addresses,free,full,wb,reserved⟩ := whole byteHeap.ty retainedBothZeroState (bytePlacement 0) p
    retainedBothZero retained_both_zero_MemOK support 0 false [] rfl memory 4 (by decide) oldReads initialReserved
  exact ⟨prepared,safe,full,wb,reserved⟩

def recoveredString := List.replicate 33 (0x61 : UInt8) ++ List.replicate 31 0xa5
def post := withSourceHeap stateA (stateA.2.heap.write 1 (.string (readBytes rawA 288 64)) (by rfl))
def rawB := mstore rawA 256 64
def qB : Placement post.2.heap := placement stateA.2.heap (bytePlacement 0) qA hA 1 true [] rfl rawA 64 (by decide)
def hB : RetainedAllocation (bytePlacement 0) qB := history stateA.2.heap (bytePlacement 0) qA hA
  1 true [] rfl rawA 64 (by decide)

theorem second_whole :
    retainedByteStateWriteback stateA (bytePlacement 0) qA hA 1 true [] rfl rawB=some post ∧
    Source.MemOK heapByteEnv byteHeap.ty post ∧ encodeMixedHeap qB (generatedHeapEntries qB) rawB=rawB ∧
    enumeratedMemoryWriteback post (bytePlacement 0) qB hB rawB=.ok (some (.ok (),post)) ∧ ReservedOK rawB qB.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have supportA := heapWrite_inventory_supported retainedBothZeroHeap 0 (.bytes (readBytes memory 160 4)) (by rfl) support
  have ready := ownerMemOK_prepares_inventory byteHeap.ty stateA qA first_whole.2.1 supportA
  have readsA := encodeMixedHeap_reads qA (generatedHeapEntries qA) (prepareHeapInventory_ok qA _ ready).2.2 rawA
  rw [first_whole.2.2.1] at readsA
  obtain ⟨prepared,source,safe,addresses,free,full,wb,reserved⟩ := whole byteHeap.ty stateA (bytePlacement 0) qA hA
    first_whole.2.1 supportA 1 true [] rfl rawA 64 (by decide) readsA first_whole.2.2.2.2
  exact ⟨prepared,safe,full,wb,reserved⟩

theorem recovered_payloads : readBytes memory 160 4=growBytes ∧ readBytes rawA 288 64=recoveredString := by decide

theorem four_aliases :
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get .here))).run post=(.ok growBytes,post) ∧
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get (.there .here)))).run post=(.ok growBytes,post) ∧
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get (.there (.there .here))))).run post=(.ok recoveredString,post) ∧
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get (.there (.there (.there .here)))))).run post=(.ok recoveredString,post) := by
  have one : (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get .here))).run post=
      (.ok (readBytes memory 160 4),post) := rfl
  have two : (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get (.there .here)))).run post=
      (.ok (readBytes memory 160 4),post) := rfl
  have three : (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get (.there (.there .here))))).run post=
      (.ok (readBytes rawA 288 64),post) := rfl
  have four : (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (post.1.get (.there (.there (.there .here)))))).run post=
      (.ok (readBytes rawA 288 64),post) := rfl
  rw [recovered_payloads.1] at one two
  rw [recovered_payloads.2] at three four
  exact ⟨one,two,three,four⟩

theorem exact_payload_and_padding : (mload rawB 128).val=4 ∧ (mload rawB 256).val=64 ∧
    rawB 160=0x11 ∧ rawB 162=0x33 ∧ rawB 163=0xa5 ∧ rawB 164=0xa5 ∧
    rawB 319=0x61 ∧ rawB 320=0x61 ∧ rawB 321=0xa5 ∧ rawB 351=0xa5 ∧ rawB 352=0xa5 ∧
    (mload rawB 384).val=3 ∧ post.2.heap.get 2=byteHeap.get 2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,rfl⟩

theorem beyond_original_none : retainedByteStateWriteback stateA (bytePlacement 0) qA hA 1 true [] rfl
    (mstore rawA 256 65)=none := rfl

theorem lost_first_header_negative : (mload rawB 128).val≠(mload memory 128).val := by decide

theorem fresh_capacity_counter : (p.shape 1).size=32 ∧ ((bytePlacement 0).shape 1).size=96 ∧
    (MemoryShape.bytes 64).size>(p.shape 1).size := by decide
end Solidity.Yul.Views.RetainedByteHeader.Controls
