import Solidity.Yul.Views.ByteElementStore
import Solidity.Yul.Views.StructWordHeapControls
import Solidity.Yul.Views.HeapByteResizeBoundaries

/-! Actual byte and string alias writes inhabit complete heap reconstruction.
A 33-byte object exercises the second payload word. Source bounds failure and
static memory-write success retain their real meanings. These are kernel seeds. -/
namespace Solidity.Yul.Views.ByteElementStore.Controls
open Solidity.Yul.Views.Controls

def bytesAfter := withSourceHeap mixedState (mixedHeap.write 0 (.bytes (mixedChild.set 2 0xff)) (by rfl))
def bytesPlacement := placement mixedHeap mixedPlacement 0 false mixedChild rfl ⟨2,by decide⟩ 0xff
def bytesPatch := saveByte mixedPhysical 162 0xff

theorem oldReads : ∀ e∈generatedHeapEntries mixedPlacement,e.image.Reads mixedPhysical (mixedPlacement.address e.id) := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro e _
  exact mixedImage_reads_of_coverage mixedPlacement mixedEntries mixed_coverage mixedPhysical mixed_all_reads e

theorem bytes_whole :
    (Source.writeLoc mixedReadFrame 0 (.memByte 0 2)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)).run mixedState=(.ok (),bytesAfter) ∧
    Source.MemOK mixedEnv mixedHeap.ty bytesAfter ∧
    encodeMixedHeap bytesPlacement (generatedHeapEntries bytesPlacement) bytesPatch=bytesPatch ∧
    ∃ history : RetainedAllocation mixedPlacement bytesPlacement,
      enumeratedMemoryWriteback bytesAfter mixedPlacement bytesPlacement history bytesPatch=.ok (some (.ok (),bytesAfter)) ∧
      ReservedOK bytesPatch bytesPlacement.free :=
  whole mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixed_actual_MemOK
    StructWordHeap.Controls.support mixedReadFrame 0 0 false mixedChild rfl ⟨2,by decide⟩ 0xff mixedPhysical oldReads mixed_reserved

def stringAfter := withSourceHeap mixedState (mixedHeap.write 1 (.string (mixedString.set 0 0x80)) (by rfl))
def stringPlacement := placement mixedHeap mixedPlacement 1 true mixedString rfl ⟨0,by decide⟩ 0x80
def stringPatch := saveByte mixedPhysical 416 0x80

theorem string_whole :
    (Source.writeLoc mixedReadFrame 0 (.memByte 1 0)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [0x80] rfl)).run mixedState=(.ok (),stringAfter) ∧
    Source.MemOK mixedEnv mixedHeap.ty stringAfter ∧
    encodeMixedHeap stringPlacement (generatedHeapEntries stringPlacement) stringPatch=stringPatch ∧
    ∃ history : RetainedAllocation mixedPlacement stringPlacement,
      enumeratedMemoryWriteback stringAfter mixedPlacement stringPlacement history stringPatch=.ok (some (.ok (),stringAfter)) ∧
      ReservedOK stringPatch stringPlacement.free :=
  whole mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixed_actual_MemOK
    StructWordHeap.Controls.support mixedReadFrame 0 1 true mixedString rfl ⟨0,by decide⟩ 0x80 mixedPhysical oldReads mixed_reserved

theorem every_H (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) :
    Source.MemOK mixedEnv H bytesAfter ∧ Source.MemOK mixedEnv H stringAfter := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨(whole H mixedState mixedPlacement mixedPlacement (retainInitial _ _) ok
    StructWordHeap.Controls.support mixedReadFrame 0 0 false mixedChild rfl ⟨2,by decide⟩ 0xff mixedPhysical oldReads mixed_reserved).2.1,
    (whole H mixedState mixedPlacement mixedPlacement (retainInitial _ _) ok
    StructWordHeap.Controls.support mixedReadFrame 0 1 true mixedString rfl ⟨0,by decide⟩ 0x80 mixedPhysical oldReads mixed_reserved).2.1⟩

theorem aliases :
    (Source.bytesOfRV mixedReadFrame 0 (.val ((bytesAfter.1.get (.here))))).run bytesAfter=(.ok [0x11,0x22,0xff],bytesAfter) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.memByte 0 2)).run bytesAfter=
      (.ok (.fixedBytes (n:=1) (h:=by decide) [0xff] rfl),bytesAfter) ∧
    (Source.heapBytes (E:=mixedEnv) (Γ:=_) 1).run stringAfter=(.ok [0x80,0x61],stringAfter) ∧
    stringAfter.2.heap.ty 1=some (.string .memory) := ⟨rfl,rfl,rfl,rfl⟩

theorem other_objects_and_padding : bytesAfter.2.heap.get 3=mixedHeap.get 3 ∧
    stringAfter.2.heap.get 0=mixedHeap.get 0 ∧ bytesPatch 163=0xa5 ∧ bytesPatch 1443=0xa5 ∧
    stringPatch 418=0xa5 ∧ (mload stringPatch 384).val=2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨rfl,rfl,by decide,by decide,by decide,by decide⟩

theorem bounds_error : (Source.writeLoc mixedReadFrame 0 (.memByte 0 3)
    (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)).run mixedState=
      (.error (.revert (Source.panicData .index)),mixedState) := rfl

theorem static_memory_success : (Source.writeLoc {mixedReadFrame with static:=true} 0 (.memByte 0 2)
    (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)).run mixedState=(.ok (),bytesAfter) := rfl

def crossingPatch := saveByte (boundaryPhysical 33) 192 0xfe

theorem crossing_payload : readBytes crossingPatch 160 33=(boundaryBytes 33).set 32 0xfe :=
  payload (boundaryBytes 33) ⟨32,by decide⟩ 0xfe (boundaryPhysical 33) 160 (by decide)

theorem crossing_source : (Source.writeLoc byteReadFrame 0 (.memByte 0 32)
    (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xfe] rfl)).run (resizeBoundaryState 33)=
    (.ok (),resizeBoundaryAfter 33 ((boundaryBytes 33).set 32 0xfe)) :=
  source_run (resizeBoundaryState 33) byteReadFrame 0 0 false (boundaryBytes 33) rfl ⟨32,by decide⟩ 0xfe

theorem crossing_neighbors : crossingPatch 191=0x11 ∧ crossingPatch 192=0xfe ∧ crossingPatch 193=0xa5 ∧
    (mload crossingPatch 128).val=33 := by decide

theorem lost_write_negative : bytesPatch 162≠mixedPhysical 162 := by decide

theorem header_instead_of_payload_negative :
    (mload (saveByte mixedPhysical 128 0xff) 128).val≠3 := by decide
end Solidity.Yul.Views.ByteElementStore.Controls
