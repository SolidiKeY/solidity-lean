import Solidity.Yul.Views.ByteWriteSequence
import Solidity.Yul.Views.RetainedByteHeaderControls

/-! Repeated writes after retained regrowth hit a late real bounds error.
The successful caller prefix, raw bytes, four aliases and original allocation
lineage agree; the invalid write and remaining request do not patch memory. -/
namespace Solidity.Yul.Views.ByteWriteSequence.Controls
open Solidity.Yul.Views.Controls
open RetainedByteHeader.Controls

def requests : List (Nat × UInt8) := [(32,0xfe),(0,0xff),(32,0x80),(64,0xee),(1,0x55)]
def payload0 := readBytes rawA 288 64
def payload1 := payload0.set 32 0xfe
def state1 := withSourceHeap post (post.2.heap.write 1 (.string payload1) (by rfl))
def payload2 := payload1.set 0 0xff
def state2 := withSourceHeap state1 (state1.2.heap.write 1 (.string payload2) (by rfl))
def payload3 := payload2.set 32 0x80
def after := withSourceHeap state2 (state2.2.heap.write 1 (.string payload3) (by rfl))
def raw := saveByte (saveByte (saveByte rawB 320 0xfe) 288 0xff) 320 0x80

theorem actual_coupled : coupled byteReadFrame 0 1 256 requests post rawB=
    ((.error (.revert (Source.panicData .index)),after),raw) := rfl

theorem actual_source : (program byteReadFrame 0 1 requests).run post=(.error (.revert (Source.panicData .index)),after) :=
  (source byteReadFrame 0 1 256 requests post rawB).symm.trans (congrArg Prod.fst actual_coupled)

theorem whole_failure_prefix :
    ∃ q : Placement after.2.heap,
      Source.MemOK heapByteEnv byteHeap.ty after ∧ q.address=qB.address ∧ q.free=qB.free ∧
      encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      ∃ history : RetainedAllocation (bytePlacement 0) q,
        enumeratedMemoryWriteback after (bytePlacement 0) q history raw=.ok (some (.ok (),after)) ∧ ReservedOK raw q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  have supportA := heapWrite_inventory_supported retainedBothZeroHeap 0 (.bytes (readBytes memory 160 4)) (by rfl)
    RetainedByteHeader.Controls.support
  have supportPost := heapWrite_inventory_supported stateA.2.heap 1 (.string payload0) (by rfl) supportA
  have ready := ownerMemOK_prepares_inventory byteHeap.ty post qB second_whole.2.1 supportPost
  have reads := encodeMixedHeap_reads qB _ (prepareHeapInventory_ok qB _ ready).2.2 rawB
  rw [second_whole.2.2.1] at reads
  have result := sound byteHeap.ty (bytePlacement 0) byteReadFrame 0 1 requests post qB hB true payload0 rfl
    second_whole.2.1 supportPost rawB reads second_whole.2.2.2.2
  rw [show qB.address 1=256 from rfl,actual_coupled] at result
  exact result.2

theorem actual_reads :
    (Source.readLoc (E:=heapByteEnv) byteReadFrame (.memByte 1 32)).run after=
      (.ok (.fixedBytes (n:=1) (h:=by decide) [0x80] rfl),after) ∧
    (Source.readLoc (E:=heapByteEnv) byteReadFrame (.memByte 1 1)).run after=
      (.ok (.fixedBytes (n:=1) (h:=by decide) [0x61] rfl),after) ∧
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (after.1.get (.there (.there .here))))).run after=
      (.ok payload3,after) ∧
    (Source.bytesOfRV (E:=heapByteEnv) byteReadFrame 0 (.val (after.1.get (.there (.there (.there .here)))))).run after=
      (.ok payload3,after) := ⟨rfl,rfl,rfl,rfl⟩

theorem exact_raw_and_untouched : raw 288=0xff ∧ raw 289=0x61 ∧ raw 320=0x80 ∧ raw 352=0xa5 ∧
    raw 163=0xa5 ∧ (mload raw 256).val=64 ∧ (mload raw 128).val=4 ∧
    after.2.heap.get 2=byteHeap.get 2 ∧ after.1=post.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,rfl,rfl⟩

theorem empty_child_context :
    (Source.EM.sub (Source.Locals.nil (D:=heapByteEnv.layout))
      (program byteReadFrame 0 1 requests : Source.EM heapByteEnv [] Unit)).run post=
      (.error (.revert (Source.panicData .index)),after) := rfl

theorem failed_and_skipped_writes_negative : raw 352≠0xee ∧ raw 289≠0x55 ∧ raw 320≠0xfe := by decide

theorem empty_identity : coupled byteReadFrame 0 1 256 [] post rawB=((.ok (),post),rawB) := rfl
end Solidity.Yul.Views.ByteWriteSequence.Controls
