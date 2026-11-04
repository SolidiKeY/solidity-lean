import Solidity.Yul.Adapters.P6ByteReferenceWrite
import Solidity.Yul.Adapters.P6ByteFamilyCopyControls

/-! Last-byte string write in a real three-object typed heap, with arbitrary
nonzero padding. Physical witnesses are synthetic, not allocation histories.
The negative alignment control distinguishes bytes1 from an MSTORE8 operand. -/
namespace Solidity.Yul.Adapters.P6ByteReferenceWrite.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteFamilyCopy.Controls (placement entries residual carrier fits)

def image := FrameHeap.frameOf carrier placement entries residual fits (by change 512≤512;decide)
def offset := payloadOffset placement 1 true stringOld (by rfl) 32 (by decide)
def reached := P6ByteMemory.store8 image offset (byteWord 0xff) (by decide)
def output := withSourceHeap byteState (byteState.2.heap.write 1
  (Source.Data.string (l:=.memory) (stringOld.set 32 0xff)) (by rfl))

/-- The entry equalities are derived from all three real typed registrations. -/
theorem actual_write (n : Nat) :
    (Source.writeLoc byteReadFrame n (.memByte 1 32)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)).run byteState=(.ok (),output) ∧
    heapByteStateWriteback byteState placement 1 true stringOld rfl (frameBytes reached)=some output ∧
    bytesObjectView (stringOld.set 32 0xff) (by decide) (frameBytes reached) 256=frameBytes reached ∧
    (∀ H,Source.MemOK heapByteEnv H byteState → Source.MemOK heapByteEnv H output) ∧
    (∀ a,a≠1 → output.2.heap.get a=byteState.2.heap.get a) ∧
    (∀ a,a≠320 → frameBytes reached a=frameBytes image a) := by
  have initial := FrameHeap.frameOf_bytes carrier placement entries residual fits (by change 512≤512;decide)
  change frameBytes image=encodeMixedHeap placement entries residual at initial
  have represented := mixed_entry placement entries (by decide) P6ByteFamilyCopy.Controls.coverage
    residual 1 true stringOld rfl
  have header : (mload (frameBytes image) 256).val=stringOld.length := by rw [initial];exact represented.1
  have payload : readBytes (frameBytes image) 288 stringOld.length=stringOld := by rw [initial];exact represented.2
  exact write byteReadFrame n byteState placement 1 true stringOld rfl image header payload 32 (by decide) 0xff (by decide)

/-- The existing owner typing, not a new safety predicate, is inhabited. -/
theorem actual_MemOK : Source.MemOK heapByteEnv byteState.2.heap.ty output :=
  (actual_write 0).2.2.2.1 _ actual_initial_MemOK

/-- The actual selected source location reads the newly written value. -/
theorem actual_readback :
    (Source.readLoc byteReadFrame (.memByte 1 32)).run output=
      (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl),output) := by
  first | decide | rfl

/-- One byte changes, including at the end of a partially occupied word; unknown
padding and the other objects retain their original nonzero bytes. -/
theorem physical_bytes : frameBytes reached 320=255 ∧ frameBytes reached 328=165 ∧
    frameBytes reached 160=0x11 ∧ frameBytes reached 416=0xee := by
  first | decide | rfl

/-- A left-aligned Source bytes1 word would store ZERO via MSTORE8 here. -/
theorem wrong_alignment :
    Environment.dataStep (.op .MSTORE8)
      ⟨[offset,lenU (255*2^248) (by decide)],frameBytes image⟩=
      some ⟨[],Environment.writeByte (frameBytes image) 320 0⟩ := by
  first | rfl | decide

/-- Repeating the same actual physical byte store replaces the old byte. -/
theorem repeated : frameBytes (P6ByteMemory.store8 reached offset (byteWord 7) (by decide)) 320=7 ∧
    frameBytes (P6ByteMemory.store8 reached offset (byteWord 7) (by decide)) 328=165 := by
  first | decide | rfl
end Solidity.Yul.Adapters.P6ByteReferenceWrite.Controls
