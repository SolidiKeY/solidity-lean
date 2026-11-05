import Solidity.Yul.Adapters.P6ByteReferenceReads
import Solidity.Yul.Adapters.P6RetainedRegionCopyControls

/-! Access controls for actual retained-region preparations. The same location
fails while the string is empty and reads the copied raw payload after regrowth.
These are synthetic heap/frame witnesses, not successful allocation histories. -/
namespace Solidity.Yul.Adapters.P6ByteReferenceReads.Controls
open Solidity.Yul.Views Solidity.Yul.Views.Controls
open Solidity.Backend.MemoryOps.Physical
open Solidity.Yul.Adapters.P6RetainedRegionCopy.Controls

/-- Actual sequential preparations supply both source heaps. Access checks the
current object, without erasing the retained reference or inventing a past read. -/
theorem retained_access : ∃ r : InventoryRealization P6ByteFamilyCopy.Controls.placement,
    ∃ found : r.heap.get 1=some ⟨.string .memory,Source.Data.string []⟩,
    ∃ next : InventoryRealization P6ByteFamilyCopy.Controls.placement,
    zero.2=some r ∧
    (P6RetainedRegionCopy.prepare (withSourceHeap byteState r.heap)
      P6ByteFamilyCopy.Controls.placement r.placement r.history r.entries
      1 true [] found zero.1 growSource growTarget rfl).2=some next ∧
    (Source.readLoc byteReadFrame (.memByte 1 40)).run (withSourceHeap byteState r.heap)=
      (.error (.revert (Source.panicData .index)),withSourceHeap byteState r.heap) ∧
    ∃ inside : 40 < (readBytes
      (frameBytes (P6ByteMemory.copySnapshot zero.1 growSource growTarget rfl)) 288 64).length,
    (Source.readLoc byteReadFrame (.memByte 1 40)).run (withSourceHeap byteState next.heap)=
      (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide)
        [(readBytes (frameBytes (P6ByteMemory.copySnapshot zero.1 growSource growTarget rfl)) 288 64)[40]] rfl),
        withSourceHeap byteState next.heap) := by
  obtain ⟨r,found,next,prepared,regrown,reencoded,read⟩ := kernel_regrow
  have inside : 40 < (readBytes
      (frameBytes (P6ByteMemory.copySnapshot zero.1 growSource growTarget rfl)) 288 64).length := by
    first | simp only [readBytes_length]; decide | decide
  exact ⟨r,found,next,prepared,regrown,
    read_outside byteReadFrame (withSourceHeap byteState r.heap) 1 true [] found 40 (by decide),
    inside,read_byte byteReadFrame (withSourceHeap byteState next.heap) 1 true _ read 40 inside⟩

/-- String-backed byte writes preserve the genuine string constructor and caller
state; this is an existing memory API operation, not surface string indexing. -/
theorem string_write (n : Nat) :
    (Source.writeLoc byteReadFrame n (.memByte 1 0)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)).run byteState=
      (.ok (),withSourceHeap byteState (byteState.2.heap.write 1
        (Source.Data.string (l:=.memory) (stringOld.set 0 0xff)) (by rfl))) := by
  exact write_byte byteReadFrame n byteState 1 true stringOld rfl 0 (by decide) 0xff

/-- An out-of-bounds write preserves the entire state and exact panic payload. -/
theorem string_write_outside (n : Nat) :
    (Source.writeLoc byteReadFrame n (.memByte 1 40)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [0xff] rfl)).run byteState=
      (.error (.revert (Source.panicData .index)),byteState) := by
  exact write_outside byteReadFrame n byteState 1 true stringOld rfl 40 (by decide) 0xff
end Solidity.Yul.Adapters.P6ByteReferenceReads.Controls
