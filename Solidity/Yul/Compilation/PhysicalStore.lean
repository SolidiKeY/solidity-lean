import Solidity.Backend.Environment.ByteConstants
import Solidity.Yul.Views.MemoryImages
/-! Constant-operand physical stores using the ACTUAL VY2 byte view and existing
compiler byte-addressed data slice. No new memory state/layout/semantics.
This is not the word-cell Evm.Machine, a native charged step, memory-safe
admission/writeback or full Source/G24 simulation. -/
namespace Solidity.Yul.Compilation.PhysicalStore
open Solidity.Yul.Views

def byteCode (address value : Roadmap.Word) : Backend.Program :=
  Backend.Environment.byteCode address (UInt8.ofNat value.val)

/-- Enumerate the producer's existing big-endian bytes, not another encoder. -/
def bytesOf (value : Roadmap.Word) : List UInt8 := List.ofFn (wordByte value)

/-- Compile a full word as32actual byte stores; address range is an explicit
selection/proof obligation, not silent wrapping. -/
def wordCode (address : Nat) (value : Roadmap.Word) : Backend.Program :=
  Backend.Environment.materialize address (bytesOf value)

def selectWord (address : Nat) (value : Roadmap.Word) : Option Backend.Program :=
  if address+32≤2^256 then some (wordCode address value) else none

/-- Concrete source-view agreement for a generated low-byte store. The
existing byte-data slice preserves every caller stack word. -/
theorem byte_run (address value : Roadmap.Word) (s : Backend.Environment.Slice) :
    Backend.Environment.runData (byteCode address value) s =
      some {s with memory := mstore8 s.memory address.val value} :=
  Backend.Environment.byteCode_correct address (UInt8.ofNat value.val) s

/-- The actual target byte materializer writes exactly the producer's word
view, including endianness and every byte outside the32byte interval. -/
theorem word_memory (m : ByteView) (address : Nat) (value : Roadmap.Word) :
    Backend.Environment.writeBytes m address (bytesOf value) = mstore m address value := by
  funext point
  by_cases inside : address≤point ∧ point<address+32
  · have index : point-address<32 := by omega
    have position : address+(point-address)=point := Nat.add_sub_of_le inside.1
    have target := Backend.Environment.writeBytes_at (bytesOf value) address (point-address) m
      (by simpa only [bytesOf,List.length_ofFn] using index)
    rw [position] at target
    simpa only [bytesOf,List.getElem_ofFn,mstore,dif_pos inside] using target
  · have outside : point<address ∨ address+32≤point := by omega
    have target := Backend.Environment.writeBytes_frame (bytesOf value) address point m
      (by simpa only [bytesOf,List.length_ofFn] using outside)
    exact target.trans (mstore_outside m address point value inside).symm

/-- Derive reads of the original typed source data after an outside byte
update; no desired read/view result is an input premise. -/
theorem image_frame {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (image : MemoryImage p d)
    (m : ByteView) (base : Nat) (address value : Roadmap.Word)
    (outside : address.val<base ∨ base+image.span≤address.val) :
    image.Reads (mstore8 (image.encode m base) address.val value) base := by
  apply image.reads_congr _ (image.encode m base) base
  · intro i inside
    exact find_saveByte_other (image.encode m base) (UInt8.ofNat value.val) (by omega)
  · exact image.encode_reads m base

#print axioms byte_run
#print axioms word_memory
#print axioms image_frame
end Solidity.Yul.Compilation.PhysicalStore
