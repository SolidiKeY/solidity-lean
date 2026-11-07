import Solidity.Yul.Composition.Concrete
import Solidity.Yul.Views.Bytes

/-! VY2 snapshot byte-copy and VY4 strict returndata windows agree with the
existing VY3-side byte materialization executor. No source heap allocation,
full MemOK, raw call lowering or universal compiler/EVM adequacy is inferred. -/
namespace Solidity.Yul.Composition
open Solidity.Roadmap (Bytes)
open Solidity.Yul.Views

/-- A successful strict window from the actual physical byte view identifies
all selected bytes, including their original source coordinates. -/
theorem physical_window_byte (src : ByteView) (base extent offset size i : Nat)
    (bytes : Bytes)
    (window : Solidity.Yul.World.returnWindow (readBytes src base extent) offset size = some bytes)
    (inside : i < size) :
    bytes[i]'(by have h := Solidity.Yul.World.returnWindow_length _ _ _ _ window; omega) =
      src (base + offset + i) := by
  have selectedByte :=  Solidity.Yul.World.returnWindow_byte (readBytes src base extent) bytes offset size i window inside
  simpa only [readBytes,List.getElem_map,List.getElem_range,Nat.add_assoc] using selectedByte

/-- Full functional equality: copied bytes are exact and every other byte is
unchanged. Both sides use existing producer operations, no replacement view. -/
theorem physical_window_memory (src dst : ByteView) (base extent offset size destination : Nat)
    (bytes : Bytes)
    (window : Solidity.Yul.World.returnWindow (readBytes src base extent) offset size = some bytes) :
    Solidity.Backend.Environment.writeBytes dst destination bytes =
      copyBytes dst src destination (base + offset) size := by
  have length : bytes.length = size := Solidity.Yul.World.returnWindow_length _ _ _ _ window
  funext address
  by_cases inside : destination ≤ address ∧ address < destination + size
  · have j : address-destination < bytes.length := by omega
    have written := Solidity.Backend.Environment.writeBytes_at bytes destination (address-destination) dst j
    rw [Nat.add_sub_of_le inside.1] at written
    rw [written]
    simp only [copyBytes,if_pos inside]
    exact physical_window_byte src base extent offset size (address-destination) bytes window (by omega)
  · rw [Solidity.Backend.Environment.writeBytes_frame bytes destination address dst (by omega)]
    exact (copyBytes_outside dst src destination (base+offset) size address inside).symm

/-- Real target code realizes the bounded physical snapshot window. Source
nonwrapping validity remains explicit rather than assumed from byte equality. -/
theorem physical_window_target (src : ByteView) (caller : Solidity.Backend.Environment.Slice)
    (base extent offset size destination : Nat) (bytes : Bytes)
    (window : Solidity.Yul.World.returnWindow (readBytes src base extent) offset size = some bytes)
    (sourceRange : ValidRange (base+offset) size)
    (fits : destination + bytes.length ≤ 2^256) :
    Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize destination bytes) caller =
      some {caller with memory := copyBytes caller.memory src destination (base+offset) size} ∧
    ValidRange destination size ∧ ValidRange (base+offset) size := by
  refine ⟨?_,Or.inr ?_,sourceRange⟩
  · rw [Solidity.Backend.Environment.materialize_correct bytes destination caller fits,
      physical_window_memory src caller.memory base extent offset size destination bytes window]
  · have length := Solidity.Yul.World.returnWindow_length _ _ _ _ window
    omega

/-- Empty copies beyond the returndata end still fail, despite VY2's empty
physical range being valid. This boundary difference is not erased. -/
example : ValidRange (2^256+1) 0 := Or.inl rfl
example : Solidity.Yul.World.returnWindow (readBytes (fun _ => 0) 0 2) 3 0 = none := by decide +kernel
#print axioms physical_window_byte
#print axioms physical_window_memory
#print axioms physical_window_target
end Solidity.Yul.Composition
