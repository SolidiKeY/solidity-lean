import Solidity.Yul.Composition.PhysicalBytes
import Solidity.Yul.Views.MemoryImages
import Solidity.Yul.Views.MemoryControls

/-! Read/copy agreement for an ACTUAL intrinsic heap byte object, over every
valid producer placement. This is not an allocator implementation, global heap
writeback, full MemOK preservation, or the G01 allocation-refinement theorem. -/
namespace Solidity.Yul.Composition
open Solidity.Yul.Views

/-- The payload read is derived from the concrete MemoryImage encoder and the
actual heap lookup. Placement, byte bound, reserved words, strict source window
and target extent are real inputs; no whole-view adequacy theorem is supplied. -/
theorem allocated_bytes_window_target {D : Source.Layout} {h : Source.Heap D}
    (p : Placement h) (id : Nat) (bytes : List UInt8) (bound : bytes.length < 2^256)
    (found : h.get id = some ⟨.bytes .memory,.bytes bytes⟩)
    (memory : ByteView) (reserved : ReservedOK memory p.free)
    (offset size destination : Nat) (selected : List UInt8)
    (window : Solidity.Yul.World.returnWindow bytes offset size = some selected)
    (caller : Solidity.Backend.Environment.Slice) (fits : destination + selected.length ≤ 2^256) :
    let image : MemoryImage p (Source.Data.bytes (l := .memory) bytes) := .bytes bytes bound
    let physical := image.encode memory (p.address id)
    ReservedOK physical p.free ∧
    Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize destination selected) caller =
      some {caller with memory := copyBytes caller.memory physical destination (p.address id+32+offset) size} ∧
    ValidRange (p.address id+32+offset) size := by
  let image : MemoryImage p (Source.Data.bytes (l := .memory) bytes) := .bytes bytes bound
  have present : (h.cells id).isSome := by change (h.get id).isSome; rw [found]; rfl
  have reads := image.encode_reads memory (p.address id)
  have payloadRead : readBytes (image.encode memory (p.address id)) (p.address id+32) bytes.length = bytes := reads.2
  have physicalWindow : Solidity.Yul.World.returnWindow
      (readBytes (image.encode memory (p.address id)) (p.address id+32) bytes.length) offset size = some selected := by
    rw [payloadRead]; exact window
  have sourceRange : ValidRange (p.address id+32+offset) size := by
    have span := image.fits p id found
    have extent := p.ends id present
    have freeBound := p.free.isLt
    have sourceBound := (Solidity.Yul.World.returnWindow_some_iff bytes selected offset size).mp window |>.1
    change 32+bytes.length ≤ (p.shape id).size at span
    exact Or.inr (by omega)
  refine ⟨image.reserved memory (p.address id) p.free (p.starts id present) reserved, ?_, sourceRange⟩
  exact (physical_window_target (image.encode memory (p.address id)) caller (p.address id+32)
    bytes.length offset size destination selected physicalWindow sourceRange fits).1

namespace PhysicalMemoryControls
open Solidity.Yul.Views.Controls

def reservedView (gap : Fin 65) : ByteView := mstore (fun _ => 0) 64 (placementShift gap).free

theorem actual_reserved (gap : Fin 65) : ReservedOK (reservedView gap) (placementShift gap).free := by
  constructor
  · exact congrArg Fin.val (mload_mstore (fun _ => 0) 64 (placementShift gap).free)
  · intro i
    exact mstore_outside (fun _ => 0) 64 (96+i.val) (placementShift gap).free (by have hi := i.isLt; omega)

def caller : Solidity.Backend.Environment.Slice := ⟨[Solidity.uintOfNat 99],fun _ => 0xee⟩
def image (gap : Fin 65) : MemoryImage (placementShift gap) (Source.Data.bytes (l := .memory) [0xaa]) :=
  .bytes [0xaa] (by decide)

/-- Every one of the producer's65 valid (including unaligned) placements
supplies the SAME byte to target copy. No pointer equality is assumed. -/
theorem all_placements_same_copy (gap : Fin 65) :
    ReservedOK ((image gap).encode (reservedView gap) ((placementShift gap).address 0)) (placementShift gap).free ∧
    Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize 31 [0xaa]) caller =
      some {caller with memory := (copyBytes caller.memory
        ((image gap).encode (reservedView gap) ((placementShift gap).address 0))
        31 ((placementShift gap).address 0+32) 1)} := by
  have law := allocated_bytes_window_target (placementShift gap) 0 [0xaa] (by decide) rfl
    (reservedView gap) (actual_reserved gap) 0 1 31 [0xaa] (by decide) caller (by decide)
  exact ⟨law.1,law.2.1⟩

example : (placementShift 0).address 0 ≠ (placementShift 1).address 0 := by decide
example : Solidity.Yul.World.returnWindow [0xaa] 2 0 = none := by decide
#print axioms actual_reserved
#print axioms all_placements_same_copy
end PhysicalMemoryControls
#print axioms allocated_bytes_window_target
end Solidity.Yul.Composition
