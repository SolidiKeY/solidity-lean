import Solidity.Backend.Environment.LoadV2
import Solidity.Lowering.V08.AbiObservations

/-! H274 general word-image adapter. Guards endian/normalization regressions:
loading the actual independent Semantics.wordBytes image returns the entire
original word, not its low byte or a supplied result. V1 remains unchanged;
this is not physical heap ownership, emission provenance or consumer freeze. -/
namespace Solidity.Yul.World.LoadV2Port
open Solidity.Backend Solidity.Backend.Environment

/-- Reuse the existing independent Source/intrinsic ABI encoding agreement. -/
theorem word_image (value : Roadmap.Word) :
    ofBytesBE (Semantics.wordBytes value.val) = value.val := by
  rw [←Lowering.V08.wordBytes_transport value]
  exact Source.wordBytes_value value

/-- Exact full-word readback from the actual initial byte image. -/
theorem load_image (frame : Frame) (memory : Memory) (offset : Word)
    (value : Roadmap.Word) (tail : List Word)
    (image : readMemory memory offset.1.toNat 32 = Semantics.wordBytes value.val) :
    LoadV2.step frame (.op .MLOAD) ⟨offset::tail,memory⟩ =
      some ⟨lenU value.val value.isLt::tail,memory⟩ := by
  rw [LoadV2.load_actual,image,word_image,uintOfNat_eq_lenU value.isLt]

/-- A single existing Backend program family indexed only by the word cell. -/
def code (cell : Nat) : Program :=
  [push256 ⟨(32*cell) % (2^256),Nat.mod_lt _ (by decide)⟩,.op .MLOAD]

/-- Actual defined PUSH/MLOAD execution on the complete initial byte image. -/
theorem code_load (frame : Frame) (memory : Memory) (cell value : Roadmap.Word)
    (tail : List Word) (fits : 32*cell.val+32 ≤ 2^256)
    (image : readMemory memory (32*cell.val) 32 = Semantics.wordBytes value.val) :
    LoadV2.run frame (code cell.val) ⟨tail,memory⟩ =
      some ⟨lenU value.val value.isLt::tail,memory⟩ := by
  have bound : 32*cell.val < 2^256 := by omega
  let address : W256 := ⟨(32*cell.val) % (2^256),Nat.mod_lt _ (by decide)⟩
  have pushed : LoadV2.step frame (push256 address) ⟨tail,memory⟩ =
      some ⟨lenU address.val address.isLt::tail,memory⟩ := by
    change cryptoStep (push256 address) ⟨tail,memory⟩ = _
    exact cryptoStep_constant 32 ⟨address.val,address.isLt⟩ ⟨tail,memory⟩
  have address_value : (lenU address.val address.isLt).1.toNat = 32*cell.val := by
    simp only [address,lenU,Int.toNat_natCast,Nat.mod_eq_of_lt bound]
  have actual := load_image frame memory (lenU address.val address.isLt) value tail
    (by rw [address_value]; exact image)
  change (LoadV2.step frame (push256 address) ⟨tail,memory⟩).bind
    (LoadV2.run frame [.op .MLOAD]) = _
  rw [pushed]
  change (LoadV2.step frame (.op .MLOAD) ⟨lenU address.val address.isLt::tail,memory⟩).bind
    (LoadV2.run frame []) = _
  rw [actual]
  rfl

#print axioms code_load

#print axioms word_image
#print axioms load_image
end Solidity.Yul.World.LoadV2Port
