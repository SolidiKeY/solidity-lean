import Solidity.Yul.World.ByteMemory
import Solidity.Backend.MemoryOps.PhysicalByteWorldInterface

/-! H26 conditional consumer of the published P6 byte-load producer.
The code is indexed only by its cell, never current memory or a desired result.
copyReturndata and write/readback are the existing concrete functions. No
emitted RETURNDATACOPY opcode implementation is established. Only the
final byte-target load uses the explicit pending Producer field. No inhabitant,
Source heap/world/compiler/resource or native MLOAD adequacy is inferred. -/
namespace Solidity.Yul.World.ReturndataByteLoad
open Solidity.Source
open Solidity.Roadmap (Address Word)
open Solidity.Backend
variable {D : Layout} {L T : Address → Solidity.Source.SPath → Solidity.Source.STy}

/-- Copy an actual last-frame word window, then load its exact numeric image
through the published P6 signature. Alignment, source bounds and capacity are
real initial premises; an output/run equation is never a premise. -/
theorem copy_load {code : Nat → Backend.Program}
    (producer : MemoryOps.Physical.ByteWorld.Producer code)
    (frame : Environment.Frame) (entry : Effects D L T) (memory : Environment.Memory)
    (destination source : Word) (cell value : Fin Evm.W)
    (window : returnWindow entry.returndata source.val 32 = some (Semantics.wordBytes value.val))
    (placement : destination.val = 32*cell.val)
    (fits : 32*cell.val+32 ≤ 2^256) (tail : List Environment.Word)
    (room : tail.length+1 ≤ 1024) :
    let after := Environment.writeBytes memory destination.val (Semantics.wordBytes value.val)
    copyReturndata TargetMemory.port entry memory destination source (toWord 32) = some after ∧
    Environment.runSlice frame (code cell.val) ⟨tail,after⟩ =
      some ⟨lenU value.val value.isLt::tail,after⟩ ∧
    ∀ i, i < destination.val ∨ destination.val+32 ≤ i → after i = memory i := by
  dsimp only
  have length : (Semantics.wordBytes value.val).length = 32 := Environment.wordBytes_length _
  have bound : destination.val+(Semantics.wordBytes value.val).length ≤ 2^256 := by
    rw [length,placement]
    exact fits
  constructor
  · rw [copyReturndata_exact _ _ _ _ _ _ _ (by
      simpa only [show (toWord 32).val=32 from rfl] using window)]
    exact TargetMemory.store_exact memory destination _ bound
  constructor
  · apply producer.load frame _ cell value tail fits room
    rw [←placement,←length]
    exact Environment.read_written _ _ _
  · intro i outside
    apply Environment.writeBytes_frame
    simpa only [length] using outside

end Solidity.Yul.World.ReturndataByteLoad
