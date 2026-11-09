import Solidity.Backend.MemoryOps.PhysicalByteWorldV2Interface
import Solidity.Yul.World.LoadV2Port
/-! R3 concrete versioned point-load instance. Guards full-word readback from
an actual initial image using the existing cell-only PUSH/MLOAD program. This
is neither v1 realization nor compiler/emission/source/resource provenance. -/
namespace Solidity.Yul.World.LoadV2Producer
open Solidity.Backend

/-- Existing cell-indexed PUSH/MLOAD program supplies the versioned field.
The capacity premise is retained even though the port theorem needs less. -/
theorem concrete_producer : MemoryOps.Physical.ByteWorldV2.Producer Solidity.Yul.World.LoadV2Port.code := by
  constructor
  intro frame bytes cell value tail fits _room image
  exact Solidity.Yul.World.LoadV2Port.code_load frame bytes cell value tail fits image

/-- info: 'Solidity.Yul.World.LoadV2Producer.concrete_producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms concrete_producer
end Solidity.Yul.World.LoadV2Producer
