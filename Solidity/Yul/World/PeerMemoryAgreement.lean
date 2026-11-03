import Solidity.Yul.Compilation.MemoryHarness
import Solidity.Yul.World.ByteMemory
import Solidity.Yul.World.WorldChecks

/-! Concrete check against immutable VY3 250555de MemoryHarness. This transports
target bytes into the world consumer, not source-view/compiler adequacy. -/
namespace Solidity.Yul.World.PeerMemoryAgreement
open Solidity.Backend.Environment
open Solidity.Source
open Solidity.Source.StateExamples

theorem compiled_input_load (s : Slice) :
    (runData Solidity.Yul.Compilation.memoryHarness s).bind
      (fun next => TargetMemory.port.load next.memory (toWord 31) (toWord 2)) = some [0xab, 0xcd] := by
  rw [Solidity.Yul.Compilation.memoryHarness_correct]
  simp only [Option.bind_some]
  rw [TargetMemory.load_exact _ _ _ (by decide)]
  exact congrArg some (read_written [0xab, 0xcd] 31 s.memory)

/-- The concrete compiler-written byte survives a disjoint actual world copy. -/
theorem compiled_byte_survives (m : Memory) :
    (copyReturndata TargetMemory.port Checks.callerEntry
      (writeBytes m 31 [0xab, 0xcd]) (toWord 0) (toWord 0) (toWord 2)).map
      (fun after => after 31) = some 0xab := by
  rw [TargetMemory.copy_frame Checks.callerEntry (writeBytes m 31 [0xab, 0xcd])
    (toWord 0) (toWord 0) (toWord 2) [9, 8] 31 (by decide) (by decide) (Or.inr (by decide))]
  exact congrArg some (writeBytes_at [0xab, 0xcd] 31 0 m (by decide))

#print axioms compiled_input_load
#print axioms compiled_byte_survives
end Solidity.Yul.World.PeerMemoryAgreement
