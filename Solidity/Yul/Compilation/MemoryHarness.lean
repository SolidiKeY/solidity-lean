import Solidity.Backend.Environment.ByteConstants

/-! Target-only memory backfill. The pre-existing byte-materialization slice
is reused unchanged. No Y05 logical-memory refinement or storage simulation
is inferred from these checks. -/
namespace Solidity.Yul.Compilation
open Backend

/-- A concrete two-byte target-memory harness crossing the 32-byte boundary. -/
def memoryHarness : Program := Backend.Environment.materialize 31 [0xab, 0xcd]

theorem memoryHarness_correct (s : Backend.Environment.Slice) :
    Backend.Environment.runData memoryHarness s =
      some { s with memory := Backend.Environment.writeBytes s.memory 31 [0xab, 0xcd] } :=
  Backend.Environment.materialize_correct _ _ _ (by decide)

theorem memoryHarness_frame (m : Backend.Environment.Memory) (i : Nat)
    (outside : i < 31 ∨ 33 ≤ i) :
    Backend.Environment.writeBytes m 31 [0xab, 0xcd] i = m i :=
  Backend.Environment.writeBytes_frame _ _ _ _ outside

example : Backend.Environment.readMemory (Backend.Environment.writeBytes (fun _ => 0) 31 [0xab, 0xcd]) 31 2 =
    [0xab, 0xcd] := Backend.Environment.read_written _ _ _
example : Backend.Environment.dataStep (.op .MSTORE8) ⟨[], fun _ => 0⟩ = none := rfl

#print axioms memoryHarness_correct
#print axioms memoryHarness_frame
end Solidity.Yul.Compilation
