import Solidity.Yul.Compilation.Allocation
import Solidity.Yul.Compilation.Slices
import Solidity.Backend.Control

/-!
# Compilation controls

Kernel controls for independent VY3 backfill. Encoding checks are not
semantic opcode agreements, nor evidence of frontend Yul admission. -/
namespace Solidity.Yul.Compilation
open Backend

example : (Slots.at (n := 3) ⟨40⟩ ⟨0, by decide⟩) = 42 := rfl
example : (Slots.at (n := 3) ⟨40⟩ ⟨2, by decide⟩) = 40 := rfl
example : (Frame.local (a := 2) (r := 1) (l := 3) ⟨40⟩ ⟨2, by decide⟩) = 45 := rfl
example : ¬ (42 < 42) := by decide
example : ¬ Nonempty (Fin 0) := by rintro ⟨i⟩; exact Nat.not_lt_zero i.val i.isLt

/-- Exact Osaka bytes for the newly requested physical/input families. -/
def physicalVector : Program := [.op .MLOAD, .op .MSTORE, .op .MSTORE8,
  .op .MCOPY, .op .SLOAD, .op .SSTORE, .op .TLOAD, .op .TSTORE,
  .op .CALLDATALOAD, .op .CALLDATASIZE, .op .CALLDATACOPY,
  .op .RETURNDATASIZE, .op .RETURNDATACOPY, .op .KECCAK256, .op .CLZ]
example : encode physicalVector =
    [0x51, 0x52, 0x53, 0x5e, 0x54, 0x55, 0x5c, 0x5d,
     0x35, 0x36, 0x37, 0x3d, 0x3e, 0x20, 0x1e] := rfl
example : decode (encode physicalVector) = some physicalVector := decode_encode _
example : encode [.op .MSTORE8] ≠ encode [.op .MSTORE] := by decide +kernel

/-- Noncommutative, zero-divisor and dirty-bit controls on the existing slice. -/
example : Scalar.run [.op .SUB] [9, 4, 77] = some [5, 77] := by decide +kernel
example : Scalar.run [.op .SUB, .op .DIV] [9, 4, 0, 77] = some [0, 77] := by decide +kernel
example : Scalar.run [.op .ADD] [256, 1, 77] = some [257, 77] := by decide +kernel
example : Scalar.run [.op .SUB] [9] = none := rfl
example : Scalar.run [.op .MSTORE] [0, 9] = none := rfl
example : Scalar.stackBound [.op (.DUP ⟨0, by decide⟩)] 1024 = false := by decide +kernel

/-- Reuse G45's actual label proof. Stack balance and source simulation are
separate obligations; this statement grants neither for arbitrary `Block`. -/
theorem structured_labels (b : Block) (start : Nat) :
    (tags (b.expand start).1).Nodup ∧
    ∀ l ∈ refs (b.expand start).1, l ∈ tags (b.expand start).1 :=
  ⟨Block.tags_nodup b start, Block.refs_defined b start⟩

#print axioms structured_labels
end Solidity.Yul.Compilation
