import Solidity.Yul.Compilation.ResultFrame
import Solidity.Yul.Compilation.MemoryHarness

/-! Concrete compiler harness with a proved pure2→1 prefix and published Osaka
memory/storage/transient suffix. The suffix has only a decode/encode roundtrip
(its external tests are not on master) and is not interpreted
by Scalar.run. This is not Y04/Y05 ownership/writeback/G24 or final adequacy. -/
namespace Solidity.Yul.Compilation
open Backend Scalar

def physicalArguments := lowerArgCons
  (lowerBinary selectSub (lowerLocal (n := 2) ⟨0, by decide⟩)
    (lowerLocal (n := 2) ⟨1, by decide⟩)) (lowerNoArgs 2)
def physicalArithmetic := (closeInlineBody ⟨1, by decide⟩ physicalArguments).get (by rfl)

theorem physicalArithmetic_run (a b : Word) (tail : Stack) :
    run physicalArithmetic.code ([a, b] ++ tail) = some ((a - b) :: tail) :=
  physicalArithmetic.correct #v[a, b] tail

/-- Preserve the arithmetic value while writing persistent/transient cells,
then use unaligned scratch31 and copy32bytes to128. The latter offset is target
placement only; source allocation addresses/refinement are separate obligations.
Read other cells5 to detect interference. Results are top-first. -/
def physicalSuffix : Program :=
  [pushWord 123, pushWord 5, .op .SSTORE,
   pushWord 987, pushWord 5, .op .TSTORE,
   readSlot ⟨0, by decide⟩, pushWord 3, .op .SSTORE,
   readSlot ⟨0, by decide⟩, pushWord 4, .op .TSTORE,
   pushWord 31, .op .MSTORE,
   pushWord 31, .op .MLOAD,
   pushWord 3, .op .SLOAD,
   pushWord 4, .op .TLOAD,
   pushWord 32, pushWord 31, pushWord 128, .op .MCOPY,
   pushWord 128, .op .MLOAD,
   pushWord 5, .op .SLOAD,
   pushWord 5, .op .TLOAD]

def observeWords : Nat → Program
  | 0 => []
  | n + 1 => observeWords n ++ [pushWord (32 * n), .op .MSTORE]

def physicalProgram (a b : Word) : Program :=
  pushPrefix [a, b, 77, 88] ++ physicalArithmetic.code ++ physicalSuffix ++
    observeWords 8 ++ [pushWord 256, pushWord 0, .op .RETURN]

theorem physicalProgram_roundtrip (a b : Word) :
    decode (encode (physicalProgram a b)) = some (physicalProgram a b) := decode_encode _

/-- Do not mistake the numeric executor for physical-state semantics. -/
example : run [.op .SSTORE] [3, 9] = none := rfl
example : run [.op .MLOAD] [31] = none := rfl
example : run [.op .MCOPY] [128, 31, 32] = none := rfl
example (tail : Stack) : run physicalArithmetic.code
    ([BitVec.ofNat 256 (2 ^ 200 + 257), 7] ++ tail) =
      some (BitVec.ofNat 256 (2 ^ 200 + 250) :: tail) :=
  physicalArithmetic_run _ _ tail
example : stackBound physicalArithmetic.code 1022 = true := by decide +kernel
example : stackBound physicalArithmetic.code 1023 = false := by decide +kernel
example : run physicalArithmetic.code [1] = none := rfl
#print axioms physicalArithmetic_run
#print axioms physicalProgram_roundtrip
end Solidity.Yul.Compilation
