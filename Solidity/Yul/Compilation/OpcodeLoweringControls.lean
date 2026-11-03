import Solidity.Yul.Compilation.OpcodeLowering

namespace Solidity.Yul.Compilation
open Backend Scalar

private def maximum : Word := BitVec.ofInt 256 (-1)
private def high : Word := BitVec.ofNat 256 (2 ^ 255)

def addModDemo := lowerTernary selectAddMod (lowerLiteral (n := 0) maximum)
  (lowerLiteral 2) (lowerLiteral 3)
def addModCode : Program := [pushWord 3, pushWord 2, pushWord maximum, .op .ADDMOD]
example : addModDemo.code 0 = some addModCode := rfl
/-- Unbounded intermediate gives2; an incorrectly wrapped ADD would give1. -/
example : run addModCode [77, 88] = some [2, 77, 88] :=
  addModDemo.correct 0 addModCode rfl #v[] #v[] [77, 88]
/-- Unbounded intermediate gives1; an incorrectly wrapped MUL would give0. -/
example : ∃ p, (lowerTernary selectMulMod (lowerLiteral (n := 0) high)
    (lowerLiteral 2) (lowerLiteral 3)).code 0 = some p ∧ run p [77, 88] = some [1, 77, 88] :=
  ⟨_, rfl, (lowerTernary selectMulMod (lowerLiteral (n := 0) high)
    (lowerLiteral 2) (lowerLiteral 3)).correct 0 _ rfl #v[] #v[] [77, 88]⟩
example : ∃ p, (lowerTernary selectAddMod (lowerLiteral (n := 0) 99)
    (lowerLiteral 7) (lowerLiteral 0)).code 0 = some p ∧ run p [77, 88] = some [0, 77, 88] :=
  ⟨_, rfl, (lowerTernary selectAddMod (lowerLiteral (n := 0) 99)
    (lowerLiteral 7) (lowerLiteral 0)).correct 0 _ rfl #v[] #v[] [77, 88]⟩

example : ∃ p, (lowerTernary selectAddMod (lowerLocal (n := 12) ⟨11, by decide⟩)
    (lowerLiteral 2) (lowerLiteral 3)).code 2 = some p ∧
    run p ([100, 101] ++ ((Vector.replicate 12 0).toList ++ [77, 88])) =
      some (2 :: ([100, 101] ++ ((Vector.replicate 12 0).toList ++ [77, 88]))) :=
  ⟨_, rfl, (lowerTernary selectAddMod (lowerLocal (n := 12) ⟨11, by decide⟩)
    (lowerLiteral 2) (lowerLiteral 3)).correct 2 _ rfl (Vector.replicate 12 0) #v[100, 101] [77, 88]⟩
example : (lowerTernary selectAddMod (lowerLocal (n := 13) ⟨12, by decide⟩)
    (lowerLiteral 2) (lowerLiteral 3)).code 2 = none := rfl
example : run [.op .ADDMOD] [7, 8] = none := rfl
example : stackBound addModCode 1021 = true := by decide +kernel
example : stackBound addModCode 1022 = false := by decide +kernel
example : run addModCode (List.replicate 1022 9) = some (2 :: List.replicate 1022 9) :=
  addModDemo.correct 0 addModCode rfl #v[] #v[] _
example : stackBound addModCode (List.replicate 1022 (9 : Word)).length = false := by decide +kernel

private def signedDiv : BinarySelection := (selectBinaryOpcode .SDIV).getD selectDiv
private def signedMod : BinarySelection := (selectBinaryOpcode .SMOD).getD selectMod
private def power : BinarySelection := (selectBinaryOpcode .EXP).getD selectMul
private def shift : BinarySelection := (selectBinaryOpcode .SHL).getD selectMul

example : ∃ p, (lowerBinary signedDiv (lowerLiteral (n := 0) (BitVec.ofInt 256 (-9)))
    (lowerLiteral 4)).code 0 = some p ∧ run p [77, 88] = some [BitVec.ofInt 256 (-2), 77, 88] :=
  ⟨_, rfl, (lowerBinary signedDiv (lowerLiteral (n := 0) (BitVec.ofInt 256 (-9)))
    (lowerLiteral 4)).correct 0 _ rfl #v[] #v[] [77, 88]⟩
example : ∃ p, (lowerBinary signedMod (lowerLiteral (n := 0) (BitVec.ofInt 256 (-9)))
    (lowerLiteral 4)).code 0 = some p ∧ run p [77, 88] = some [maximum, 77, 88] :=
  ⟨_, rfl, (lowerBinary signedMod (lowerLiteral (n := 0) (BitVec.ofInt 256 (-9)))
    (lowerLiteral 4)).correct 0 _ rfl #v[] #v[] [77, 88]⟩
example : ∃ p, (lowerBinary power (lowerLiteral (n := 0) 3) (lowerLiteral 4)).code 0 = some p ∧
    run p [77, 88] = some [81, 77, 88] :=
  ⟨_, rfl, (lowerBinary power (lowerLiteral (n := 0) 3) (lowerLiteral 4)).correct
    0 _ rfl #v[] #v[] [77, 88]⟩
example : ∃ p, (lowerBinary shift (lowerLiteral (n := 0) 2) (lowerLiteral 257)).code 0 = some p ∧
    run p [77, 88] = some [1028, 77, 88] :=
  ⟨_, rfl, (lowerBinary shift (lowerLiteral (n := 0) 2) (lowerLiteral 257)).correct
    0 _ rfl #v[] #v[] [77, 88]⟩

/-- These refusals are target-selection boundaries, not new admission exclusions. -/
example : selectBinaryOpcode .BYTE = none := rfl
example : selectUnaryOpcode .CLZ = none := rfl
example : selectBinaryOpcode .CALL = none := rfl
example : selectBinaryOpcode .GAS = none := rfl
example : run [.op .CLZ] [0] = none := rfl
end Solidity.Yul.Compilation
