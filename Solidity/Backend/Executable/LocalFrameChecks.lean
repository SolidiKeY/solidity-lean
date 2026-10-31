import Solidity.Backend.Executable.LocalFrame
import Solidity.Backend.Executable.ScalarSequenceChecks

/-! Actual typed local reads, shifted operand access, wrong index/order and
physical peak controls; numeric slice and encoder evidence only. -/
namespace Solidity.Backend.Executable.LocalFrameChecks
open Scalar ScalarSequence LocalFrame
open ScalarSequenceChecks (caller contract)
def three : PrimTy.uint.Denote := ⟨3, by decide⟩
def result : PrimTy.uint.Denote := ⟨96, by decide⟩

theorem actual_reads :
    (intRead (C := contract)).evalT caller = .ok ⟨-7, by decide⟩ ∧
    (uintRead (C := contract)).evalT caller = .ok ⟨99, by decide⟩ ∧
    run intCode (frameTail caller [123,456]) = some [BitVec.ofInt 256 (-7),BitVec.ofInt 256 (-7),99,123,456] ∧
    run uintCode (frameTail caller [123,456]) = some [99,BitVec.ofInt 256 (-7),99,123,456] :=
  ⟨rfl,rfl,(reads caller [123,456]).1,(reads caller [123,456]).2⟩

theorem local_combination :
    (LocalFrame.expr three).evalT caller = .ok result ∧
    run (LocalFrame.operands three) (frameTail caller [123,456]) =
      some [99,3,BitVec.ofInt 256 (-7),99,123,456] ∧
    run (LocalFrame.code three) (frameTail caller [123,456]) =
      some [96,BitVec.ofInt 256 (-7),99,123,456] ∧
    stackBound (LocalFrame.code three) ((frameTail caller [123,456]).length : Int) = true := by
  have hs := LocalFrame.stages caller [123,456] three result rfl
  exact ⟨source caller three result rfl rfl, hs.2.1, hs.2.2, (capacity caller _ _).mpr (by decide)⟩

/-- Copying the wrong caller index is observable even though both are words. -/
example : run uintCode (frameTail caller []) ≠
    some (encodeValue .int (TEnv.get .here caller.env) :: frameTail caller []) := by decide +kernel

/-- Forgetting the right operand's PUSH shifts the intended uint read onto the
signed caller word. Reversing operand emission independently changes SUB. -/
example : run (literal .uint three ++ [.op (.DUP 1)] ++ subChoice.code) (frameTail caller []) ≠
    some (96 :: frameTail caller []) := by decide +kernel
example : run (uintCode ++ literal .uint three ++ subChoice.code) (frameTail caller []) ≠
    some (96 :: frameTail caller []) := by decide +kernel

/-- The output fits, but the actual intermediate DUP3 reaches1025 words. -/
example : stackBound (LocalFrame.code three)
    ((frameTail caller (List.replicate 1021 17)).length : Int) = false := by
  have no := (capacity caller (List.replicate 1021 17) three)
  simp only [List.length_replicate] at no
  cases h : stackBound (LocalFrame.code three) ((frameTail caller (List.replicate 1021 17)).length : Int) with
  | false => rfl
  | true => have bad := no.mp h; omega

example : stackBound intCode ((frameTail caller (List.replicate 1021 17)).length : Int) = true :=
  (read_capacity caller _).1.mpr (by simp only [List.length_replicate]; omega)

example : (Backend.encode (LocalFrame.code three)).length = 35 := by
  rw [length_encode]
  rfl
example : Backend.encode intCode = [0x80] ∧ Backend.encode uintCode = [0x81] := ⟨rfl,rfl⟩
/-- info: 'Solidity.Backend.Executable.LocalFrameChecks.actual_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_reads
/-- info: 'Solidity.Backend.Executable.LocalFrameChecks.local_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_combination
end Solidity.Backend.Executable.LocalFrameChecks
