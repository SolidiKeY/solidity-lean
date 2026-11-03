import Solidity.Backend.AbiEntry.WordValidationInterface

/-! Actual numeric bytecode for strict unsigned bounds. Bounds at or above
2^256 accept every word; they are not silently truncated to an immediate. -/
namespace Solidity.Backend.AbiEntry.WordValidation
open Scalar

/-- Compare a loaded word with an unbounded semantic bound. -/
def belowCode (bound : Nat) : Program :=
  if bound < 2 ^ 256 then
    [pushWord (BitVec.ofNat 256 bound), .op .GT]
  else [.op .POP, pushByte 1]

theorem below_correct (bound : Nat) (word : Scalar.Word) (tail : Stack) :
    run (belowCode bound) (word :: tail) =
      some (flag (decide (word.toNat < bound)) :: tail) := by
  by_cases hb : bound < 2 ^ 256
  · rw [belowCode, if_pos hb, run, step_pushWord]
    simp only [run, step, numericStep, unary, binary, applyBinary,
      Option.bind_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  · have hw : word.toNat < bound := Nat.lt_of_lt_of_le word.isLt (Nat.le_of_not_gt hb)
    rw [belowCode, if_neg hb]
    change some (1 :: tail) = some (flag (decide (word.toNat < bound)) :: tail)
    simp only [decide_eq_true hw, flag, if_true]

theorem below_capacity (bound : Nat) (tail : Stack)
    (h : tail.length + 2 ≤ 1024) :
    stackBound (belowCode bound) ((tail.length + 1 : Nat) : Int) = true := by
  unfold belowCode
  split <;>
    simp only [stackBound, heightTrace, stackDelta, pushWord, pushByte,
      numericDelta, unary, binary, Option.isSome_some, if_true,
      List.all_cons, List.all_nil, Bool.and_true, safeHeight,
      Bool.and_eq_true, decide_eq_true_eq] <;> omega

/-- The semantic enum bound is kept at its actual cardinality. -/
def enumValidator (members : Nat) : Interface.WordValidator (.enumBelow members) where
  code := belowCode members
  scratch := 1
  scratch_fits := by decide
  correct := below_correct members
  capacity := below_capacity members

/-- Boolean validation rejects every word other than zero and one. -/
def boolValidator : Interface.WordValidator .bool where
  code := belowCode 2
  scratch := 1
  scratch_fits := by decide
  correct := below_correct 2
  capacity := below_capacity 2

/-- Covers arbitrary bit counts, including the full word and address160. -/
def uintValidator (bits : Nat) : Interface.WordValidator (.uint bits) where
  code := belowCode (2 ^ bits)
  scratch := 1
  scratch_fits := by decide
  correct := below_correct (2 ^ bits)
  capacity := below_capacity (2 ^ bits)

/-- info: 'Solidity.Backend.AbiEntry.WordValidation.below_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms below_correct
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.below_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms below_capacity
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.enumValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enumValidator
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.boolValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolValidator
/-- info: 'Solidity.Backend.AbiEntry.WordValidation.uintValidator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uintValidator
end Solidity.Backend.AbiEntry.WordValidation
