import Solidity.Backend.Scalar.SignedBits
import Solidity.Backend.Scalar.Checked
import Solidity.Backend.Scalar.Guards
import Solidity.Backend.Scalar.Comparisons

/-! Checked int256 negation preserves the source minimum-integer failure and
selects existing overflow bytes instead of accepting the EVM's wrapped result. -/
namespace Solidity.Backend.Scalar

def minimumInt : PrimTy.int.Denote := ⟨-((2 ^ 255 : Nat) : Int), by decide⟩

def negationTest : Program :=
  [.op (.DUP ⟨0, by decide⟩), pushWord (encodeValue .int minimumInt), .op .EQ]

def negationBody : Program := [pushWord 0, .op .SUB]

theorem negationTest_typed (a : PrimTy.int.Denote) (tail : Stack) :
    run negationTest (encodeValue .int a :: tail) =
      some (flag (!PrimTy.int.inRange (-a.val)) :: encodeValue .int a :: tail) := by
  rw [negationTest, run]
  change run [pushWord (encodeValue .int minimumInt), .op .EQ]
    (encodeValue .int a :: encodeValue .int a :: tail) = _
  rw [run, step_pushWord]
  change some (flag (encodeValue .int minimumInt == encodeValue .int a) ::
    encodeValue .int a :: tail) = _
  rw [encode_int_beq]
  have ha : -((2 ^ 255 : Nat) : Int) ≤ a.val ∧ a.val < ((2 ^ 255 : Nat) : Int) := int_range a
  have he : decide (minimumInt.val = a.val) = !PrimTy.int.inRange (-a.val) := by
    by_cases hr : PrimTy.int.inRange (-a.val) = true
    · have hrr : -((2 ^ 255 : Nat) : Int) ≤ -a.val ∧
          -a.val < ((2 ^ 255 : Nat) : Int) := by
        simpa only [PrimTy.inRange, decide_eq_true_eq] using hr
      have hc : ¬ minimumInt.val = a.val := by
        change ¬ -((2 ^ 255 : Nat) : Int) = a.val
        omega
      simp only [hc, decide_false, hr, Bool.not_true]
    · have hrr : ¬ (-((2 ^ 255 : Nat) : Int) ≤ -a.val ∧
          -a.val < ((2 ^ 255 : Nat) : Int)) := by
        simpa only [PrimTy.inRange, decide_eq_true_eq] using hr
      have hc : minimumInt.val = a.val := by
        change -((2 ^ 255 : Nat) : Int) = a.val
        omega
      have hrf : PrimTy.int.inRange (-a.val) = false := Bool.eq_false_iff.mpr hr
      simp only [hc, decide_true, hrf, Bool.not_false]
  rw [he]

theorem negationBody_typed (a : PrimTy.int.Denote) (tail : Stack) :
    run negationBody (encodeValue .int a :: tail) =
      some (BitVec.ofInt 256 (-a.val) :: tail) := by
  rw [negationBody, run, step_pushWord]
  change some ((0#256 - BitVec.ofInt 256 a.val) :: tail) = _
  rw [BitVec.zero_sub, ← BitVec.ofInt_neg]

theorem checked_negation_correct (a : PrimTy.int.Denote) (tail : Stack) :
    guarded negationTest negationBody overflowFailure (encodeValue .int a :: tail) =
      some (checkedOutcome .int (UnOp.evalT .neg (p := .int) rfl a) tail) := by
  unfold guarded
  rw [negationTest_typed]
  cases hr : PrimTy.int.inRange (-a.val) with
  | false =>
    rw [show UnOp.evalT .neg (p := .int) rfl a = none by
      simp only [UnOp.evalT, PrimTy.ofInt?, hr, Bool.false_eq_true, dite_false]]
    rfl
  | true =>
    rw [show UnOp.evalT .neg (p := .int) rfl a = some ⟨-a.val, hr⟩ by
      simp only [UnOp.evalT, PrimTy.ofInt?, hr, dite_true]]
    change (run negationBody (encodeValue .int a :: tail)).map Except.ok =
      some (Except.ok (BitVec.ofInt 256 (-a.val) :: tail))
    rw [negationBody_typed]
    rfl

example : guarded negationTest negationBody overflowFailure
    [encodeValue .int minimumInt, 99] = some (.error overflowFailure) := rfl
example : run negationBody [encodeValue .int minimumInt, 99] =
    some [encodeValue .int minimumInt, 99] := by decide +kernel
example : guarded negationTest negationBody overflowFailure [BitVec.ofInt 256 (-7), 99] =
    some (.ok [7, 99]) := rfl

#print axioms negationTest_typed
#print axioms checked_negation_correct

end Solidity.Backend.Scalar
