import Solidity.Backend.Scalar.Checked
import Solidity.Backend.Scalar.Comparisons
import Solidity.Evm.SimLemmas

/-! Checked unsigned multiplication reuses the committed pure arithmetic
mul_ok_iff lemma, not the symbolic machine's compilation/simulation theorem. -/
namespace Solidity.Backend.Scalar

theorem flag_or (a b : Bool) : flag a ||| flag b = flag (a || b) := by
  cases a <;> cases b <;> rfl

def unsignedMulTest : Program :=
  [.op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .MUL,
   .op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .DIV,
   .op (.DUP ⟨3, by decide⟩), .op .EQ, .op (.SWAP ⟨0, by decide⟩), .op .POP,
   .op (.DUP ⟨1, by decide⟩), .op .ISZERO, .op .OR, .op .ISZERO]

theorem unsignedMulTest_raw (a b : Word) (tail : Stack) :
    run unsignedMulTest (a :: b :: tail) =
      some (flag (decide (2 ^ 256 ≤ a.toNat * b.toNat)) :: a :: b :: tail) := by
  change some (flag ((flag (a == 0) ||| flag (b ==
      (if a == 0 then 0 else BitVec.ofNat 256 ((a * b).toNat / a.toNat)))) == 0) ::
      a :: b :: tail) = _
  rw [flag_or, flag_iszero]
  by_cases ha : a = 0
  · subst a
    have h0 : ¬ (2 ^ 256 : Nat) ≤ 0 := by decide
    have hz : (0 : Word).toNat = 0 := rfl
    simp only [beq_self_eq_true, Bool.true_or, Bool.not_true, hz,
      Nat.zero_mul, h0, decide_false]
  · have han : a.toNat ≠ 0 := by
      intro h
      apply ha
      apply BitVec.eq_of_toNat_eq
      exact h
    have hab : (a == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact ha (beq_iff_eq.mp h)
    have hq : (a * b).toNat / a.toNat < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (a * b).isLt
    have he : (b == BitVec.ofNat 256 ((a * b).toNat / a.toNat)) =
        decide ((a * b).toNat / a.toNat = b.toNat) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hq, decide_eq_true_eq]
      exact eq_comm
    simp only [hab, Bool.false_eq_true, if_false, Bool.false_or, he]
    have hi : (a * b).toNat / a.toNat = b.toNat ↔ a.toNat * b.toNat < 2 ^ 256 := by
      simpa only [han, false_or, Evm.W, BitVec.toNat_mul] using
        (Evm.mul_ok_iff (a := a.toNat) (b := b.toNat))
    by_cases h : (a * b).toNat / a.toNat = b.toNat
    · have hn : ¬ 2 ^ 256 ≤ a.toNat * b.toNat := by have : a.toNat * b.toNat < 2 ^ 256 := hi.mp h; omega
      simp only [h, decide_true, Bool.not_true, hn, decide_false]
    · have hn : 2 ^ 256 ≤ a.toNat * b.toNat := by
        have hh : ¬ a.toNat * b.toNat < 2 ^ 256 := fun hh => h (hi.mpr hh)
        omega
      simp only [h, decide_false, Bool.not_false, hn, decide_true]

theorem unsignedMulTest_typed (a b : PrimTy.uint.Denote) (tail : Stack) :
    run unsignedMulTest (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (flag (!PrimTy.uint.inRange (a.val * b.val)) ::
        encodeValue .uint a :: encodeValue .uint b :: tail) := by
  rw [unsignedMulTest_raw, encode_uint_toNat, encode_uint_toNat]
  have hp : a.val * b.val = ((a.val.toNat * b.val.toNat : Nat) : Int) := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg (uint_range a).1,
      Int.toNat_of_nonneg (uint_range b).1]
  have he : decide (2 ^ 256 ≤ a.val.toNat * b.val.toNat) =
      !PrimTy.uint.inRange (a.val * b.val) := by
    by_cases hr : PrimTy.uint.inRange (a.val * b.val) = true
    · have hh : 0 ≤ ((a.val.toNat * b.val.toNat : Nat) : Int) ∧
          ((a.val.toNat * b.val.toNat : Nat) : Int) < ((2 ^ 256 : Nat) : Int) := by
        simpa only [PrimTy.inRange, hp, decide_eq_true_eq] using hr
      have hn : ¬ 2 ^ 256 ≤ a.val.toNat * b.val.toNat := by omega
      simp only [hn, decide_false, hr, Bool.not_true]
    · have hh : ¬ (0 ≤ ((a.val.toNat * b.val.toNat : Nat) : Int) ∧
          ((a.val.toNat * b.val.toNat : Nat) : Int) < ((2 ^ 256 : Nat) : Int)) := by
        simpa only [PrimTy.inRange, hp, decide_eq_true_eq] using hr
      have hn : 2 ^ 256 ≤ a.val.toNat * b.val.toNat := by omega
      have hf : PrimTy.uint.inRange (a.val * b.val) = false := Bool.eq_false_iff.mpr hr
      simp only [hn, decide_true, hf, Bool.not_false]
  rw [he]

def checkedUintMul : CheckedCertificate .mul .uint rfl where
  test := unsignedMulTest
  body := [.op .MUL]
  correct := by
    intro a b tail
    simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some]
    change guarded unsignedMulTest [.op .MUL] overflowFailure _ =
      some (checkedOutcome .uint (PrimTy.uint.ofInt? (a.val * b.val)) tail)
    apply guarded_range_correct _ _ a b (a.val * b.val) tail (unsignedMulTest_typed a b tail)
    change some ((BitVec.ofInt 256 a.val * BitVec.ofInt 256 b.val) :: tail) = _
    rw [← BitVec.ofInt_mul]

example : guarded unsignedMulTest [.op .MUL] overflowFailure [0, BitVec.ofInt 256 (-1), 99] =
    some (.ok [0, 99]) := rfl
example : guarded unsignedMulTest [.op .MUL] overflowFailure [7, 9, 99] =
    some (.ok [63, 99]) := rfl
example : guarded unsignedMulTest [.op .MUL] overflowFailure
    [BitVec.ofNat 256 (2 ^ 128), BitVec.ofNat 256 (2 ^ 128), 99] =
    some (.error overflowFailure) := rfl

#print axioms unsignedMulTest_raw
#print axioms checkedUintMul

end Solidity.Backend.Scalar
