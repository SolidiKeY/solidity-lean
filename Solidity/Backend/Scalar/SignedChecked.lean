import Solidity.Backend.Scalar.Checked
import Solidity.Backend.Scalar.SignedBits
import Solidity.Evm.Signed

/-! Checked signed ADD and SUB with operand-preserving real opcode tests.
The range facts are reused from the pinned arithmetic model, independently
of its machine simulation. Failure emission remains the guard boundary. -/
namespace Solidity.Backend.Scalar

theorem flag_xor (a b : Bool) : flag a ^^^ flag b = flag (a ^^ b) := by
  cases a <;> cases b <;> rfl

theorem xor_range (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R]
    (h : (P ↔ Q) ↔ R) : (decide P ^^ decide Q) = !decide R := by
  by_cases hp : P <;> by_cases hq : Q
  · have hr : R := h.mp ⟨fun _ => hq, fun _ => hp⟩
    simp only [hp, hq, hr, decide_true, Bool.not_true, Bool.xor_self]
  · have hr : ¬ R := fun r => hq ((h.mpr r).mp hp)
    simp only [hp, hq, hr, decide_true, decide_false, Bool.not_false, Bool.xor_false]
  · have hr : ¬ R := fun r => hp ((h.mpr r).mpr hq)
    simp only [hp, hq, hr, decide_true, decide_false, Bool.not_false, Bool.false_xor]
  · have hr : R := h.mp ⟨fun p => False.elim (hp p), fun q => False.elim (hq q)⟩
    simp only [hp, hq, hr, decide_true, decide_false, Bool.not_true, Bool.xor_self]

theorem sgn_word (a : Word) : Evm.sgn a.toNat = a.toInt := signedOf_word a

def signedAddTest : Program :=
  [.op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .ADD,
   .op (.DUP ⟨2, by decide⟩), .op (.SWAP ⟨0, by decide⟩), .op .SLT,
   .op (.DUP ⟨1, by decide⟩), pushWord 0, .op .SGT, .op .XOR]

def signedSubTest : Program :=
  [.op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .SUB,
   .op (.DUP ⟨1, by decide⟩), .op .SLT,
   .op (.DUP ⟨2, by decide⟩), pushWord 0, .op .SGT, .op .XOR]

theorem signedAddTest_raw (a b : Word) (tail : Stack) :
    run signedAddTest (a :: b :: tail) =
      some (flag (!PrimTy.int.inRange (a.toInt + b.toInt)) :: a :: b :: tail) := by
  have hs : Evm.sgn ((b.toNat + a.toNat) % Evm.W) = (a + b).toInt := by
    have h : Evm.sgn (BitVec.toNat (a + b)) = BitVec.toInt (a + b) := sgn_word (a + b)
    rw [BitVec.toNat_add] at h
    simpa only [Nat.add_comm] using h
  have h : (Evm.sgn (BitVec.toNat a) < 0 ↔ Evm.sgn ((BitVec.toNat b + BitVec.toNat a) % Evm.W) < Evm.sgn (BitVec.toNat b)) ↔
      -↑Evm.H ≤ Evm.sgn (BitVec.toNat a) + Evm.sgn (BitVec.toNat b) ∧
        Evm.sgn (BitVec.toNat a) + Evm.sgn (BitVec.toNat b) < ↑Evm.H := (Evm.sadd_ok a.isLt b.isLt).1
  rw [sgn_word, sgn_word, hs] at h
  have he : (decide (BitVec.toInt a < 0) ^^ decide (BitVec.toInt (a + b) < BitVec.toInt b)) =
      !decide (-((2 ^ 255 : Nat) : Int) ≤ BitVec.toInt a + BitVec.toInt b ∧ BitVec.toInt a + BitVec.toInt b < ((2 ^ 255 : Nat) : Int)) := xor_range (a.toInt < 0) ((a+b).toInt < b.toInt)
    (-((2^255:Nat):Int) ≤ a.toInt+b.toInt ∧ a.toInt+b.toInt < ((2^255:Nat):Int)) h
  change run [.op .SGT, .op .XOR]
    (0 :: a :: flag (decide ((a+b).toInt < b.toInt)) :: a :: b :: tail) = _
  change some ((flag (decide (a.toInt < 0)) ^^^
    flag (decide ((a+b).toInt < b.toInt))) :: a :: b :: tail) = _
  rw [flag_xor, he]
  rfl

theorem signedSubTest_raw (a b : Word) (tail : Stack) :
    run signedSubTest (a :: b :: tail) =
      some (flag (!PrimTy.int.inRange (a.toInt - b.toInt)) :: a :: b :: tail) := by
  have hs : Evm.sgn ((a.toNat + (Evm.W - b.toNat)) % Evm.W) = (a - b).toInt := by
    have h : Evm.sgn (BitVec.toNat (a - b)) = BitVec.toInt (a - b) := sgn_word (a - b)
    rw [BitVec.toNat_sub] at h
    simpa only [Nat.add_comm] using h
  have h : (Evm.sgn (BitVec.toNat b) < 0 ↔
        Evm.sgn (BitVec.toNat a) < Evm.sgn ((BitVec.toNat a + (Evm.W - BitVec.toNat b)) % Evm.W)) ↔
      -↑Evm.H ≤ Evm.sgn (BitVec.toNat a) - Evm.sgn (BitVec.toNat b) ∧
        Evm.sgn (BitVec.toNat a) - Evm.sgn (BitVec.toNat b) < ↑Evm.H := (Evm.ssub_ok a.isLt b.isLt).1
  rw [sgn_word, sgn_word, hs] at h
  have he : (decide (BitVec.toInt b < 0) ^^ decide (BitVec.toInt a < BitVec.toInt (a - b))) =
      !decide (-((2 ^ 255 : Nat) : Int) ≤ BitVec.toInt a - BitVec.toInt b ∧ BitVec.toInt a - BitVec.toInt b < ((2 ^ 255 : Nat) : Int)) := xor_range (b.toInt < 0) (a.toInt < (a-b).toInt)
    (-((2^255:Nat):Int) ≤ a.toInt-b.toInt ∧ a.toInt-b.toInt < ((2^255:Nat):Int)) h
  change run [.op .SGT, .op .XOR]
    (0 :: b :: flag (decide (a.toInt < (a-b).toInt)) :: a :: b :: tail) = _
  change some ((flag (decide (b.toInt < 0)) ^^^
    flag (decide (a.toInt < (a-b).toInt))) :: a :: b :: tail) = _
  rw [flag_xor, he]
  rfl


theorem guarded_int_range_correct (test body : Program) (a b : PrimTy.int.Denote)
    (n : Int) (tail : Stack)
    (ht : run test (encodeValue .int a :: encodeValue .int b :: tail) =
      some (flag (!PrimTy.int.inRange n) :: encodeValue .int a :: encodeValue .int b :: tail))
    (hb : run body (encodeValue .int a :: encodeValue .int b :: tail) =
      some (BitVec.ofInt 256 n :: tail)) :
    guarded test body overflowFailure (encodeValue .int a :: encodeValue .int b :: tail) =
      some (checkedOutcome .int (PrimTy.int.ofInt? n) tail) := by
  unfold guarded
  rw [ht]
  cases hr : PrimTy.int.inRange n with
  | false =>
    rw [show PrimTy.int.ofInt? n = none by
      simp only [PrimTy.ofInt?, hr, Bool.false_eq_true, dite_false]]
    rfl
  | true =>
    rw [show PrimTy.int.ofInt? n = some ⟨n, hr⟩ by
      simp only [PrimTy.ofInt?, hr, dite_true]]
    change (run body (encodeValue .int a :: encodeValue .int b :: tail)).map Except.ok =
      some (Except.ok (BitVec.ofInt 256 n :: tail))
    rw [hb]
    rfl

def checkedIntAdd : CheckedCertificate .add .int rfl where
  test := signedAddTest
  body := [.op .ADD]
  correct := by
    intro a b tail
    apply guarded_int_range_correct _ _ a b (a.val+b.val) tail
    · simpa only [encode_int_toInt] using
        signedAddTest_raw (encodeValue .int a) (encodeValue .int b) tail
    · change some ((BitVec.ofInt 256 a.val + BitVec.ofInt 256 b.val) :: tail) = _
      rw [← BitVec.ofInt_add]

def checkedIntSub : CheckedCertificate .sub .int rfl where
  test := signedSubTest
  body := [.op .SUB]
  correct := by
    intro a b tail
    apply guarded_int_range_correct _ _ a b (a.val-b.val) tail
    · simpa only [encode_int_toInt] using
        signedSubTest_raw (encodeValue .int a) (encodeValue .int b) tail
    · change some ((BitVec.ofInt 256 a.val - BitVec.ofInt 256 b.val) :: tail) = _
      rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

example : guarded checkedIntAdd.test checkedIntAdd.body overflowFailure
    [BitVec.ofInt 256 ((2^255-1:Nat):Int), 1, 99] =
    some (.error overflowFailure) := rfl
example : guarded checkedIntSub.test checkedIntSub.body overflowFailure
    [BitVec.ofInt 256 (-7), 2, 99] = some (.ok [BitVec.ofInt 256 (-9), 99]) := rfl

#print axioms checkedIntAdd
#print axioms checkedIntSub

#print axioms signedAddTest_raw
#print axioms signedSubTest_raw
end Solidity.Backend.Scalar
