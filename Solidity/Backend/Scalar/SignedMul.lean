import Solidity.Backend.Scalar.SignedChecked
import Solidity.Backend.Scalar.Negation
import Solidity.Backend.Scalar.PowerGuard

/-! Signed multiplication's division-back overflow guard, including the
minimum-integer factor with negative multiplicand that division alone misses. -/
namespace Solidity.Backend.Scalar

theorem toWord_ofInt (q : Int) (hq : -((2^256:Nat):Int) ≤ q ∧ q < ((2^256:Nat):Int)) :
    Evm.toWord q = (BitVec.ofInt 256 q).toNat := by
  have hW : (0:Int) < ((2^256:Nat):Int) := by decide
  simp only [Evm.toWord, BitVec.toNat_ofInt]
  by_cases hn : 0 ≤ q
  · rw [if_pos hn, Int.emod_eq_of_lt hn hq.2]
  · have he : q % ((2^256:Nat):Int) = q + ((2^256:Nat):Int) := by
      rw [← Int.add_emod_right q ((2^256:Nat):Int)]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [if_neg hn, he]
    rfl

def signedMulTest : Program :=
  [.op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .MUL,
   .op (.DUP ⟨1, by decide⟩), .op (.DUP ⟨1, by decide⟩), .op .SDIV,
   .op (.DUP ⟨3, by decide⟩), .op .EQ, .op (.SWAP ⟨0, by decide⟩), .op .POP,
   .op (.DUP ⟨1, by decide⟩), .op .ISZERO, .op .OR,
   .op (.DUP ⟨2, by decide⟩), pushWord (encodeValue .int minimumInt), .op .EQ,
   .op (.DUP ⟨2, by decide⟩), pushWord 0, .op .SGT, .op .AND, .op .ISZERO,
   .op .AND, .op .ISZERO]

theorem signedMulTest_raw (a b : Word) (tail : Stack) :
    run signedMulTest (a::b::tail) =
      some (flag (!PrimTy.int.inRange (a.toInt*b.toInt)) :: a::b::tail) := by
  have hs : Evm.sgn ((b.toNat*a.toNat)%Evm.W) = (a*b).toInt := by
    have h : Evm.sgn (BitVec.toNat (a * b)) = BitVec.toInt (a * b) := sgn_word (a*b)
    rw [BitVec.toNat_mul] at h
    simpa only [Nat.mul_comm] using h
  have hq : -↑Evm.W ≤ (Evm.sgn (BitVec.toNat b * BitVec.toNat a % Evm.W)).tdiv (BitVec.toInt a) ∧
      (Evm.sgn (BitVec.toNat b * BitVec.toNat a % Evm.W)).tdiv (BitVec.toInt a) < ↑Evm.W := Evm.tdiv_sgn_range (x := (b.toNat*a.toNat)%Evm.W)
    (Nat.mod_lt _ Evm.W_pos) a.toInt
  rw [hs] at hq
  have ht : Evm.toWord ((BitVec.toInt (a * b)).tdiv (BitVec.toInt a)) =
      (BitVec.ofInt 256 ((BitVec.toInt (a * b)).tdiv (BitVec.toInt a))).toNat := toWord_ofInt ((a*b).toInt.tdiv a.toInt) hq
  have h : ¬(BitVec.toNat b = Evm.H ∧ Evm.sgn (BitVec.toNat a) < 0) ∧
        ((BitVec.toNat b =
            if BitVec.toNat a = 0 then 0
            else Evm.toWord ((Evm.sgn (BitVec.toNat b * BitVec.toNat a % Evm.W)).tdiv (Evm.sgn (BitVec.toNat a)))) ∨
          BitVec.toNat a = 0) ↔
      -↑Evm.H ≤ Evm.sgn (BitVec.toNat a) * Evm.sgn (BitVec.toNat b) ∧
        Evm.sgn (BitVec.toNat a) * Evm.sgn (BitVec.toNat b) < ↑Evm.H := (Evm.smul_ok a.isLt b.isLt).1
  rw [sgn_word, sgn_word, hs, ht] at h
  have hz : a.toNat = 0 ↔ a = 0 := by
    exact (BitVec.toNat_eq (x := a) (y := 0#256)).symm
  have hm : b.toNat = Evm.H ↔ b = encodeValue .int minimumInt := by
    rw [BitVec.toNat_eq]
    rfl
  have hd : b.toNat = (if a.toNat = 0 then 0 else
        (BitVec.ofInt 256 ((a*b).toInt.tdiv a.toInt)).toNat) ↔
      b = (if a == 0 then 0 else BitVec.ofInt 256 ((a*b).toInt.tdiv a.toInt)) := by
    by_cases ha : a=0
    · subst a
      simp only [if_true, beq_self_eq_true]
      change b.toNat = 0 ↔ b = 0
      exact (BitVec.toNat_eq (x := b) (y := 0#256)).symm
    · have han : a.toNat ≠ 0 := fun h => ha (hz.mp h)
      have hab : (a==0)=false := decide_eq_false ha
      simp only [han, if_false, hab, Bool.false_eq_true]
      exact BitVec.toNat_eq.symm
  rw [hd, hm, hz] at h
  simp only [beq_iff_eq, Evm.H] at h
  have he : (!(decide (0 > a.toInt) && (encodeValue .int minimumInt == b)) &&
      ((a == 0) || (b == (if a == 0 then 0 else
        BitVec.ofInt 256 ((a*b).toInt.tdiv a.toInt))))) =
      PrimTy.int.inRange (a.toInt*b.toInt) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp,
      Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, beq_eq_false_iff_ne, PrimTy.inRange]
    constructor
    · rintro ⟨hspecial, hzero | hdiv⟩
      · exact h.mp ⟨fun ⟨hm, hn⟩ => hspecial hn hm.symm, Or.inr hzero⟩
      · exact h.mp ⟨fun ⟨hm, hn⟩ => hspecial hn hm.symm, Or.inl hdiv⟩
    · intro hr
      obtain ⟨hspecial, hdiv⟩ := h.mpr hr
      exact ⟨fun hn hm => hspecial ⟨hm.symm, hn⟩, hdiv.elim Or.inr Or.inl⟩
  change run (pushWord (encodeValue .int minimumInt) :: _)
    (b :: (flag (a==0) ||| flag (b == (if a==0 then 0 else
      BitVec.ofInt 256 ((a*b).toInt.tdiv a.toInt)))) :: a::b::tail) = _
  rw [run, step_pushWord]
  change run (pushWord 0 :: _)
    (a :: flag (encodeValue .int minimumInt == b) ::
      (flag (a==0) ||| flag (b == (if a==0 then 0 else
        BitVec.ofInt 256 ((a*b).toInt.tdiv a.toInt)))) :: a::b::tail) = _
  rw [run, step_pushWord]
  let z : Bool := a == 0
  let e : Bool := b == (if a == 0 then 0 else BitVec.ofInt 256 ((a*b).toInt.tdiv a.toInt))
  let m : Bool := encodeValue .int minimumInt == b
  let neg : Bool := decide (a.toInt < 0)
  change some (flag ((flag ((flag neg &&& flag m) == 0) &&& (flag z ||| flag e)) == 0) :: a::b::tail) = _
  rw [flag_and, flag_iszero, flag_or, flag_and, flag_iszero]
  change some (flag (!(!(neg && m) && (z || e))) :: a::b::tail) = _
  rw [he]


def checkedIntMul : CheckedCertificate .mul .int rfl where
  test := signedMulTest
  body := [.op .MUL]
  correct := by
    intro a b tail
    apply guarded_int_range_correct _ _ a b (a.val*b.val) tail
    · simpa only [encode_int_toInt] using
        signedMulTest_raw (encodeValue .int a) (encodeValue .int b) tail
    · change some ((BitVec.ofInt 256 a.val * BitVec.ofInt 256 b.val) :: tail) = _
      rw [← BitVec.ofInt_mul]

/-- Division-back alone accepts this wrapped product; the special guard rejects it. -/
example : guarded checkedIntMul.test checkedIntMul.body overflowFailure
    [BitVec.ofInt 256 (-1), encodeValue .int minimumInt, 99] =
    some (.error overflowFailure) := rfl
example : guarded checkedIntMul.test checkedIntMul.body overflowFailure
    [BitVec.ofInt 256 (-7), 3, 99] = some (.ok [BitVec.ofInt 256 (-21), 99]) := rfl

#print axioms checkedIntMul

#print axioms signedMulTest_raw
end Solidity.Backend.Scalar
