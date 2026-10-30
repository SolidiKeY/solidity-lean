import Solidity.Backend.Scalar.Bitwise

/-! Signed intrinsic bitwise operations use actual two's-complement word
operations at every input sign, including the source's positive-operand arm. -/
namespace Solidity.Backend.Scalar

theorem signedOf_word (r : Word) : Semantics.signedOf r.toNat = r.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  unfold Semantics.signedOf
  split <;> split <;> omega

theorem wordOf_int (x : Int) : Semantics.wordOf x = (BitVec.ofInt 256 x).toNat := rfl

theorem encoded_signed_word (r : Word) (tail : Stack) :
    (PrimTy.int.ofInt? r.toInt).map (fun v => encodeValue .int v :: tail) = some (r :: tail) := by
  have hr : PrimTy.int.inRange r.toInt = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq, Int.natCast_pow]
    exact ⟨BitVec.le_toInt r, BitVec.toInt_lt⟩
  rw [encoded_int _ hr]
  rw [BitVec.ofInt_toInt]

/-- The source's special nonnegative arm agrees with the signed word reading
because no bitwise operation on two positive int256 values sets the sign bit. -/
theorem signedBitwise_read (f : Nat → Nat → Nat)
    (hf : ∀ a b, a < 2 ^ 255 → b < 2 ^ 255 → f a b < 2 ^ 255)
    (x y : Int) (hx : -((2 ^ 255 : Nat) : Int) ≤ x ∧ x < ((2 ^ 255 : Nat) : Int))
    (hy : -((2 ^ 255 : Nat) : Int) ≤ y ∧ y < ((2 ^ 255 : Nat) : Int))
    (r : Word) (hr : r.toNat = f (BitVec.ofInt 256 x).toNat (BitVec.ofInt 256 y).toNat) :
    Semantics.uintBitwise f x y = r.toInt := by
  cases x with
  | ofNat a =>
    cases y with
    | ofNat b =>
      simp only [Int.ofNat_eq_coe] at hx hy hr ⊢
      have ha : a < 2 ^ 255 := by omega
      have hb : b < 2 ^ 255 := by omega
      have haw : a < 2 ^ 256 := by omega
      have hbw : b < 2 ^ 256 := by omega
      simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt haw, Nat.mod_eq_of_lt hbw] at hr
      have hsmall : r.toNat < 2 ^ 255 := by rw [hr]; exact hf a b ha hb
      rw [Semantics.uintBitwise_natCast, ← hr, ← signedOf_word]
      simp only [Semantics.signedOf, hsmall, if_true]
    | negSucc b =>
      change Semantics.signedOf (f (Semantics.wordOf (Int.ofNat a))
        (Semantics.wordOf (Int.negSucc b))) = r.toInt
      rw [wordOf_int, wordOf_int, ← hr, signedOf_word]
  | negSucc a =>
    cases y with
    | ofNat b =>
      change Semantics.signedOf (f (Semantics.wordOf (Int.negSucc a))
        (Semantics.wordOf (Int.ofNat b))) = r.toInt
      rw [wordOf_int, wordOf_int, ← hr, signedOf_word]
    | negSucc b =>
      change Semantics.signedOf (f (Semantics.wordOf (Int.negSucc a))
        (Semantics.wordOf (Int.negSucc b))) = r.toInt
      rw [wordOf_int, wordOf_int, ← hr, signedOf_word]

def intAnd : BinaryCertificate .band .int rfl where
  code := [.op .AND]
  correct := by
    intro a b tail
    let r : Word := encodeValue .int a &&& encodeValue .int b
    change some (r :: tail) =
      (PrimTy.int.ofInt? (Semantics.uintBitwise (· &&& ·) a.val b.val)).map
        (fun v => encodeValue .int v :: tail)
    have he : Semantics.uintBitwise (· &&& ·) a.val b.val = r.toInt := by
      refine signedBitwise_read (· &&& ·) ?_ a.val b.val (int_range a) (int_range b) r ?_
      · intro a b ha hb
        exact Nat.and_lt_two_pow a hb
      · exact BitVec.toNat_and _ _
    rw [he]
    exact (encoded_signed_word r tail).symm

def intOr : BinaryCertificate .bor .int rfl where
  code := [.op .OR]
  correct := by
    intro a b tail
    let r : Word := encodeValue .int a ||| encodeValue .int b
    change some (r :: tail) =
      (PrimTy.int.ofInt? (Semantics.uintBitwise (· ||| ·) a.val b.val)).map
        (fun v => encodeValue .int v :: tail)
    have he : Semantics.uintBitwise (· ||| ·) a.val b.val = r.toInt := by
      refine signedBitwise_read (· ||| ·) ?_ a.val b.val (int_range a) (int_range b) r ?_
      · intro a b ha hb
        exact Nat.or_lt_two_pow ha hb
      · exact BitVec.toNat_or _ _
    rw [he]
    exact (encoded_signed_word r tail).symm

def intXor : BinaryCertificate .bxor .int rfl where
  code := [.op .XOR]
  correct := by
    intro a b tail
    let r : Word := encodeValue .int a ^^^ encodeValue .int b
    change some (r :: tail) =
      (PrimTy.int.ofInt? (Semantics.uintBitwise (· ^^^ ·) a.val b.val)).map
        (fun v => encodeValue .int v :: tail)
    have he : Semantics.uintBitwise (· ^^^ ·) a.val b.val = r.toInt := by
      refine signedBitwise_read (· ^^^ ·) ?_ a.val b.val (int_range a) (int_range b) r ?_
      · intro a b ha hb
        exact Nat.xor_lt_two_pow ha hb
      · exact BitVec.toNat_xor _ _
    rw [he]
    exact (encoded_signed_word r tail).symm

example : run intAnd.code [BitVec.ofInt 256 (-1), 7, 99] = some [7, 99] := by decide +kernel
example : run intOr.code [BitVec.ofInt 256 (-128), 127, 99] =
    some [BitVec.ofInt 256 (-1), 99] := by decide +kernel
example : run intXor.code [BitVec.ofInt 256 (-1), BitVec.ofInt 256 (-1), 99] =
    some [0, 99] := by decide +kernel

#print axioms intAnd
#print axioms intOr
#print axioms intXor

end Solidity.Backend.Scalar
