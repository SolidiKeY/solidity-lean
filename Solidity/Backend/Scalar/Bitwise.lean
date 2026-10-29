import Solidity.Backend.Scalar.Casts

/-! Unsigned bitwise selection is connected to the intrinsic integer-based
bitwise denotation, not inferred merely from an opcode name. -/
namespace Solidity.Backend.Scalar

/-- A word's canonical unsigned integer always fits the existing uint carrier. -/
theorem encoded_word (r : Word) (tail : Stack) :
    (PrimTy.uint.ofInt? (r.toNat : Int)).map (fun v => encodeValue .uint v :: tail) =
      some (r :: tail) := by
  have hr : PrimTy.uint.inRange (r.toNat : Int) = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr r.isLt⟩
  rw [encoded_uint _ hr]
  have he : BitVec.ofInt 256 (r.toNat : Int) = r := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt r.isLt]
  rw [he]

/-- Arithmetic bridge for any word bitwise operation whose unsigned reading
is the corresponding natural operation. Concrete opcode instances discharge hr. -/
theorem uintBitwise_encoded (f : Nat → Nat → Nat) (a b : PrimTy.uint.Denote)
    (r : Word) (hr : r.toNat = f a.val.toNat b.val.toNat) (tail : Stack) :
    (PrimTy.uint.ofInt? (Semantics.uintBitwise f a.val b.val)).map
      (fun v => encodeValue .uint v :: tail) = some (r :: tail) := by
  have ha : a.val = (a.val.toNat : Int) := by have := uint_range a; omega
  have hb : b.val = (b.val.toNat : Int) := by have := uint_range b; omega
  have he : Semantics.uintBitwise f a.val b.val = (r.toNat : Int) := by
    calc
      Semantics.uintBitwise f a.val b.val = (f a.val.toNat b.val.toNat : Int) := by
        rw [ha, hb]
        rfl
      _ = (r.toNat : Int) := congrArg Int.ofNat hr.symm
  rw [he]
  exact encoded_word r tail

/-- Intrinsic unsigned `&&&` uses Osaka AND. -/
def uintAnd : BinaryCertificate .band .uint rfl where
  code := [.op .AND]
  correct := by
    intro a b tail
    change some (((encodeValue .uint a) &&& (encodeValue .uint b)) :: tail) =
      (PrimTy.uint.ofInt? (Semantics.uintBitwise (· &&& ·) a.val b.val)).map
        (fun v => encodeValue .uint v :: tail)
    symm
    apply uintBitwise_encoded
    simp only [BitVec.toNat_and, encode_uint_toNat]

/-- Intrinsic unsigned `|||` uses Osaka OR. -/
def uintOr : BinaryCertificate .bor .uint rfl where
  code := [.op .OR]
  correct := by
    intro a b tail
    change some (((encodeValue .uint a) ||| (encodeValue .uint b)) :: tail) =
      (PrimTy.uint.ofInt? (Semantics.uintBitwise (· ||| ·) a.val b.val)).map
        (fun v => encodeValue .uint v :: tail)
    symm
    apply uintBitwise_encoded
    simp only [BitVec.toNat_or, encode_uint_toNat]

/-- Intrinsic unsigned `^^^` uses Osaka XOR. -/
def uintXor : BinaryCertificate .bxor .uint rfl where
  code := [.op .XOR]
  correct := by
    intro a b tail
    change some (((encodeValue .uint a) ^^^ (encodeValue .uint b)) :: tail) =
      (PrimTy.uint.ofInt? (Semantics.uintBitwise (· ^^^ ·) a.val b.val)).map
        (fun v => encodeValue .uint v :: tail)
    symm
    apply uintBitwise_encoded
    simp only [BitVec.toNat_xor, encode_uint_toNat]

/-- Unsigned complement retains exactly the existing 256-bit source meaning. -/
def uintNot : UnaryCertificate .bnot .uint rfl where
  code := [.op .NOT]
  correct := by
    intro a tail
    change some ((~~~encodeValue .uint a) :: tail) =
      (PrimTy.uint.ofInt? (Semantics.uintBound - 1 - a.val)).map
        (fun v => encodeValue .uint v :: tail)
    have he : Semantics.uintBound - 1 - a.val =
        ((~~~encodeValue .uint a).toNat : Int) := by
      rw [BitVec.toNat_not, encode_uint_toNat]
      have ha := uint_range a
      unfold Semantics.uintBound
      omega
    rw [he]
    exact (encoded_word _ tail).symm

example : run uintAnd.code [0xf0, 0x3c, 99] = some [0x30, 99] := by decide +kernel
example : run uintOr.code [0xf0, 0x3c, 99] = some [0xfc, 99] := by decide +kernel
example : run uintXor.code [0xf0, 0x3c, 99] = some [0xcc, 99] := by decide +kernel

/-- info: 'Solidity.Backend.Scalar.uintAnd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uintAnd
/-- info: 'Solidity.Backend.Scalar.uintOr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uintOr
/-- info: 'Solidity.Backend.Scalar.uintXor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms uintXor


#print axioms uintNot

end Solidity.Backend.Scalar
