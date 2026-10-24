import SolidityBridge.Arith.Casts

namespace Solidity.Bridge.Arith

/-- The core's nonnegative fast path reads the same words as BitVec. -/
theorem uint_bitwise_value (f : Nat → Nat → Nat) (x y : PrimTy.uint.Denote) :
    Semantics.uintBitwise f x.val y.val =
      (f (BitVec.ofInt 256 x.val).toNat (BitVec.ofInt 256 y.val).toNat : Int) := by
  have hx : x.val = (x.val.toNat : Int) := (Int.toNat_of_nonneg (PrimTy.uint_nonneg x)).symm
  have hy : y.val = (y.val.toNat : Int) := (Int.toNat_of_nonneg (PrimTy.uint_nonneg y)).symm
  have hxn : (BitVec.ofInt 256 x.val).toNat = x.val.toNat := by
    simpa only [Int.toNat_natCast] using congrArg Int.toNat (uint_decode x)
  have hyn : (BitVec.ofInt 256 y.val).toNat = y.val.toNat := by
    simpa only [Int.toNat_natCast] using congrArg Int.toNat (uint_decode y)
  rw [hxn, hyn]
  conv_lhs => rw [hx, hy, Semantics.uintBitwise_natCast]

theorem uint_band_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.band.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val &&& BitVec.ofInt 256 y.val).toNat : Int) := by
  change (PrimTy.uint.ofInt? (Semantics.uintBitwise (· &&& ·) x.val y.val)).map Subtype.val = _
  rw [uint_bitwise_value, ← BitVec.toNat_and]
  exact uint_word_check _

theorem uint_bor_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.bor.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val ||| BitVec.ofInt 256 y.val).toNat : Int) := by
  change (PrimTy.uint.ofInt? (Semantics.uintBitwise (· ||| ·) x.val y.val)).map Subtype.val = _
  rw [uint_bitwise_value, ← BitVec.toNat_or]
  exact uint_word_check _

theorem uint_bxor_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.bxor.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val ^^^ BitVec.ofInt 256 y.val).toNat : Int) := by
  change (PrimTy.uint.ofInt? (Semantics.uintBitwise (· ^^^ ·) x.val y.val)).map Subtype.val = _
  rw [uint_bitwise_value, ← BitVec.toNat_xor]
  exact uint_word_check _

theorem wordOf_bitvec (x : BitVec 256) : Semantics.wordOf x.toInt = x.toNat := by
  have h : (BitVec.ofInt 256 x.toInt).toNat = x.toNat :=
    congrArg BitVec.toNat (BitVec.ofInt_toInt (x := x))
  simpa only [Semantics.wordOf, BitVec.toNat_ofInt] using h

theorem signedOf_bitvec (x : BitVec 256) : Semantics.signedOf x.toNat = x.toInt := by
  simpa only [Semantics.signedOf, Semantics.intBound, Semantics.uintBound, Int.ofNat_lt]
    using unsigned_to_signed_value x

theorem uintBitwise_cases (f : Nat → Nat → Nat) (x y : Int) :
    Semantics.uintBitwise f x y =
      if 0 ≤ x ∧ 0 ≤ y then (f x.toNat y.toNat : Int)
      else Semantics.signedOf (f (Semantics.wordOf x) (Semantics.wordOf y)) := by
  cases x <;> cases y <;> rfl

/-- Uniform word correspondence for the three signed bitwise constructors. -/
theorem signed_bitwise_value (f : Nat → Nat → Nat)
    (g : BitVec 256 → BitVec 256 → BitVec 256)
    (hg : ∀ x y, (g x y).toNat = f x.toNat y.toNat)
    (hm : ∀ x y, x.msb = false → y.msb = false → (g x y).msb = false)
    (x y : BitVec 256) :
    Semantics.uintBitwise f x.toInt y.toInt = (g x y).toInt := by
  rw [uintBitwise_cases]
  by_cases hp : 0 ≤ x.toInt ∧ 0 ≤ y.toInt
  · have hx : x.msb = false := by
      cases h : x.msb
      · rfl
      · exact False.elim ((not_le_of_gt (BitVec.toInt_neg_of_msb_true h)) hp.1)
    have hy : y.msb = false := by
      cases h : y.msb
      · rfl
      · exact False.elim ((not_le_of_gt (BitVec.toInt_neg_of_msb_true h)) hp.2)
    rw [if_pos hp, BitVec.toNat_toInt_of_msb x hx, BitVec.toNat_toInt_of_msb y hy,
      ← hg, BitVec.toInt_eq_toNat_of_msb (hm x y hx hy)]
  · rw [if_neg hp, wordOf_bitvec, wordOf_bitvec, ← hg, signedOf_bitvec]

theorem int_band_bitvec (x y : BitVec 256) :
    (BinOp.band.evalT rfl (signed x) (signed y)).map Subtype.val =
      some ((x &&& y).toInt) := by
  change (PrimTy.int.ofInt? (Semantics.uintBitwise (· &&& ·) x.toInt y.toInt)).map Subtype.val = _
  rw [signed_bitwise_value (· &&& ·) (· &&& ·) BitVec.toNat_and]
  · exact int_word_check _
  · intro a b ha hb
    simp only [BitVec.msb_and, ha, hb, Bool.false_and]

theorem int_bor_bitvec (x y : BitVec 256) :
    (BinOp.bor.evalT rfl (signed x) (signed y)).map Subtype.val =
      some ((x ||| y).toInt) := by
  change (PrimTy.int.ofInt? (Semantics.uintBitwise (· ||| ·) x.toInt y.toInt)).map Subtype.val = _
  rw [signed_bitwise_value (· ||| ·) (· ||| ·) BitVec.toNat_or]
  · exact int_word_check _
  · intro a b ha hb
    simp only [BitVec.msb_or, ha, hb, Bool.or_false]

theorem int_bxor_bitvec (x y : BitVec 256) :
    (BinOp.bxor.evalT rfl (signed x) (signed y)).map Subtype.val =
      some ((x ^^^ y).toInt) := by
  change (PrimTy.int.ofInt? (Semantics.uintBitwise (· ^^^ ·) x.toInt y.toInt)).map Subtype.val = _
  rw [signed_bitwise_value (· ^^^ ·) (· ^^^ ·) BitVec.toNat_xor]
  · exact int_word_check _
  · intro a b ha hb
    simp only [BitVec.msb_xor, ha, hb, Bool.xor_false]

theorem uint_bnot_bitvec (x : PrimTy.uint.Denote) :
    (UnOp.bnot.evalT rfl x).map Subtype.val =
      some ((~~~BitVec.ofInt 256 x.val).toNat : Int) := by
  have hb : (BitVec.ofInt 256 x.val).toNat < 2 ^ 256 := (BitVec.ofInt 256 x.val).isLt
  have hd : ((BitVec.ofInt 256 x.val).toNat : Int) = x.val := uint_decode x
  have hv : ((~~~BitVec.ofInt 256 x.val).toNat : Int) = Semantics.uintBound - 1 - x.val := by
    rw [BitVec.toNat_not]
    change ((2 ^ 256 - 1 - (BitVec.ofInt 256 x.val).toNat : Nat) : Int) =
      ((2 ^ 256 : Nat) : Int) - 1 - x.val
    omega
  change (PrimTy.uint.ofInt? (Semantics.uintBound - 1 - x.val)).map Subtype.val = _
  rw [← hv]
  exact uint_word_check _


end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_band_bitvec
#print axioms Solidity.Bridge.Arith.uint_bor_bitvec
#print axioms Solidity.Bridge.Arith.uint_bxor_bitvec

#print axioms Solidity.Bridge.Arith.int_band_bitvec
#print axioms Solidity.Bridge.Arith.int_bor_bitvec
#print axioms Solidity.Bridge.Arith.int_bxor_bitvec

#print axioms Solidity.Bridge.Arith.uint_bnot_bitvec
