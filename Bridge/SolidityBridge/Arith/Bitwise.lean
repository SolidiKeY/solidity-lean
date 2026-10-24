import SolidityBridge.Arith.Division

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

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_band_bitvec
#print axioms Solidity.Bridge.Arith.uint_bor_bitvec
#print axioms Solidity.Bridge.Arith.uint_bxor_bitvec
