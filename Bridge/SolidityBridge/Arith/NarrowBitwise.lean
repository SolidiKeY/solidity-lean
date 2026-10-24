import SolidityBridge.Arith.Bitwise
import SolidityBridge.Arith.NarrowWrapping

namespace Solidity.Bridge.Arith

theorem unsignedN_extend {n : Nat} (hn : n ≤ 256) (x : BitVec n) :
    (x.setWidth 256).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact x.isLt.trans_le (Nat.pow_le_pow_right (by decide) hn)

theorem signedN_extend {n : Nat} (hn : n ≤ 256) (x : BitVec n) :
    signed (x.signExtend 256) = signedN hn x :=
  Subtype.ext (BitVec.toInt_signExtend_of_le hn)

theorem uint_band_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.band.evalT rfl (unsignedN hn x) (unsignedN hn y)).map Subtype.val =
      some ((x &&& y).toNat : Int) := by
  rw [uint_band_bitvec, unsignedN_word, unsignedN_word, ← BitVec.setWidth_and,
    unsignedN_extend hn]

theorem uint_bor_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.bor.evalT rfl (unsignedN hn x) (unsignedN hn y)).map Subtype.val =
      some ((x ||| y).toNat : Int) := by
  rw [uint_bor_bitvec, unsignedN_word, unsignedN_word, ← BitVec.setWidth_or,
    unsignedN_extend hn]

theorem uint_bxor_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.bxor.evalT rfl (unsignedN hn x) (unsignedN hn y)).map Subtype.val =
      some ((x ^^^ y).toNat : Int) := by
  rw [uint_bxor_bitvec, unsignedN_word, unsignedN_word, ← BitVec.setWidth_xor,
    unsignedN_extend hn]

theorem int_band_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.band.evalT rfl (signedN hn x) (signedN hn y)).map Subtype.val =
      some ((x &&& y).toInt) := by
  rw [← signedN_extend hn x, ← signedN_extend hn y, int_band_bitvec,
    ← BitVec.signExtend_and, BitVec.toInt_signExtend_of_le hn]

theorem int_bor_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.bor.evalT rfl (signedN hn x) (signedN hn y)).map Subtype.val =
      some ((x ||| y).toInt) := by
  rw [← signedN_extend hn x, ← signedN_extend hn y, int_bor_bitvec,
    ← BitVec.signExtend_or, BitVec.toInt_signExtend_of_le hn]

theorem int_bxor_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.bxor.evalT rfl (signedN hn x) (signedN hn y)).map Subtype.val =
      some ((x ^^^ y).toInt) := by
  rw [← signedN_extend hn x, ← signedN_extend hn y, int_bxor_bitvec,
    ← BitVec.signExtend_xor, BitVec.toInt_signExtend_of_le hn]

/-- The actual narrow complement lowering is maxN -% x. -/
theorem uint_bnot_all_widths {n : Nat} (hn : n ≤ 256) (x : BitVec n) :
    (BinOp.subW.evalT rfl (unsignedN hn (~~~(0 : BitVec n))) (unsignedN hn x)).map
      Subtype.val = some ((~~~x).toNat : Int) := by
  have hp : (2 : Nat) ^ n ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hn
  have hv : ((~~~x).toNat : Int) =
      (unsignedN hn (~~~(0 : BitVec n))).val - (unsignedN hn x).val := by
    simp only [unsignedN, BitVec.toNat_not]
    have hz : (0 : BitVec n).toNat = 0 := rfl
    rw [hz]
    have hx : x.toNat < 2 ^ n := x.isLt
    omega
  change (PrimTy.uint.ofInt? (((unsignedN hn (~~~(0 : BitVec n))).val -
      (unsignedN hn x).val) % Semantics.uintBound)).map Subtype.val = _
  rw [← hv, uint_mod]
  have hm : ((~~~x).toNat : Int) % Semantics.uintBound = ((~~~x).toNat : Int) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr ((~~~x).isLt.trans_le hp))
  rw [hm]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_band_all_widths
#print axioms Solidity.Bridge.Arith.uint_bor_all_widths
#print axioms Solidity.Bridge.Arith.uint_bxor_all_widths
#print axioms Solidity.Bridge.Arith.int_band_all_widths
#print axioms Solidity.Bridge.Arith.int_bor_all_widths
#print axioms Solidity.Bridge.Arith.int_bxor_all_widths
#print axioms Solidity.Bridge.Arith.uint_bnot_all_widths
