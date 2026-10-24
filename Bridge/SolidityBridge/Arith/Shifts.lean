import SolidityBridge.Arith.Division

namespace Solidity.Bridge.Arith.Shifts

private def one : PrimTy.int.Denote := ⟨1, by decide⟩
private def minusOne : PrimTy.int.Denote := ⟨-1, by decide⟩

/-- The core accepts a negative signed shift count and converts it to zero. -/
theorem core_negative_count :
    (BinOp.shr.evalT rfl one minusOne).map Subtype.val = some 1 := by
  decide +kernel

/-- Reading that count as its unsigned word instead shifts all bits out. -/
theorem bitvec_negative_count :
    ((BitVec.ofInt 256 1).sshiftRight' (BitVec.ofInt 256 (-1))).toInt = 0 := by
  rw [BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_of_msb_false (by decide),
    BitVec.ushiftRight_eq_zero (by decide)]
  rfl

/-- A minimal failure of the unqualified primitive word-shift correspondence. -/
example :
    (BinOp.shr.evalT rfl one minusOne).map Subtype.val ≠
      some (((BitVec.ofInt 256 1).sshiftRight' (BitVec.ofInt 256 (-1))).toInt) := by
  rw [core_negative_count, bitvec_negative_count]
  decide

end Solidity.Bridge.Arith.Shifts

#print axioms Solidity.Bridge.Arith.Shifts.core_negative_count
#print axioms Solidity.Bridge.Arith.Shifts.bitvec_negative_count

namespace Solidity.Bridge.Arith

theorem uint_shl_value (x y : PrimTy.uint.Denote) :
    (if y.val < 256 then x.val * 2 ^ y.val.toNat % Semantics.uintBound else 0) =
      ((BitVec.ofInt 256 x.val <<< y.val.toNat).toNat : Int) := by
  by_cases hn : y.val < 256
  · rw [if_pos hn, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Int.natCast_emod,
      Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat, uint_decode]
    rfl
  · rw [if_neg hn, BitVec.shiftLeft_eq_zero (by omega)]
    rfl

theorem uint_shl_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.shl.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val <<< y.val.toNat).toNat : Int) := by
  change (PrimTy.uint.ofInt? (if y.val < 256 then x.val * 2 ^ y.val.toNat % Semantics.uintBound else 0)).map Subtype.val = _
  rw [uint_shl_value]
  exact uint_word_check _

theorem uint_shr_value (x y : PrimTy.uint.Denote) :
    (if y.val < 256 then x.val / 2 ^ y.val.toNat else 0) =
      ((BitVec.ofInt 256 x.val >>> y.val.toNat).toNat : Int) := by
  by_cases hn : y.val < 256
  · rw [if_pos hn, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Int.natCast_ediv, Int.natCast_pow, Nat.cast_ofNat, uint_decode]
  · rw [if_neg hn, BitVec.ushiftRight_eq_zero (by omega)]
    rfl

theorem uint_shr_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.shr.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val >>> y.val.toNat).toNat : Int) := by
  change (PrimTy.uint.ofInt? (if y.val < 256 then x.val / 2 ^ y.val.toNat
    else if x.val < 0 then -1 else 0)).map Subtype.val = _
  rw [if_neg (not_lt.mpr (PrimTy.uint_nonneg x)), uint_shr_value]
  exact uint_word_check _

theorem int_decode (x : PrimTy.int.Denote) : (BitVec.ofInt 256 x.val).toInt = x.val := by
  apply Eq.symm
  apply (int_roundtrip x.val).mpr
  simpa only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] using x.property

/-- Exact natural-count characterization, including the core's negative-count conversion. -/
theorem int_shr_value (x : PrimTy.int.Denote) (n : Int) :
    (if n < 256 then x.val / 2 ^ n.toNat else if x.val < 0 then -1 else 0) =
      ((BitVec.ofInt 256 x.val).sshiftRight n.toNat).toInt := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, int_decode]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  by_cases hn : n < 256
  · rw [if_pos hn]
  · rw [if_neg hn]
    have hp : (2 : Int) ^ 256 ≤ 2 ^ n.toNat := by
      have hn' : 256 ≤ n.toNat := by omega
      have hpow : (2 : Nat) ^ 256 ≤ 2 ^ n.toNat := Nat.pow_le_pow_right (by decide) hn'
      exact_mod_cast hpow
    have hx : -(2 : Int) ^ 255 ≤ x.val ∧ x.val < 2 ^ 255 := by
      simpa only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] using x.property
    by_cases hs : x.val < 0
    · rw [if_pos hs]
      exact (Int.ediv_eq_neg_one_of_neg_of_le hs (by omega)).symm
    · rw [if_neg hs]
      exact (Int.ediv_eq_zero_of_lt (by omega) (by omega)).symm

theorem int_shr_nat_bitvec (x y : PrimTy.int.Denote) :
    (BinOp.shr.evalT rfl x y).map Subtype.val =
      some (((BitVec.ofInt 256 x.val).sshiftRight y.val.toNat).toInt) := by
  change (PrimTy.int.ofInt? (if y.val < 256 then x.val / 2 ^ y.val.toNat
    else if x.val < 0 then -1 else 0)).map Subtype.val = _
  rw [int_shr_value]
  exact int_word_check _

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_shl_bitvec
#print axioms Solidity.Bridge.Arith.uint_shr_bitvec
#print axioms Solidity.Bridge.Arith.int_shr_nat_bitvec
