import SolidityBridge.Arith.NarrowChecked
import SolidityBridge.Arith.NarrowBitwise
import SolidityBridge.Arith.Shifts

namespace Solidity.Bridge.Arith

theorem uint_div_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.div.evalT rfl (unsignedN hn x) (unsignedN hn y)).map Subtype.val =
      if y.toNat = 0 then none else some ((x / y).toNat : Int) := by
  rw [uint_div_exact, unsignedN_word, unsignedN_word, BitVec.toNat_udiv,
    unsignedN_extend hn, unsignedN_extend hn]
  simp only [unsignedN, Int.natCast_eq_zero, BitVec.toNat_udiv]

theorem uint_mod_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.mod.evalT rfl (unsignedN hn x) (unsignedN hn y)).map Subtype.val =
      if y.toNat = 0 then none else some ((x % y).toNat : Int) := by
  rw [uint_mod_exact, unsignedN_word, unsignedN_word, BitVec.toNat_umod,
    unsignedN_extend hn, unsignedN_extend hn]
  simp only [unsignedN, Int.natCast_eq_zero, BitVec.toNat_umod]

theorem int_wordN_check {n : Nat} (hn : n ≤ 256) (x : BitVec n) :
    (PrimTy.int.ofInt? x.toInt).map Subtype.val = some x.toInt := by
  rw [int_check, if_pos]
  simpa only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] using
    (signedN hn x).property

/-- Signed remainder is srem, at every inhabited source width, with zero explicit. -/
theorem int_mod_all_widths {n : Nat} (hn : n ≤ 256) (x y : BitVec n) :
    (BinOp.mod.evalT rfl (signedN hn x) (signedN hn y)).map Subtype.val =
      if y.toInt = 0 then none else some ((x.srem y).toInt) := by
  change ((if y.toInt = 0 then none else some (x.toInt.tmod y.toInt)).bind
    PrimTy.int.ofInt?).map Subtype.val = _
  split
  · rfl
  · simp only [Option.bind_some]
    rw [← BitVec.toInt_srem]
    exact int_wordN_check hn _

/-- Checked signed division: zero, primitive 256-bit failure and narrow guard failure are distinct. -/
theorem int_div_checked_all_widths {n : Nat} (hn0 : 0 < n) (hn : n ≤ 256)
    (failure : THalt) (x y : BitVec n) :
    intWidthResult n failure (TRes.ofOpt (BinOp.div.evalT rfl (signedN hn x) (signedN hn y))) =
      if y.toInt = 0 then .error .revert else
      if x.toInt.tdiv y.toInt = (x.sdiv y).toInt then .ok (x.toInt.tdiv y.toInt) else
      if x.toInt.tdiv y.toInt = (BitVec.ofInt 256 (x.toInt.tdiv y.toInt)).toInt
      then .error failure else .error .revert := by
  change intWidthResult n failure (TRes.ofOpt
    ((if y.toInt = 0 then none else some (x.toInt.tdiv y.toInt)).bind PrimTy.int.ofInt?)) = _
  split
  · rfl
  · simp only [Option.bind_some]
    rw [int_checked_width n hn0 hn]
    simp only [BitVec.toInt_sdiv, BitVec.toInt_ofInt]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_div_all_widths
#print axioms Solidity.Bridge.Arith.uint_mod_all_widths
#print axioms Solidity.Bridge.Arith.int_mod_all_widths
#print axioms Solidity.Bridge.Arith.int_div_checked_all_widths
