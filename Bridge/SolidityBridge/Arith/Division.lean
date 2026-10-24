import SolidityBridge.Arith.Basic

set_option maxRecDepth 2048

namespace Solidity.Bridge.Arith

theorem uint_word_check (x : BitVec 256) :
    (PrimTy.uint.ofInt? x.toNat).map Subtype.val = some (x.toNat : Int) := by
  rw [uint_check, if_pos]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr x.isLt⟩

theorem int_word_check (x : BitVec 256) :
    (PrimTy.int.ofInt? x.toInt).map Subtype.val = some x.toInt := by
  rw [int_check, if_pos]
  exact ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

/-- The zero divisor and signed division overflow remain explicit. -/
theorem int_div_exact (x y : BitVec 256) :
    (BinOp.div.evalT rfl (signed x) (signed y)).map Subtype.val =
      if y.toInt = 0 then none else
      if x.toInt.tdiv y.toInt = (x.sdiv y).toInt
      then some (x.toInt.tdiv y.toInt) else none := by
  change ((if y.toInt = 0 then none else some (x.toInt.tdiv y.toInt)).bind
    PrimTy.int.ofInt?).map Subtype.val = _
  split
  · rfl
  · simp only [Option.bind_some]
    simpa only [BitVec.toInt_ofInt, BitVec.toInt_sdiv] using
      int_check_bitvec (x.toInt.tdiv y.toInt)

/-- Solidity's signed remainder rounds toward zero: the reference is srem. -/
theorem int_mod_exact (x y : BitVec 256) :
    (BinOp.mod.evalT rfl (signed x) (signed y)).map Subtype.val =
      if y.toInt = 0 then none else some (x.srem y).toInt := by
  change ((if y.toInt = 0 then none else some (x.toInt.tmod y.toInt)).bind
    PrimTy.int.ofInt?).map Subtype.val = _
  split
  · rfl
  · simp only [Option.bind_some]
    rw [← BitVec.toInt_srem]
    exact int_word_check _

theorem uint_decode (x : PrimTy.uint.Denote) :
    ((BitVec.ofInt 256 x.val).toNat : Int) = x.val := by
  apply Eq.symm
  apply (uint_roundtrip x.val).mpr
  simpa only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] using x.property

theorem uint_div_word (x y : PrimTy.uint.Denote) :
    x.val.tdiv y.val = ((BitVec.ofInt 256 x.val / BitVec.ofInt 256 y.val).toNat : Int) := by
  rw [BitVec.toNat_udiv, Int.natCast_ediv, uint_decode, uint_decode]
  exact Int.tdiv_eq_ediv_of_nonneg (PrimTy.uint_nonneg x)

theorem uint_mod_word (x y : PrimTy.uint.Denote) :
    x.val.tmod y.val = ((BitVec.ofInt 256 x.val % BitVec.ofInt 256 y.val).toNat : Int) := by
  rw [BitVec.toNat_umod, Int.natCast_emod, uint_decode, uint_decode]
  exact Int.tmod_eq_emod_of_nonneg (PrimTy.uint_nonneg x)

theorem uint_div_exact (x y : PrimTy.uint.Denote) :
    (BinOp.div.evalT rfl x y).map Subtype.val =
      if y.val = 0 then none else
      some ((BitVec.ofInt 256 x.val / BitVec.ofInt 256 y.val).toNat : Int) := by
  change ((if y.val = 0 then none else some (x.val.tdiv y.val)).bind
    PrimTy.uint.ofInt?).map Subtype.val = _
  split
  · rfl
  · simp only [Option.bind_some]
    rw [uint_div_word]
    exact uint_word_check _

theorem uint_mod_exact (x y : PrimTy.uint.Denote) :
    (BinOp.mod.evalT rfl x y).map Subtype.val =
      if y.val = 0 then none else
      some ((BitVec.ofInt 256 x.val % BitVec.ofInt 256 y.val).toNat : Int) := by
  change ((if y.val = 0 then none else some (x.val.tmod y.val)).bind
    PrimTy.uint.ofInt?).map Subtype.val = _
  split
  · rfl
  · simp only [Option.bind_some]
    rw [uint_mod_word]
    exact uint_word_check _

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.int_div_exact
#print axioms Solidity.Bridge.Arith.int_mod_exact
#print axioms Solidity.Bridge.Arith.uint_div_exact
#print axioms Solidity.Bridge.Arith.uint_mod_exact
