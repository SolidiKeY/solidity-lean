import SolidityBridge.Arith.Basic

namespace Solidity.Bridge.Arith

/-- Uniform in the word width, including every Solidity width. -/
theorem ofInt_sub (w : Nat) (x y : Int) :
    BitVec.ofInt w (x - y) = BitVec.ofInt w x - BitVec.ofInt w y := by
  rw [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- Uniform in width and exponent; no bound on the mathematical power. -/
theorem ofInt_pow (w : Nat) (x : Int) (k : Nat) :
    BitVec.ofInt w (x ^ k) = BitVec.ofInt w x ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, BitVec.pow_succ, BitVec.ofInt_mul, ih]

theorem uint_subW_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.subW.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toNat : Int) := by
  rw [← ofInt_sub, BitVec.toNat_ofInt, Int.toNat_of_nonneg
    (Int.emod_nonneg _ (by omega))]
  exact uint_mod _

theorem uint_powW_bitvec (x y : PrimTy.uint.Denote) :
    (BinOp.powW.evalT rfl x y).map Subtype.val =
      some (((BitVec.ofInt 256 x.val) ^ y.val.toNat).toNat : Int) := by
  change ((if y.val < 0 then none else some (x.val ^ y.val.toNat % Semantics.uintBound)).bind
    PrimTy.uint.ofInt?).map Subtype.val = _
  rw [if_neg (not_lt.mpr (PrimTy.uint_nonneg y))]
  simp only [Option.bind_some]
  rw [← ofInt_pow, BitVec.toNat_ofInt, Int.toNat_of_nonneg
    (Int.emod_nonneg _ (by omega))]
  exact uint_mod _

theorem uint_powW_zmod (x y : PrimTy.uint.Denote) :
    (BinOp.powW.evalT rfl x y).map (fun z => (z.val : ZMod (2 ^ 256))) =
      some ((x.val : ZMod (2 ^ 256)) ^ y.val.toNat) := by
  change ((if y.val < 0 then none else some (x.val ^ y.val.toNat % Semantics.uintBound)).bind
    PrimTy.uint.ofInt?).map _ = _
  rw [if_neg (not_lt.mpr (PrimTy.uint_nonneg y))]
  simp only [Option.bind_some]
  exact (uint_mod_map (fun n : Int => (n : ZMod (2 ^ 256))) (x.val ^ y.val.toNat)).trans
    (by simp only [Semantics.uintBound, ZMod.intCast_mod, Int.cast_pow])

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_subW_bitvec
#print axioms Solidity.Bridge.Arith.uint_powW_bitvec
#print axioms Solidity.Bridge.Arith.uint_powW_zmod
