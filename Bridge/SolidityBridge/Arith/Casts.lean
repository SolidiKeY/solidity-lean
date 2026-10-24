import SolidityBridge.Arith.Division

set_option maxRecDepth 2048

namespace Solidity.Bridge.Arith

theorem unsigned_to_signed_value (x : BitVec 256) :
    (if (x.toNat : Int) < Semantics.intBound then (x.toNat : Int)
      else (x.toNat : Int) - Semantics.uintBound) = x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  have hc : (x.toNat : Int) < Semantics.intBound ↔ 2 * x.toNat < 2 ^ 256 := by
    simp only [Semantics.intBound, Nat.cast_pow, Nat.cast_ofNat]
    omega
  simp only [hc, Semantics.uintBound]

theorem uint_toInt_bitvec (x : BitVec 256) :
    (UnOp.toInt.evalT rfl (unsigned x)).map Subtype.val = some x.toInt := by
  change (PrimTy.int.ofInt? (if (x.toNat : Int) < Semantics.intBound then (x.toNat : Int)
    else (x.toNat : Int) - Semantics.uintBound)).map Subtype.val = _
  rw [unsigned_to_signed_value]
  exact int_word_check _

theorem int_toUint_bitvec (x : PrimTy.int.Denote) :
    (UnOp.toUint.evalT rfl x).map Subtype.val =
      some ((BitVec.ofInt 256 x.val).toNat : Int) := by
  rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  exact uint_mod _

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_toInt_bitvec
#print axioms Solidity.Bridge.Arith.int_toUint_bitvec
