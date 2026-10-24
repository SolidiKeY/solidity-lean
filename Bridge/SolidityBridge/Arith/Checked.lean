import SolidityBridge.Arith.Wrapping

namespace Solidity.Bridge.Arith

/-- Actual checked uint add; failure iff the mathematical result differs from the word. -/
theorem uint_add_exact (x y : PrimTy.uint.Denote) :
    (BinOp.add.evalT rfl x y).map Subtype.val =
      if x.val + y.val = ((BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toNat : Int) then some (x.val + y.val) else none := by
  simpa only [BitVec.ofInt_add] using uint_check_bitvec (x.val + y.val)

/-- Actual checked uint sub; failure iff the mathematical result differs from the word. -/
theorem uint_sub_exact (x y : PrimTy.uint.Denote) :
    (BinOp.sub.evalT rfl x y).map Subtype.val =
      if x.val - y.val = ((BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toNat : Int) then some (x.val - y.val) else none := by
  simpa only [ofInt_sub 256] using uint_check_bitvec (x.val - y.val)

/-- Actual checked uint mul; failure iff the mathematical result differs from the word. -/
theorem uint_mul_exact (x y : PrimTy.uint.Denote) :
    (BinOp.mul.evalT rfl x y).map Subtype.val =
      if x.val * y.val = ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toNat : Int) then some (x.val * y.val) else none := by
  simpa only [BitVec.ofInt_mul] using uint_check_bitvec (x.val * y.val)

/-- Actual checked int add; failure iff the mathematical result differs from the word. -/
theorem int_add_exact (x y : PrimTy.int.Denote) :
    (BinOp.add.evalT rfl x y).map Subtype.val =
      if x.val + y.val = ((BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toInt : Int) then some (x.val + y.val) else none := by
  simpa only [BitVec.ofInt_add] using int_check_bitvec (x.val + y.val)

/-- Actual checked int sub; failure iff the mathematical result differs from the word. -/
theorem int_sub_exact (x y : PrimTy.int.Denote) :
    (BinOp.sub.evalT rfl x y).map Subtype.val =
      if x.val - y.val = ((BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toInt : Int) then some (x.val - y.val) else none := by
  simpa only [ofInt_sub 256] using int_check_bitvec (x.val - y.val)

/-- Actual checked int mul; failure iff the mathematical result differs from the word. -/
theorem int_mul_exact (x y : PrimTy.int.Denote) :
    (BinOp.mul.evalT rfl x y).map Subtype.val =
      if x.val * y.val = ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toInt : Int) then some (x.val * y.val) else none := by
  simpa only [BitVec.ofInt_mul] using int_check_bitvec (x.val * y.val)

theorem int_neg_exact (x : PrimTy.int.Denote) :
    (UnOp.neg.evalT rfl x).map Subtype.val =
      if -x.val = (-BitVec.ofInt 256 x.val).toInt then some (-x.val) else none := by
  simpa only [BitVec.ofInt_neg] using int_check_bitvec (-x.val)

theorem uint_pow_exact (x y : PrimTy.uint.Denote) :
    (BinOp.pow.evalT rfl x y).map Subtype.val =
      if x.val ^ y.val.toNat = (((BitVec.ofInt 256 x.val) ^ y.val.toNat).toNat : Int)
      then some (x.val ^ y.val.toNat) else none := by
  change ((if y.val < 0 then none else some (x.val ^ y.val.toNat)).bind
    PrimTy.uint.ofInt?).map Subtype.val = _
  rw [if_neg (not_lt.mpr (PrimTy.uint_nonneg y))]
  simp only [Option.bind_some]
  simpa only [ofInt_pow] using uint_check_bitvec (x.val ^ y.val.toNat)

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_add_exact
#print axioms Solidity.Bridge.Arith.uint_sub_exact
#print axioms Solidity.Bridge.Arith.uint_mul_exact
#print axioms Solidity.Bridge.Arith.int_add_exact
#print axioms Solidity.Bridge.Arith.int_sub_exact
#print axioms Solidity.Bridge.Arith.int_mul_exact
#print axioms Solidity.Bridge.Arith.int_neg_exact
#print axioms Solidity.Bridge.Arith.uint_pow_exact
