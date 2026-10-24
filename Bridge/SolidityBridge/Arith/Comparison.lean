import SolidityBridge.Arith.Basic

namespace Solidity.Bridge.Arith

theorem uint_lt_bitvec (x y : BitVec 256) :
    BinOp.lt.evalT rfl (unsigned x) (unsigned y) = some (x.ult y) := by
  simp only [BinOp.evalT, BinOp.evalNum, unsigned, BitVec.ult, Int.ofNat_lt]

theorem uint_gt_bitvec (x y : BitVec 256) :
    BinOp.gt.evalT rfl (unsigned x) (unsigned y) = some (y.ult x) := by
  simp only [BinOp.evalT, BinOp.evalNum, unsigned, BitVec.ult, Int.ofNat_lt]

theorem uint_le_bitvec (x y : BitVec 256) :
    BinOp.le.evalT rfl (unsigned x) (unsigned y) = some (x.ule y) := by
  simp only [BinOp.evalT, BinOp.evalNum, unsigned, BitVec.ule, Int.ofNat_le]

theorem uint_ge_bitvec (x y : BitVec 256) :
    BinOp.ge.evalT rfl (unsigned x) (unsigned y) = some (y.ule x) := by
  simp only [BinOp.evalT, BinOp.evalNum, unsigned, BitVec.ule, Int.ofNat_le]

theorem uint_eqB_bitvec (x y : BitVec 256) :
    BinOp.eqB.evalT rfl (unsigned x) (unsigned y) = some (decide (x = y)) := by
  simp only [BinOp.evalT, BinOp.evalNum, unsigned, Int.ofNat_inj, BitVec.toNat_inj]

theorem uint_neB_bitvec (x y : BitVec 256) :
    BinOp.neB.evalT rfl (unsigned x) (unsigned y) = some (!decide (x = y)) := by
  simp only [BinOp.evalT, BinOp.evalNum, unsigned, Int.ofNat_inj, BitVec.toNat_inj]

theorem int_lt_bitvec (x y : BitVec 256) :
    BinOp.lt.evalT rfl (signed x) (signed y) = some (x.slt y) := by
  simp only [BinOp.evalT, BinOp.evalNum, signed, BitVec.slt]

theorem int_gt_bitvec (x y : BitVec 256) :
    BinOp.gt.evalT rfl (signed x) (signed y) = some (y.slt x) := by
  simp only [BinOp.evalT, BinOp.evalNum, signed, BitVec.slt]

theorem int_le_bitvec (x y : BitVec 256) :
    BinOp.le.evalT rfl (signed x) (signed y) = some (x.sle y) := by
  simp only [BinOp.evalT, BinOp.evalNum, signed, BitVec.sle]

theorem int_ge_bitvec (x y : BitVec 256) :
    BinOp.ge.evalT rfl (signed x) (signed y) = some (y.sle x) := by
  simp only [BinOp.evalT, BinOp.evalNum, signed, BitVec.sle]

theorem int_eqB_bitvec (x y : BitVec 256) :
    BinOp.eqB.evalT rfl (signed x) (signed y) = some (decide (x = y)) := by
  simp only [BinOp.evalT, BinOp.evalNum, signed, BitVec.toInt_inj]

theorem int_neB_bitvec (x y : BitVec 256) :
    BinOp.neB.evalT rfl (signed x) (signed y) = some (!decide (x = y)) := by
  simp only [BinOp.evalT, BinOp.evalNum, signed, BitVec.toInt_inj]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.uint_lt_bitvec
#print axioms Solidity.Bridge.Arith.uint_gt_bitvec
#print axioms Solidity.Bridge.Arith.uint_le_bitvec
#print axioms Solidity.Bridge.Arith.uint_ge_bitvec
#print axioms Solidity.Bridge.Arith.uint_eqB_bitvec
#print axioms Solidity.Bridge.Arith.uint_neB_bitvec
#print axioms Solidity.Bridge.Arith.int_lt_bitvec
#print axioms Solidity.Bridge.Arith.int_gt_bitvec
#print axioms Solidity.Bridge.Arith.int_le_bitvec
#print axioms Solidity.Bridge.Arith.int_ge_bitvec
#print axioms Solidity.Bridge.Arith.int_eqB_bitvec
#print axioms Solidity.Bridge.Arith.int_neB_bitvec
