import SolidityBridge.Arith.Basic

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
