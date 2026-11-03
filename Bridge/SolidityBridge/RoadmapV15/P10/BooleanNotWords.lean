import SolidityBridge.RoadmapV15.P10.Modular
import Solidity.Backend.Scalar.Select

/-! ISZERO word transport and the actual typed Boolean-not selection.
The typed input is an already evaluated canonical Boolean value. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem iszero_word (a : Scalar.Word) :
    UInt256.isZero ⟨a.toFin⟩ = ⟨(Scalar.flag (a == 0)).toFin⟩ := by
  have test : UInt256.eq0 (UInt256.mk a.toFin) = (a == 0) := by
    simp only [UInt256.eq0,instBEqUInt256,instBEqUInt256.beq]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Fin.ext_iff,BitVec.toNat_eq]
    rfl
  rw [UInt256.isZero,test]
  cases h : a == 0 <;> rfl

theorem boolean_not_word (b : PrimTy.bool.Denote) :
    Scalar.flag (Scalar.encodeValue .bool b == 0) = Scalar.encodeValue .bool (!b) := by
  cases b <;> rfl

theorem boolean_not_selection :
    Scalar.selectUnary .not .bool rfl = some Scalar.booleanNot ∧
      Scalar.booleanNot.code = [.op .ISZERO] := by
  exact ⟨rfl,rfl⟩

#print axioms iszero_word
#print axioms boolean_not_word
#print axioms boolean_not_selection
end SolidityBridge.RoadmapV15.P10
