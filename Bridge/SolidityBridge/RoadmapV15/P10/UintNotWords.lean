import SolidityBridge.RoadmapV15.P10.Modular
import Solidity.Backend.Scalar.Select

/-! Unsigned complement uses the existing word subtraction and selected certificate.
The fixed-entry private NOT row is prior coverage; this is consumer transport. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem uint_not_word (a : Scalar.Word) :
    UInt256.lnot ⟨a.toFin⟩ = ⟨(~~~a).toFin⟩ := by
  have h : ~~~a = BitVec.allOnes 256 - a := by
    rw [BitVec.not_eq_neg_add,←BitVec.neg_one_eq_allOnes]
    simp only [BitVec.sub_eq_add_neg]
    exact BitVec.add_comm _ _
  rw [h,BitVec.toFin_sub]
  rfl

theorem uint_not_selection :
    Scalar.selectUnary .bnot .uint rfl = some Scalar.uintNot ∧
      Scalar.uintNot.code = [.op .NOT] := by
  exact ⟨rfl,rfl⟩

#print axioms uint_not_word
#print axioms uint_not_selection
end SolidityBridge.RoadmapV15.P10
