import SolidityBridge.RoadmapV15.P10.Modular
import Solidity.Backend.Scalar.Select

/-! Existing word-ring representation and actual wrapping arithmetic selection.
This consumer does not replace checked arithmetic by wrapping arithmetic. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem wrapping_add_word (a b : Scalar.Word) :
    UInt256.add ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(a + b).toFin⟩ := by
  rfl

theorem wrapping_sub_word (a b : Scalar.Word) :
    UInt256.sub ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(a - b).toFin⟩ := by
  rfl

theorem wrapping_mul_word (a b : Scalar.Word) :
    UInt256.mul ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(a * b).toFin⟩ := by
  rfl

theorem wrapping_arithmetic_selection :
    Scalar.selectBinary .addW .uint rfl = some Scalar.wrappingAdd ∧
    Scalar.wrappingAdd.code = [.op .ADD] ∧
    Scalar.selectBinary .subW .uint rfl = some Scalar.wrappingSub ∧
    Scalar.wrappingSub.code = [.op .SUB] ∧
    Scalar.selectBinary .mulW .uint rfl = some Scalar.wrappingMul ∧
    Scalar.wrappingMul.code = [.op .MUL] := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms wrapping_add_word
#print axioms wrapping_sub_word
#print axioms wrapping_mul_word
#print axioms wrapping_arithmetic_selection
end SolidityBridge.RoadmapV15.P10
