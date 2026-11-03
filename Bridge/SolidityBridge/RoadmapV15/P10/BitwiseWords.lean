import SolidityBridge.RoadmapV15.P10.Modular

/-! Actual pinned bitwise words versus the existing intrinsic Scalar words.
Each reference modulo is discharged by the existing bounded result. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem bitwise_and_word (a b : Scalar.Word) :
    UInt256.land ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(a &&& b).toFin⟩ := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (a.toNat &&& b.toNat) % 2^256 = (a &&& b).toNat
  rw [←BitVec.toNat_and]
  exact Nat.mod_eq_of_lt (a &&& b).isLt

theorem bitwise_or_word (a b : Scalar.Word) :
    UInt256.lor ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(a ||| b).toFin⟩ := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (a.toNat ||| b.toNat) % 2^256 = (a ||| b).toNat
  rw [←BitVec.toNat_or]
  exact Nat.mod_eq_of_lt (a ||| b).isLt

theorem bitwise_xor_word (a b : Scalar.Word) :
    UInt256.xor ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(a ^^^ b).toFin⟩ := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (a.toNat ^^^ b.toNat) % 2^256 = (a ^^^ b).toNat
  rw [←BitVec.toNat_xor]
  exact Nat.mod_eq_of_lt (a ^^^ b).isLt

#print axioms bitwise_and_word
#print axioms bitwise_or_word
#print axioms bitwise_xor_word
end SolidityBridge.RoadmapV15.P10
