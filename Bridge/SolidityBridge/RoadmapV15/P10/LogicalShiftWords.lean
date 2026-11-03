import SolidityBridge.RoadmapV15.P10.Modular
import Solidity.Backend.Scalar.Select

/-! Existing logical shift words, saturation and typed source selections.
These equations are auxiliary prior-covered word transport, not new semantics. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem logical_shl_word (count value : Scalar.Word) :
    UInt256.shiftLeft ⟨value.toFin⟩ ⟨count.toFin⟩ =
      ⟨(if count.toNat < 256 then value <<< count.toNat else 0).toFin⟩ := by
  unfold UInt256.shiftLeft
  by_cases h : count.toNat < 256
  · rw [if_pos h,if_neg (by change ¬count.toNat ≥ 256;omega)]
    apply congrArg UInt256.mk
    apply Fin.ext
    change (value.toNat <<< count.toNat) % 2^256 = (value <<< count.toNat).toNat
    exact BitVec.toNat_shiftLeft.symm
  · rw [if_neg h,if_pos (by change count.toNat ≥ 256;omega)]
    rfl

theorem logical_shr_word (count value : Scalar.Word) :
    UInt256.shiftRight ⟨value.toFin⟩ ⟨count.toFin⟩ =
      ⟨(if count.toNat < 256 then value >>> count.toNat else 0).toFin⟩ := by
  unfold UInt256.shiftRight
  by_cases h : count.toNat < 256
  · rw [if_pos h,if_neg (by change ¬count.toNat ≥ 256;omega)]
    apply congrArg UInt256.mk
    apply Fin.ext
    change (value.toNat >>> count.toNat) % 2^256 = (value >>> count.toNat).toNat
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) value.isLt)
  · rw [if_neg h,if_pos (by change count.toNat ≥ 256;omega)]
    rfl

#print axioms logical_shl_word
#print axioms logical_shr_word
end SolidityBridge.RoadmapV15.P10
