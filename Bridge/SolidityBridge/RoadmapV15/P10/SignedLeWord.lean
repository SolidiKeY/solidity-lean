import SolidityBridge.RoadmapV15.P10.Modular
import SolidityBridge.ExternalEvm.SignedOps
import Solidity.Backend.Scalar.Select

/-! Consume the existing reserved signed-word bridge for the intLe emitter.
Signed comparison mathematics and the intrinsic source certificate are prior work. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem signed_gt_word (a b : Scalar.Word) :
    UInt256.sgt ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(Scalar.flag (decide (b.toInt < a.toInt))).toFin⟩ := by
  have ha : Solidity.Evm.sgn a.toFin.val = a.toInt := Scalar.signedOf_word a
  have hb : Solidity.Evm.sgn b.toFin.val = b.toInt := Scalar.signedOf_word b
  have encoded (x : Scalar.Word) : encode x.toFin = UInt256.mk x.toFin := by
    apply congrArg UInt256.mk
    apply Fin.ext
    rfl
  rw [UInt256.sgt,←encoded a,←encoded b,←signed_gt_bool a.toFin b.toFin,ha,hb]
  cases h : decide (b.toInt < a.toInt) <;> rfl

#print axioms signed_gt_word
end SolidityBridge.RoadmapV15.P10
