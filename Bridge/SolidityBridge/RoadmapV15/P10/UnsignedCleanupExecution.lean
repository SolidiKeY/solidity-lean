import SolidityBridge.RoadmapV15.P10.UnsignedCleanupLayout
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Both actual emitted unsignedCode instructions, retaining the complete charged
State and X continuation. No source-origin or whole-program adequacy claim. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- No desired execution or intermediate frame is supplied: both steps are derived. -/
theorem unsigned_cleanup_execution :
∀ (seed : EvmYul.EVM.State) (before after : Solidity.Backend.Program) (w : Fin 32)
 (x : Solidity.Backend.Scalar.Word) (tail : Solidity.Backend.Scalar.Stack)
 (_fits : (Solidity.Backend.encode (before ++ [Solidity.Backend.Scalar.pushWord (SolidityBridge.RoadmapV15.P10.unsignedCleanupMask w)])).length < EvmYul.UInt256.size)
 (_room : tail.length+2 ≤ 1024) (_gas : 6 ≤ seed.gasAvailable.toNat) (fuel : Nat),
 let input := SolidityBridge.RoadmapV15.P10.unsignedPushInput seed before after w (x::tail);
 let pushed := SolidityBridge.RoadmapV15.P10.unsignedPushResult seed before after w (x::tail);
 let next := (Solidity.Evm.External.Assembly.chargedPrepare pushed 3).replaceStackAndIncrPC
  ((Solidity.Backend.Scalar.unsignedClean w x::tail).map (fun y => EvmYul.UInt256.mk y.toFin));
 Solidity.Backend.Scalar.run (Solidity.Backend.Scalar.unsignedCode w) (x::tail) = some (Solidity.Backend.Scalar.unsignedClean w x::tail) ∧
 Solidity.Evm.External.Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
 EvmYul.EVM.X (fuel+3) #[] input = EvmYul.EVM.X (fuel+1) #[] next
 := by
  intro seed before after w x tail fits room gas fuel
  dsimp only
  have length : (Backend.encode (before ++ [Scalar.pushWord (unsignedCleanupMask w)])).length =
      (Backend.encode before).length+33 := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,
      Scalar.encode_pushWord,List.length_append,List.length_cons,Vector.length_toList,List.length_nil]
  have initialFits : (Backend.encode before).length < UInt256.size := by
    rw [length] at fits
    omega
  have initialGas : 3 ≤ seed.gasAvailable.toNat := by omega
  have initialRoom : (x::tail).length+1 ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have first := word_push_agreement seed before (.op .AND::after)
    (unsignedCleanupMask w) (x::tail) initialFits initialGas initialRoom (fuel+1)
  have remaining : 3 ≤ (unsignedPushResult seed before after w (x::tail)).gasAvailable.toNat := by
    change 3 ≤ (seed.gasAvailable-UInt256.ofNat 3).toNat
    rw [reference_gas_debit seed.gasAvailable 3 initialGas]
    omega
  have second := bitwise_and_agreement
    (unsignedCleanupSite (unsignedPushResult seed before after w (x::tail)) before after w fits)
    (unsignedCleanupMask w) x tail room remaining fuel
  dsimp only at first second
  rw [unsigned_push_tail_alignment] at second
  rw [unsigned_mask_result] at second
  have firstDriver : Assembly.driverSteps 1 (fuel+3) #[] (unsignedPushInput seed before after w (x::tail)) =
      .ok (unsignedPushResult seed before after w (x::tail)) := first.2.1
  refine ⟨Scalar.unsigned_correct w x tail,?_,?_⟩
  · rw [fetched_steps_cons 1 (fuel+1),firstDriver]
    exact second.2.1
  · exact first.2.2.trans second.2.2

#print axioms unsigned_cleanup_execution
end SolidityBridge.RoadmapV15.P10
