import SolidityBridge.RoadmapV15.P10.SignedCleanupAlignment
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Full actual two-instruction signedCode consumption. Source/compiler origin,
whole-program resource adequacy and Osaka approval remain separate. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Both emitted instructions execute: no desired trace or intermediate frame is supplied. -/
theorem signed_cleanup_composition :
∀ (seed : EvmYul.EVM.State) (before after : Solidity.Backend.Program) (w : Fin 32)
 (x : Solidity.Backend.Scalar.Word) (tail : Solidity.Backend.Scalar.Stack)
 (_fits : (Solidity.Backend.encode (before ++ [Solidity.Backend.Scalar.pushWord (SolidityBridge.RoadmapV15.P10.signedCleanupIndex w)])).length < EvmYul.UInt256.size)
 (_room : tail.length+2 ≤ 1024) (_gas : 8 ≤ seed.gasAvailable.toNat) (fuel : Nat),
 let input := SolidityBridge.RoadmapV15.P10.signedPushInput seed before after w x tail;
 let pushed := SolidityBridge.RoadmapV15.P10.signedPushResult seed before after w x tail;
 let next := (Solidity.Evm.External.Assembly.chargedPrepare pushed 5).replaceStackAndIncrPC
  ((Solidity.Backend.Scalar.signedClean w x::tail).map (fun y => EvmYul.UInt256.mk y.toFin));
 Solidity.Backend.Scalar.run (Solidity.Backend.Scalar.signedCode w) (x::tail) = some (Solidity.Backend.Scalar.signedClean w x::tail) ∧
 Solidity.Evm.External.Assembly.driverSteps 2 (fuel+3) #[] input = .ok next ∧
 EvmYul.EVM.X (fuel+3) #[] input = EvmYul.EVM.X (fuel+1) #[] next
 := by
  intro seed before after w x tail fits room gas fuel
  dsimp only
  have length : (Backend.encode (before ++ [Scalar.pushWord (signedCleanupIndex w)])).length =
      (Backend.encode before).length + 33 := by
    simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,
      Scalar.encode_pushWord,List.length_append,List.length_cons,Vector.length_toList,List.length_nil]
  have initialFits : (Backend.encode before).length < UInt256.size := by
    rw [length] at fits
    omega
  have initialGas : 3 ≤ seed.gasAvailable.toNat := by omega
  have initialRoom : (x::tail).length+1 ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have first := word_push_agreement seed before (.op .SIGNEXTEND::after)
    (signedCleanupIndex w) (x::tail) initialFits initialGas initialRoom (fuel+1)
  have remaining : 5 ≤ (signedPushResult seed before after w x tail).gasAvailable.toNat :=
    signed_push_gas seed.gasAvailable gas
  have second := signed_cleanup_tail (signedPushResult seed before after w x tail)
    before after w fits x tail room remaining fuel
  dsimp only at first second
  rw [signed_push_tail_alignment] at second
  have firstDriver : Assembly.driverSteps 1 (fuel+3) #[] (signedPushInput seed before after w x tail) =
      .ok (signedPushResult seed before after w x tail) := first.2.1
  refine ⟨second.1,?_,?_⟩
  · rw [fetched_steps_cons 1 (fuel+1),firstDriver]
    exact second.2.1
  · exact first.2.2.trans second.2.2

#print axioms signed_cleanup_composition
end SolidityBridge.RoadmapV15.P10
