import SolidityBridge.RoadmapV15.P10.SignedCleanupSites

/-! Full Scalar signed cleanup result paired with the actual fetched tail.
The represented tail entry is explicit: no preceding PUSH execution is claimed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Every width/value, complete charged tail State, and actual X continuation. -/
theorem signed_cleanup_tail :
∀ (seed : EvmYul.EVM.State) (before after : Solidity.Backend.Program) (w : Fin 32)
 (fits : (Solidity.Backend.encode (before ++ [Solidity.Backend.Scalar.pushWord (SolidityBridge.RoadmapV15.P10.signedCleanupIndex w)])).length < EvmYul.UInt256.size)
 (x : Solidity.Backend.Scalar.Word) (tail : Solidity.Backend.Scalar.Stack)
 (_room : tail.length + 2 ≤ 1024) (_gas : 5 ≤ seed.gasAvailable.toNat) (fuel : Nat),
 let site := SolidityBridge.RoadmapV15.P10.signedCleanupSite seed before after w fits;
 let input := (SolidityBridge.RoadmapV15.P10.modularSite site (SolidityBridge.RoadmapV15.P10.signedCleanupIndex w :: x :: tail)).state;
 let next := (Solidity.Evm.External.Assembly.chargedPrepare input 5).replaceStackAndIncrPC
  ((Solidity.Backend.Scalar.signedClean w x :: tail).map (fun y => EvmYul.UInt256.mk y.toFin));
 Solidity.Backend.Scalar.run (Solidity.Backend.Scalar.signedCode w) (x :: tail) = some (Solidity.Backend.Scalar.signedClean w x :: tail) ∧
 Solidity.Evm.External.Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
 EvmYul.EVM.X (fuel+2) #[] input = EvmYul.EVM.X (fuel+1) #[] next
 := by
  intro seed before after w fits x tail room gas fuel
  dsimp only
  refine ⟨Scalar.signed_correct w x tail,?_⟩
  have h := signextend_fetched (signedCleanupSite seed before after w fits)
    (signedCleanupIndex w) x tail room gas fuel
  dsimp only at h
  rw [signed_cleanup_index_word] at h
  exact h

/-- The selected tail is in the actual complete emitted signedCode image. -/
theorem signed_cleanup_code :
∀ (seed : EvmYul.EVM.State) (before after : Solidity.Backend.Program) (w : Fin 32)
 (fits : (Solidity.Backend.encode (before ++ [Solidity.Backend.Scalar.pushWord (SolidityBridge.RoadmapV15.P10.signedCleanupIndex w)])).length < EvmYul.UInt256.size)
,
 (SolidityBridge.RoadmapV15.P10.signedCleanupSite seed before after w fits).state.executionEnv.code.data.toList =
 Solidity.Backend.encode (before ++ Solidity.Backend.Scalar.signedCode w ++ after)
 := by
  intro seed before after w fits
  simp only [signedCleanupSite,Site.state,signedCleanupIndex,Scalar.signedCode,
    List.toList_toArray,List.append_assoc,List.cons_append,List.nil_append]

#print axioms signed_cleanup_code
#print axioms signed_cleanup_tail
end SolidityBridge.RoadmapV15.P10
