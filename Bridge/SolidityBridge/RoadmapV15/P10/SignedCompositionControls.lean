import SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures

/-! Populated actual two-instruction clients. Execution uses the proved modular
composition rather than expanding the entire pinned dispatcher in the kernel. -/
namespace SolidityBridge.RoadmapV15.P10.SignedCompositionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SignedCompositionFixtures
open WordPushFixtures (seed before after spill u)

theorem producer_client (w : Fin 32) (x : Scalar.Word) :
    Scalar.run (Scalar.signedCode w) (x::spill) = some (Scalar.signedClean w x::spill) ∧
    Assembly.driverSteps 2 3 #[] (input 8 w x) = .ok (next w x) ∧
    EVM.X 3 #[] (input 8 w x) = EVM.X 1 #[] (next w x) :=
  signed_cleanup_composition (seed 8 false) before after w x spill
    (SignedCleanupFixtures.site 8 w).pcFits (by decide) (by decide) 0

private theorem execute (w : Fin 32) (x : Scalar.Word) :
    Assembly.driverSteps 2 3 #[] (input 8 w x) = .ok (observed w x (Scalar.signedClean w x)) := by
  have h := (producer_client w x).2.1
  simpa only [input,next,observed,signedPushResult,signedPushInput,wordPushInput,
    seed,before,after,u,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem populated_execution :
(let input := SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures.input;
 let observed := SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures.observed;
 Solidity.Evm.External.Assembly.driverSteps 2 3 #[] (input 8 ⟨0,by decide⟩ 128) = .ok (observed ⟨0,by decide⟩ 128 (BitVec.ofInt 256 (-128))) ∧
 Solidity.Evm.External.Assembly.driverSteps 2 3 #[] (input 8 ⟨0,by decide⟩ (BitVec.ofNat 256 (2^200+384))) = .ok (observed ⟨0,by decide⟩ (BitVec.ofNat 256 (2^200+384)) (BitVec.ofInt 256 (-128))) ∧
 Solidity.Evm.External.Assembly.driverSteps 2 3 #[] (input 8 ⟨31,by decide⟩ (BitVec.ofNat 256 (2^256-1))) = .ok (observed ⟨31,by decide⟩ (BitVec.ofNat 256 (2^256-1)) (BitVec.ofNat 256 (2^256-1))))
 := by
  exact ⟨execute _ _,execute _ _,execute _ _⟩

theorem gas_and_fuel_refusals :
(let input := SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures.input;
 Solidity.Evm.External.Assembly.driverSteps 2 3 #[] (input 7 ⟨0,by decide⟩ 128) = .error .OutOfGass ∧
 Solidity.Evm.External.Assembly.driverSteps 2 3 #[] (input 2 ⟨0,by decide⟩ 128) = .error .OutOfGass ∧
 Solidity.Evm.External.Assembly.driverSteps 2 2 #[] (input 8 ⟨0,by decide⟩ 128) = .error .OutOfFuel)
 := by
  constructor
  · rfl
  · constructor <;> rfl

theorem arithmetic_and_ordered_observations :
(let input := SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures.input;
 let next := SolidityBridge.RoadmapV15.P10.SignedCompositionFixtures.next;
 let u := SolidityBridge.RoadmapV15.P10.WordPushFixtures.u;
 (u 2-u 3).toNat = EvmYul.UInt256.size-1 ∧
 (u (EvmYul.UInt256.size-33)+u 33).toNat = 0 ∧
 (u (EvmYul.UInt256.size-34)+u 33).toNat = EvmYul.UInt256.size-1 ∧
 ¬8 ≤ (u 2).toNat ∧ (u 0+u 33).toNat ≠ 34 ∧
 (input 8 ⟨0,by decide⟩ 128).executionEnv.code.data.toList =
  [0x60,0x7f,0x50,0x7f] ++ List.replicate 32 0 ++ [0x0b,0x00] ∧
 (input 8 ⟨0,by decide⟩ 128).stack = [u 128,u 258,u 513] ∧
 (next ⟨0,by decide⟩ 128).stack = [u (2^256-128),u 258,u 513] ∧
 (next ⟨0,by decide⟩ 128).pc.toNat = 37 ∧
 (next ⟨0,by decide⟩ 128).gasAvailable.toNat = 0 ∧
 (next ⟨0,by decide⟩ 128).execLength = 43 ∧
 (next ⟨0,by decide⟩ 128).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
 (next ⟨0,by decide⟩ 128).returnData.data.toList = [0xcc,0xdd] ∧
 (next ⟨0,by decide⟩ 128).H_return.data.toList = [0xee,0xff] ∧
 (next ⟨0,by decide⟩ 128).executionEnv.calldata.data.toList = [0x11,0x22,0x33])
 := by
  decide

#print axioms producer_client
#print axioms populated_execution
#print axioms gas_and_fuel_refusals
#print axioms arithmetic_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.SignedCompositionControls
