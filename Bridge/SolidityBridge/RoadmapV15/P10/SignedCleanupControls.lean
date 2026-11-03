import SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures

/-! Inhabited full-State tail clients plus signed/truncation/width and failure
controls. None asserts execution of the preceding emitted PUSH. -/
namespace SolidityBridge.RoadmapV15.P10.SignedCleanupControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open SignedCleanupFixtures
open WordPushFixtures (seed before after spill)

theorem producer_client (w : Fin 32) (x : Scalar.Word) :
    Scalar.run (Scalar.signedCode w) (x::spill) = some (Scalar.signedClean w x::spill) ∧
    Assembly.driverSteps 1 2 #[] (input 10 w x) = .ok (next w x) ∧
    EVM.X 2 #[] (input 10 w x) = EVM.X 1 #[] (next w x) :=
  signed_cleanup_tail (seed 10 false) before after w (site 10 w).pcFits x spill
    (by decide) (by decide) 0

theorem populated_execution_and_failures :
(let input := SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures.input;
 let observed := SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures.observed;
 Solidity.Evm.External.Assembly.driverSteps 1 2 #[] (input 10 ⟨0,by decide⟩ 128) = .ok (observed ⟨0,by decide⟩ 128 (BitVec.ofInt 256 (-128))) ∧
 Solidity.Evm.External.Assembly.driverSteps 1 2 #[] (input 4 ⟨0,by decide⟩ 128) = .error .OutOfGass ∧
 Solidity.Evm.External.Assembly.driverSteps 1 1 #[] (input 0 ⟨0,by decide⟩ 128) = .error .OutOfFuel)
 := by
  constructor
  · rfl
  · constructor <;> rfl

theorem signed_boundary_and_ordered_observations :
(let input := SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures.input;
 let next := SolidityBridge.RoadmapV15.P10.SignedCleanupFixtures.next;
 let u := SolidityBridge.RoadmapV15.P10.WordPushFixtures.u;
 Solidity.Backend.Scalar.signedClean ⟨0,by decide⟩ 128 = BitVec.ofInt 256 (-128) ∧
 Solidity.Backend.Scalar.signedClean ⟨0,by decide⟩ (BitVec.ofNat 256 (2^200+384)) = BitVec.ofInt 256 (-128) ∧
 Solidity.Backend.Scalar.signedClean ⟨1,by decide⟩ 32768 = BitVec.ofInt 256 (-32768) ∧
 Solidity.Backend.Scalar.signedClean ⟨31,by decide⟩ (BitVec.ofNat 256 (2^256-1)) = BitVec.ofNat 256 (2^256-1) ∧
 Solidity.Backend.Scalar.signedClean ⟨0,by decide⟩ 127 = 127 ∧
 EvmYul.UInt256.signextend (u 8) (u 128) ≠ EvmYul.UInt256.mk (BitVec.ofInt 256 (-128)).toFin ∧
 (input 10 ⟨0,by decide⟩ 128).executionEnv.code.data.toList =
  [0x60,0x7f,0x50,0x7f] ++ List.replicate 32 0 ++ [0x0b,0x00] ∧
 (input 10 ⟨0,by decide⟩ 128).stack = [u 0,u 128,u 258,u 513] ∧
 (next ⟨0,by decide⟩ 128).stack = [u (2^256-128),u 258,u 513] ∧
 (next ⟨0,by decide⟩ 128).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
 (next ⟨0,by decide⟩ 128).returnData.data.toList = [0xcc,0xdd] ∧
 (next ⟨0,by decide⟩ 128).H_return.data.toList = [0xee,0xff] ∧
 (next ⟨0,by decide⟩ 128).executionEnv.calldata.data.toList = [0x11,0x22,0x33])
 := by
  decide

#print axioms producer_client
#print axioms populated_execution_and_failures
#print axioms signed_boundary_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.SignedCleanupControls
