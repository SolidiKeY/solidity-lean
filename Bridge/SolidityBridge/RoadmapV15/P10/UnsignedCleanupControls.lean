import SolidityBridge.RoadmapV15.P10.UnsignedCleanupFixtures

/-! Direct complete-State clients of both emitted unsigned cleanup instructions.
Peak stack capacity and local failures do not establish source-frame origin. -/
namespace SolidityBridge.RoadmapV15.P10.UnsignedCleanupControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open UnsignedCleanupFixtures
open WordPushFixtures (seed before after spill u)

theorem producer_client (w : Fin 32) (x : Scalar.Word) :
    Scalar.run (Scalar.unsignedCode w) (x::spill) = some (Scalar.unsignedClean w x::spill) ∧
    Assembly.driverSteps 2 3 #[] (input 6 w (x::spill)) = .ok (next w x spill) ∧
    EVM.X 3 #[] (input 6 w (x::spill)) = EVM.X 1 #[] (next w x spill) :=
  unsigned_cleanup_execution (seed 6 false) before after w x spill (fits w) (by decide) (by decide) 0

private theorem execute (w : Fin 32) (x : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 3 #[] (input 6 w (x::tail)) = .ok (observed w x tail (Scalar.unsignedClean w x)) := by
  have h := (unsigned_cleanup_execution (seed 6 false) before after w x tail (fits w) room (by decide) 0).2.1
  simpa only [input,observed,seed,before,after,u,unsignedPushResult,unsignedPushInput,wordPushInput,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem populated_execution :
    Assembly.driverSteps 2 3 #[] (input 6 ⟨0,by decide⟩ (0x1234::spill)) =
      .ok (observed ⟨0,by decide⟩ 0x1234 spill 0x34) ∧
    Assembly.driverSteps 2 3 #[] (input 6 ⟨0,by decide⟩ (BitVec.ofNat 256 (2^255+0x1234)::spill)) =
      .ok (observed ⟨0,by decide⟩ (BitVec.ofNat 256 (2^255+0x1234)) spill 0x34) ∧
    Assembly.driverSteps 2 3 #[] (input 6 ⟨31,by decide⟩ (BitVec.ofNat 256 (2^256-1)::spill)) =
      .ok (observed ⟨31,by decide⟩ (BitVec.ofNat 256 (2^256-1)) spill (BitVec.ofNat 256 (2^256-1))) := by
  exact ⟨execute _ _ _ (by decide),execute _ _ _ (by decide),execute _ _ _ (by decide)⟩

/-- Initial1023 succeeds while the intermediate PUSH stack has1024 words. -/
theorem full_initial_success :
    Assembly.driverSteps 2 3 #[] (input 6 ⟨0,by decide⟩ (0x1234::List.replicate 1022 258)) =
      .ok (observed ⟨0,by decide⟩ 0x1234 (List.replicate 1022 258) 0x34) := by
  exact execute _ _ _ (by simp only [List.length_replicate];decide)

/-- A valid initial1024 stack refuses the emitted PUSH; AND is never reached. -/
theorem full_initial_refusal :
    Assembly.driverSteps 2 3 #[] (input 6 ⟨0,by decide⟩ (258::List.replicate 1023 258)) = .error .StackOverflow ∧
    EVM.X 3 #[] (input 6 ⟨0,by decide⟩ (258::List.replicate 1023 258)) = .error .StackOverflow := by
  have h := word_push_full_stack (seed 6 false) before (.op .AND::after)
    (unsignedCleanupMask ⟨0,by decide⟩) (258::List.replicate 1023 258)
    (by decide) (by decide) (by simp only [List.length_cons,List.length_replicate]) 1
  constructor
  · change Assembly.driverSteps 2 3 #[] (wordPushInput (seed 6 false) before (.op .AND::after)
      (unsignedCleanupMask ⟨0,by decide⟩) (258::List.replicate 1023 258)) = _
    rw [fetched_steps_cons 1 1,h.1]
    rfl
  · exact h.2

theorem gas_fuel_refusals :
(let input := SolidityBridge.RoadmapV15.P10.UnsignedCleanupFixtures.input;
 let tail := SolidityBridge.RoadmapV15.P10.WordPushFixtures.spill;
 Solidity.Evm.External.Assembly.driverSteps 2 3 #[] (input 2 ⟨0,by decide⟩ (0x1234::tail)) = .error .OutOfGass ∧
 Solidity.Evm.External.Assembly.driverSteps 2 3 #[] (input 5 ⟨0,by decide⟩ (0x1234::tail)) = .error .OutOfGass ∧
 Solidity.Evm.External.Assembly.driverSteps 2 2 #[] (input 6 ⟨0,by decide⟩ (0x1234::tail)) = .error .OutOfFuel)
 := by
  first
  | solve | simp only []
  | solve | decide
  | solve | omega
  | solve | rfl
  | exact ⟨rfl,rfl,rfl⟩

theorem values_and_ordered_observations :
(let input := SolidityBridge.RoadmapV15.P10.UnsignedCleanupFixtures.input;
 let next := SolidityBridge.RoadmapV15.P10.UnsignedCleanupFixtures.next;
 let tail := SolidityBridge.RoadmapV15.P10.WordPushFixtures.spill;
 let u := SolidityBridge.RoadmapV15.P10.WordPushFixtures.u;
 (Solidity.Backend.Scalar.unsignedClean ⟨0,by decide⟩ 128).toNat = 128 ∧
 (Solidity.Backend.Scalar.signedClean ⟨0,by decide⟩ 128).toNat ≠ 128 ∧
 (Solidity.Backend.Scalar.unsignedClean ⟨1,by decide⟩ 0x123456).toNat = 0x3456 ∧
 (Solidity.Backend.Scalar.unsignedClean ⟨0,by decide⟩ 0).toNat = 0 ∧
 (SolidityBridge.RoadmapV15.P10.unsignedCleanupMask ⟨0,by decide⟩).toNat = 255 ∧
 (SolidityBridge.RoadmapV15.P10.unsignedCleanupMask ⟨31,by decide⟩).toNat = 2^256-1 ∧
 (u 1-u EvmYul.UInt256.size).toNat = 1 ∧ (1 : Nat)-EvmYul.UInt256.size = 0 ∧ ¬EvmYul.UInt256.size ≤ (u 1).toNat ∧
 (input 6 ⟨0,by decide⟩ (0x1234::tail)).executionEnv.code.data.toList =
  [0x60,0x7f,0x50,0x7f] ++ List.replicate 31 0 ++ [0xff,0x16,0x00] ∧
 (input 6 ⟨0,by decide⟩ (0x1234::tail)).executionEnv.code.data.toList ≠
  [0x60,0x7f,0x50,0x7f,0xff] ++ List.replicate 31 0 ++ [0x16,0x00] ∧
 (input 6 ⟨0,by decide⟩ (0x1234::tail)).stack = [u 0x1234,u 258,u 513] ∧
 (next ⟨0,by decide⟩ 0x1234 tail).stack = [u 0x34,u 258,u 513] ∧
 (next ⟨0,by decide⟩ 0x1234 tail).pc.toNat = 37 ∧
 (next ⟨0,by decide⟩ 0x1234 tail).gasAvailable.toNat = 0 ∧
 (next ⟨0,by decide⟩ 0x1234 tail).execLength = 43 ∧
 (next ⟨0,by decide⟩ 0x1234 tail).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
 (next ⟨0,by decide⟩ 0x1234 tail).returnData.data.toList = [0xcc,0xdd] ∧
 (next ⟨0,by decide⟩ 0x1234 tail).H_return.data.toList = [0xee,0xff] ∧
 (next ⟨0,by decide⟩ 0x1234 tail).executionEnv.calldata.data.toList = [0x11,0x22,0x33])
 := by
  decide

#print axioms producer_client
#print axioms populated_execution
#print axioms full_initial_success
#print axioms full_initial_refusal
#print axioms gas_fuel_refusals
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.UnsignedCleanupControls
