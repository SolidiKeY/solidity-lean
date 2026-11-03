import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Complete populated native-state clients and meaningful failure/encoding controls.
The zero word still uses the actual PUSH32 emitter. Word-constructor wrapping
is not a source overflow-policy theorem. -/
namespace SolidityBridge.RoadmapV15.P10.WordPushControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures
private def minusOne : PrimTy.int.Denote := ⟨-1,by decide⟩

private theorem execute (perm : Bool) (w : Scalar.Word) (words : Scalar.Stack)
    (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (input 10 perm w words) = .ok (expected perm w words) := by
  have h := (word_push_agreement (seed 10 perm) before after w words
    (by decide) (by change (3 <= 10);decide) room 0).2.1
  simpa only [input,expected,seed,before,after,u,wordPushInput,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem producer_client :
    Scalar.step (Scalar.pushWord 258) spill = some (258::spill) ∧
    Assembly.driverSteps 1 2 #[] (input 10 false 258 spill) = .ok (expected false 258 spill) ∧
    EVM.X 2 #[] (input 10 false 258 spill) = EVM.X 1 #[] (expected false 258 spill) := by
  have h := word_push_agreement (seed 10 false) before after 258 spill
    (by decide) (by change (3 <= 10);decide) (by decide) 0
  simpa only [input,expected,seed,before,after,u,wordPushInput,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem zero_uses_push32 :
    Assembly.driverSteps 1 2 #[] (input 10 false 0 spill) = .ok (expected false 0 spill) ∧
    EVM.C' (input 10 false 0 spill) (.Push .PUSH32) = 3 ∧
    (input 10 false 0 spill).executionEnv.code.get? 3 = some 0x7f := by
  exact ⟨execute false 0 spill (by decide),rfl,rfl⟩

theorem maximum_word :
    Assembly.driverSteps 1 2 #[] (input 10 false (BitVec.ofNat 256 (2^256-1)) spill) =
      .ok (expected false (BitVec.ofNat 256 (2^256-1)) spill) := by
  exact execute _ _ _ (by decide)

theorem typed_signed_word :
    Assembly.driverSteps 1 2 #[] (input 10 false (Scalar.encodeValue .int minusOne) spill) =
      .ok (expected false (BitVec.ofInt 256 (-1)) spill) := by
  exact execute _ _ _ (by decide)

theorem word_wrap_before_encoding :
    Assembly.driverSteps 1 2 #[] (input 10 false (BitVec.ofNat 256 (2^256+258)) spill) =
      .ok (expected false 258 spill) := by
  have wrapped : BitVec.ofNat 256 (2^256+258) = (258 : Scalar.Word) := by decide
  rw [wrapped]
  exact execute _ _ _ (by decide)

theorem writable_word :
    Assembly.driverSteps 1 2 #[] (input 10 true 258 spill) = .ok (expected true 258 spill) := by
  exact execute _ _ _ (by decide)

theorem capacity_success :
    Assembly.driverSteps 1 2 #[] (input 10 false 258 (List.replicate 1023 258)) =
      .ok (expected false 258 (List.replicate 1023 258)) := by
  exact execute _ _ _ (by simp only [List.length_replicate];decide)

theorem capacity_refusal :
    Assembly.driverSteps 1 2 #[] (input 3 false 258 (List.replicate 1024 258)) = .error .StackOverflow ∧
    EVM.X 2 #[] (input 3 false 258 (List.replicate 1024 258)) = .error .StackOverflow := by
  exact word_push_full_stack (seed 3 false) before after 258 (List.replicate 1024 258)
    (by decide) (by change (3 <= 3);decide) (by simp only [List.length_replicate]) 0

theorem gas_before_capacity :
    Assembly.driverSteps 1 2 #[] (input 2 false 258 (List.replicate 1024 258)) = .error .OutOfGass := by
  rfl

theorem fuel_before_gas :
    Assembly.driverSteps 1 1 #[] (input 0 false 258 []) = .error .OutOfFuel := by
  rfl

theorem wrong_endian_value :
    (uInt256OfByteArray ⟨(toBytesBE 32 (258 : Scalar.Word).toNat).toArray⟩).toNat ≠
      2*256^31+256^30 := by
  decide

theorem wrong_payload_length :
    (Scalar.pushWord (258 : Scalar.Word)).encode ≠ 0x7f :: (toBytesBE 31 258).toList := by
  decide

theorem ordered_observations :
    (expected false 258 spill).executionEnv.code.data.toList =
      [0x60,0x7f,0x50,0x7f] ++ (toBytesBE 32 258).toList ++ [0x00] ∧
    (expected false 258 spill).stack = [u 258,u 258,u 513] ∧
    (expected false 258 spill).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
    (expected false 258 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected false 258 spill).H_return.data.toList = [0xee,0xff] ∧
    (expected false 258 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide

#print axioms producer_client
#print axioms zero_uses_push32
#print axioms maximum_word
#print axioms typed_signed_word
#print axioms word_wrap_before_encoding
#print axioms writable_word
#print axioms capacity_success
#print axioms capacity_refusal
#print axioms gas_before_capacity
#print axioms fuel_before_gas
#print axioms wrong_endian_value
#print axioms wrong_payload_length
#print axioms ordered_observations
end SolidityBridge.RoadmapV15.P10.WordPushControls
