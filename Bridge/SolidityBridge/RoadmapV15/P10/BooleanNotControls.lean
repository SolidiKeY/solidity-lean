import SolidityBridge.RoadmapV15.P10.BooleanNotFixtures

/-! Populated canonical clients, raw-word probes and charged/fuel boundaries.
A full legal unary input remains full; these controls do not claim a reachable
unary overflow. The supplied jump array is a parameter probe only. -/
namespace SolidityBridge.RoadmapV15.P10.BooleanNotControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open BooleanNotFixtures
open WordPushFixtures (seed before after spill u)

private theorem execute (a : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 supplied (input 3 false (a::tail)) =
      .ok (observed 3 false a tail (Scalar.flag (a == 0))) := by
  have h := (iszero_agreement supplied (site 3 false) a tail room (by decide) 0).2.1
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem typed_true :
    Scalar.run Scalar.booleanNot.code (Scalar.encodeValue .bool true::spill) =
      some (Scalar.encodeValue .bool false::spill) ∧
    Assembly.driverSteps 1 2 supplied (input 11 true (1::spill)) = .ok (observed 11 true 1 spill 0) ∧
    EVM.X 2 supplied (input 11 true (1::spill)) = EVM.X 1 supplied (observed 11 true 1 spill 0) := by
  have h := boolean_not_agreement supplied (site 11 true) true spill (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem typed_false :
    Scalar.run Scalar.booleanNot.code (Scalar.encodeValue .bool false::spill) =
      some (Scalar.encodeValue .bool true::spill) ∧
    Assembly.driverSteps 1 2 supplied (input 3 false (0::spill)) = .ok (observed 3 false 0 spill 1) ∧
    EVM.X 2 supplied (input 3 false (0::spill)) = EVM.X 1 supplied (observed 3 false 0 spill 1) := by
  have h := boolean_not_agreement supplied (site 3 false) false spill (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem raw_word_clients :
    Assembly.driverSteps 1 2 supplied (input 3 false (0::spill)) = .ok (observed 3 false 0 spill 1) ∧
    Assembly.driverSteps 1 2 supplied (input 3 false (2::spill)) = .ok (observed 3 false 2 spill 0) ∧
    Assembly.driverSteps 1 2 supplied (input 3 false (BitVec.ofNat 256 (2^256-1)::spill)) =
      .ok (observed 3 false (BitVec.ofNat 256 (2^256-1)) spill 0) := by
  exact ⟨execute _ _ (by decide),execute _ _ (by decide),execute _ _ (by decide)⟩

/-- A legal 1024-word input neither grows nor loses its caller tail. -/
theorem full_input_stack :
    Assembly.driverSteps 1 2 supplied (input 3 false (1::List.replicate 1023 258)) =
      .ok (observed 3 false 1 (List.replicate 1023 258) 0) := by
  exact execute _ _ (by simp only [List.length_replicate];decide)

theorem refused_resources :
    Assembly.driverSteps 1 2 supplied (input 3 false []) = .error .StackUnderflow ∧
    Assembly.driverSteps 1 2 supplied (input 2 false []) = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 supplied (input 0 false []) = .error .OutOfFuel := by
  exact ⟨rfl,rfl,rfl⟩

theorem values_and_ordered_observations :
    Scalar.encodeValue .bool false = 0 ∧ Scalar.encodeValue .bool true = 1 ∧
    (∀ b : Bool, Scalar.encodeValue .bool b ≠ 2) ∧
    (UInt256.isZero (u 2)).toNat = 0 ∧ (UInt256.lnot (u 1)).toNat ≠ 0 ∧
    supplied.toList = [u 37,u 99] ∧
    (input 11 true (1::spill)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x15,0x00] ∧
    (input 11 true (1::spill)).executionEnv.code.data.toList ≠ [0x60,0x7f,0x50,0x19,0x00] ∧
    (input 11 true (1::spill)).stack = [u 1,u 258,u 513] ∧
    (observed 11 true 1 spill 0).stack = [u 0,u 258,u 513] ∧
    (observed 3 false 0 spill 1).stack = [u 1,u 258,u 513] ∧
    (observed 11 true 1 spill 0).pc.toNat = 4 ∧
    (observed 11 true 1 spill 0).gasAvailable.toNat = 8 ∧
    (observed 11 true 1 spill 0).execLength = 42 ∧
    (observed 11 true 1 spill 0).memory.data.toList = ([0xaa,0xbb] : List UInt8) ++ List.replicate 30 0 ∧
    (observed 11 true 1 spill 0).returnData.data.toList = [0xcc,0xdd] ∧
    (observed 11 true 1 spill 0).H_return.data.toList = [0xee,0xff] ∧
    (observed 11 true 1 spill 0).executionEnv.calldata.data.toList = [0x11,0x22,0x33] := by
  decide

#print axioms typed_true
#print axioms typed_false
#print axioms raw_word_clients
#print axioms full_input_stack
#print axioms refused_resources
#print axioms values_and_ordered_observations
end SolidityBridge.RoadmapV15.P10.BooleanNotControls
