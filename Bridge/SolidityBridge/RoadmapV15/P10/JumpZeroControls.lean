import SolidityBridge.RoadmapV15.P10.JumpZeroConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Full-State zero-branch clients and nonzero/destination/refusal contrasts.
No populated supplied array is promoted to a scanner-correctness theorem. -/
namespace SolidityBridge.RoadmapV15.P10.JumpZeroControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u)

def supplied : Array UInt256 := #[u 37,u 99]
def tail : List UInt256 := [u 258,u 513]
def site (gas : Nat) (perm : Bool) : Site .JUMPI := ⟨seed gas perm,before,after,by decide⟩
def input (gas : Nat) (perm : Bool) (destination : UInt256) (rest : List UInt256) : EVM.State :=
  (jumpZeroSite (site gas perm) destination rest).state
def observed (gas : Nat) (perm : Bool) (destination : UInt256) (rest : List UInt256) : EVM.State :=
  {input gas perm destination rest with
    pc := u 4,gasAvailable := u (gas-10),execLength := 42,stack := rest}
def nonzero (gas : Nat) (perm : Bool) (destination condition : UInt256) : EVM.State :=
  {input gas perm destination tail with stack := destination::condition::tail}

private theorem execute (valid : Array UInt256) (destination : UInt256) (rest : List UInt256)
    (room : rest.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 valid (input 10 false destination rest) =
      .ok (observed 10 false destination rest) := by
  have h := (jump_zero_agreement valid (site 10 false) destination rest room (by decide) 0).1
  simpa only [input,observed,site,seed,before,after,u,jumpZeroSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem maximum_invalid_destination :
    Assembly.driverSteps 1 2 #[] (input 10 false (u (2^256-1)) tail) =
      .ok (observed 10 false (u (2^256-1)) tail) ∧
    EVM.X 2 #[] (input 10 false (u (2^256-1)) tail) =
      EVM.X 1 #[] (observed 10 false (u (2^256-1)) tail) := by
  have h := jump_zero_agreement #[] (site 10 false) (u (2^256-1)) tail (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,jumpZeroSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem writable_parameter_probe :
    Assembly.driverSteps 1 2 supplied (input 27 true (u 13) tail) = .ok (observed 27 true (u 13) tail) ∧
    EVM.X 2 supplied (input 27 true (u 13) tail) = EVM.X 1 supplied (observed 27 true (u 13) tail) := by
  have h := jump_zero_agreement supplied (site 27 true) (u 13) tail (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,jumpZeroSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem legal_boundaries :
    Assembly.driverSteps 1 2 #[] (input 10 false (u 13) []) = .ok (observed 10 false (u 13) []) ∧
    Assembly.driverSteps 1 2 supplied (input 10 false (u 13) (List.replicate 1022 (u 258))) =
      .ok (observed 10 false (u 13) (List.replicate 1022 (u 258))) := by
  exact ⟨execute _ _ _ (by decide),execute _ _ _ (by simp only [List.length_replicate];decide)⟩

theorem nonzero_and_ordered_refusals :
    Assembly.driverSteps 1 2 #[] (nonzero 10 false (u 13) (u 1)) = .error .BadJumpDestination ∧
    Assembly.driverSteps 1 2 supplied (nonzero 10 true (u 13) (u 2)) = .error .BadJumpDestination ∧
    Assembly.driverSteps 1 2 #[] (nonzero 9 false (u 13) (u 1)) = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] ({input 10 false (u 13) [] with stack := [u 13]}) = .error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] ({input 9 false (u 13) [] with stack := []}) = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (nonzero 0 false (u 13) (u 1)) = .error .OutOfFuel := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem complete_ordered_observations :
    (input 10 false (u 13) tail).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x57,0x00] ∧
    (input 10 false (u 13) tail).stack = [u 13,u 0,u 258,u 513] ∧
    (observed 10 false (u 13) tail).stack = [u 258,u 513] ∧
    (observed 10 false (u 13) tail).stack ≠ [u 513,u 258] ∧
    (observed 10 false (u 13) tail).pc = u 4 ∧
    (observed 10 false (u 13) tail).pc ≠ u 13 ∧
    (observed 10 false (u 13) tail).gasAvailable = u 0 ∧
    (observed 27 true (u 13) tail).gasAvailable = u 17 ∧
    (observed 10 false (u 13) tail).execLength = 42 ∧
    (observed 10 false (u 13) tail).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed 10 false (u 13) tail).returnData.data.toList = [0xcc,0xdd] ∧
    (observed 10 false (u 13) tail).H_return.data.toList = [0xee,0xff] ∧
    (observed 10 false (u 13) tail).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed 10 false (u 13) tail).accountMap = WordPushFixtures.accounts ∧
    (observed 10 false (u 13) tail).σ₀ = WordPushFixtures.accounts := by
  exact ⟨rfl,rfl,rfl,by decide,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms maximum_invalid_destination
#print axioms writable_parameter_probe
#print axioms legal_boundaries
#print axioms nonzero_and_ordered_refusals
#print axioms complete_ordered_observations
end SolidityBridge.RoadmapV15.P10.JumpZeroControls
