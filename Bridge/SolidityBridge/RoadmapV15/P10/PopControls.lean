import SolidityBridge.RoadmapV15.P10.PopConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated full-State POP clients. No tail permutation or retained head is
accepted; gas precedes stack failure and fuel precedes both in the actual driver.
The supplied jump array is only a parameter probe, not a valid-jump-set proof. -/
namespace SolidityBridge.RoadmapV15.P10.PopControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after spill u)

def supplied : Array UInt256 := #[u 37,u 99]
def site (gas : Nat) (perm : Bool) : Site .POP := ⟨seed gas perm,before,after,by decide⟩
def input (gas : Nat) (perm : Bool) (words : Scalar.Stack) : EVM.State :=
  (modularSite (site gas perm) words).state
def observed (gas : Nat) (perm : Bool) (a : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {input gas perm (a::tail) with
    pc := u 4,gasAvailable := u (gas-2),execLength := 42
    stack := tail.map (fun w => UInt256.mk w.toFin)}

private theorem execute (gas : Nat) (perm : Bool) (a : Scalar.Word) (tail : Scalar.Stack)
    (choice : gas = 2 ∨ gas = 11) (room : tail.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 supplied (input gas perm (a::tail)) = .ok (observed gas perm a tail) := by
  rcases choice with rfl|rfl
  · have h := (pop_agreement supplied (site 2 perm) a tail room (by change (2 : Nat) ≤ 2;decide) 0).2.1
    simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h
  · have h := (pop_agreement supplied (site 11 perm) a tail room (by change (2 : Nat) ≤ 11;decide) 0).2.1
    simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
      Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem nonzero_static :
    Scalar.step (.op .POP) (17::spill) = some spill ∧
    Assembly.driverSteps 1 2 supplied (input 2 false (17::spill)) = .ok (observed 2 false 17 spill) ∧
    EVM.X 2 supplied (input 2 false (17::spill)) = EVM.X 1 supplied (observed 2 false 17 spill) := by
  have h := pop_agreement supplied (site 2 false) 17 spill (by decide) (by decide) 0
  simpa only [input,observed,site,seed,before,after,u,modularSite,Site.state,
    Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC] using h

theorem zero_max_writable :
    Assembly.driverSteps 1 2 supplied (input 11 true (0::spill)) = .ok (observed 11 true 0 spill) ∧
    Assembly.driverSteps 1 2 supplied (input 11 true (BitVec.ofNat 256 (2^256-1)::spill)) =
      .ok (observed 11 true (BitVec.ofNat 256 (2^256-1)) spill) := by
  exact ⟨execute _ _ _ _ (by decide) (by decide),execute _ _ _ _ (by decide) (by decide)⟩

theorem legal_boundaries :
    Assembly.driverSteps 1 2 supplied (input 2 false [17]) = .ok (observed 2 false 17 []) ∧
    Assembly.driverSteps 1 2 supplied (input 2 false (17::List.replicate 1023 258)) =
      .ok (observed 2 false 17 (List.replicate 1023 258)) := by
  exact ⟨execute _ _ _ _ (by decide) (by decide),
    execute _ _ _ _ (by decide) (by simp only [List.length_replicate];decide)⟩

theorem exact_refusal_order :
    Assembly.driverSteps 1 2 supplied (input 2 false []) = .error .StackUnderflow ∧
    Assembly.driverSteps 1 2 supplied (input 1 false []) = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 supplied (input 1 false (17::spill)) = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 supplied (input 0 false []) = .error .OutOfFuel := by exact ⟨rfl,rfl,rfl,rfl⟩

theorem ordered_state_and_negatives :
    (input 2 false (17::spill)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x50,0x00] ∧
    (observed 2 false 17 spill).stack = [u 258,u 513] ∧
    (observed 2 false 17 spill).stack ≠ [u 513,u 258] ∧
    (observed 2 false 17 spill).stack ≠ [u 17,u 258,u 513] ∧
    (observed 2 false 17 spill).gasAvailable = u 0 ∧
    (observed 2 false 17 spill).pc = u 4 ∧
    (observed 2 false 17 spill).execLength = 42 ∧
    (observed 2 false 17 spill).executionEnv.perm = false ∧
    (observed 2 false 17 spill).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed 2 false 17 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (observed 2 false 17 spill).H_return.data.toList = [0xee,0xff] ∧
    (observed 2 false 17 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed 2 false 17 spill).accountMap = WordPushFixtures.accounts ∧
    (observed 2 false 17 spill).σ₀ = WordPushFixtures.accounts := by
  exact ⟨rfl,rfl,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms nonzero_static
#print axioms zero_max_writable
#print axioms legal_boundaries
#print axioms exact_refusal_order
#print axioms ordered_state_and_negatives
end SolidityBridge.RoadmapV15.P10.PopControls
