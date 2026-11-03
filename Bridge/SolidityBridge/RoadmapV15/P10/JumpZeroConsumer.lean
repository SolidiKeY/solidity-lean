import SolidityBridge.RoadmapV15.P10.Execution

/-! Zero-condition JUMPI consumes two actual native words and falls through
without destination validation. No gate-success, decoder or execution oracle
is assumed. Supplied jump-array correctness is neither needed nor inferred. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def jumpZeroSite (site : Site .JUMPI) (destination : UInt256) (tail : List UInt256) : Site .JUMPI :=
  {site with seed := {site.seed with stack := destination::(⟨0⟩ : UInt256)::tail}}

theorem jump_zero_gate (valid : Array UInt256) (s : EVM.State)
    (destination : UInt256) (tail : List UInt256)
    (stack : s.stack = destination::(⟨0⟩ : UInt256)::tail)
    (room : tail.length+2 ≤ 1024) (gas : 10 ≤ s.gasAvailable.toNat) :
    Assembly.driverGate valid s .JUMPI = .ok (s,10) := by
  have expansion : EVM.memoryExpansionCost s .JUMPI = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' s .JUMPI = 10 := rfl
  have enough : 2 ≤ s.stack.length := by rw [stack];simp only [List.length_cons];omega
  have outputRoom : s.stack.length-2 ≤ 1024 := by rw [stack];simp only [List.length_cons];omega
  have disabled : s.stack[1]? = some (⟨0⟩ : UInt256) := by rw [stack];rfl
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.add_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge gas),
    if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge outputRoom),disabled]
  cases s.executionEnv.perm <;> rfl

theorem jump_zero_agreement (valid : Array UInt256) (site : Site .JUMPI)
    (destination : UInt256) (tail : List UInt256) (room : tail.length+2 ≤ 1024)
    (gas : 10 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (jumpZeroSite site destination tail).state
    let next := (Assembly.chargedPrepare input 10).replaceStackAndIncrPC tail
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
      EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  let input := (jumpZeroSite site destination tail).state
  have gate : Assembly.driverGate valid input .JUMPI = .ok (input,10) :=
    jump_zero_gate valid input destination tail rfl room gas
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.JUMPI,none) :=
    decode_jump_if (jumpZeroSite site destination tail)
  have step : EVM.step (fuel+1) 10 (some (.JUMPI,none)) input =
      .ok ((Assembly.chargedPrepare input 10).replaceStackAndIncrPC tail) := by
    rw [dispatch_jump_if]
    rfl
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.JUMPI,none) 10 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

#print axioms jump_zero_gate
#print axioms jump_zero_agreement
end SolidityBridge.RoadmapV15.P10
