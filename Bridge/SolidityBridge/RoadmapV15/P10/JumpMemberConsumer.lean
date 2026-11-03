import SolidityBridge.RoadmapV15.P10.Execution

/-! Conditional-branch consumers of the actual supplied jump-array policy.
Membership is explicit data, not scanner correctness or a successful-gate oracle.
No compiler/source control-flow or Osaka adequacy follows. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def jumpMemberSite (site : Site .JUMPI) (destination condition : UInt256)
    (tail : List UInt256) : Site .JUMPI :=
  {site with seed := {site.seed with stack := destination::condition::tail}}

private theorem jump_member_gate (valid : Array UInt256) (s : EVM.State)
    (destination condition : UInt256) (tail : List UInt256)
    (stack : s.stack = destination::condition::tail)
    (member : valid.contains destination = true)
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
  have admitted : EVM.X.notIn s.stack[0]? valid = false := by
    rw [stack]
    change (!valid.contains destination) = false
    rw [member]
    rfl
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.add_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge gas),
    if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge outputRoom),admitted,Bool.false_eq_true,and_false,if_false]
  cases s.executionEnv.perm <;> rfl

theorem jump_member_agreement (valid : Array UInt256) (site : Site .JUMPI)
    (destination condition : UInt256) (tail : List UInt256)
    (member : valid.contains destination = true) (room : tail.length+2 ≤ 1024)
    (gas : 10 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (jumpMemberSite site destination condition tail).state
    let next := {Assembly.chargedPrepare input 10 with
      pc := if condition != (⟨0⟩ : UInt256) then destination else input.pc + ⟨1⟩
      stack := tail}
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
      EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  let input := (jumpMemberSite site destination condition tail).state
  have gate : Assembly.driverGate valid input .JUMPI = .ok (input,10) :=
    jump_member_gate valid input destination condition tail rfl member room gas
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.JUMPI,none) :=
    decode_jump_if (jumpMemberSite site destination condition tail)
  have step : EVM.step (fuel+1) 10 (some (.JUMPI,none)) input =
      .ok {Assembly.chargedPrepare input 10 with
        pc := if condition != (⟨0⟩ : UInt256) then destination else input.pc + ⟨1⟩
        stack := tail} := by rw [dispatch_jump_if];rfl
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.JUMPI,none) 10 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

/-- Refusal precedes later capacity/static checks; no capacity or permission
premise is needed to observe this actual earlier failure. -/
theorem jump_missing_refusal (valid : Array UInt256) (site : Site .JUMPI)
    (destination condition : UInt256) (tail : List UInt256)
    (missing : valid.contains destination = false) (nonzero : condition ≠ (⟨0⟩ : UInt256))
    (gas : 10 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (jumpMemberSite site destination condition tail).state
    Assembly.driverSteps 1 (fuel+2) valid input = .error .BadJumpDestination ∧
      EVM.X (fuel+1) valid input = .error .BadJumpDestination := by
  dsimp only
  let input := (jumpMemberSite site destination condition tail).state
  have expansion : EVM.memoryExpansionCost input .JUMPI = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : input.gasAvailable-UInt256.ofNat 0 = input.gasAvailable := by
    change UInt256.mk (input.gasAvailable.val-0) = input.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' input .JUMPI = 10 := rfl
  have enoughGas : 10 ≤ input.gasAvailable.toNat := gas
  have enough : 2 ≤ input.stack.length := by
    change 2 ≤ (destination::condition::tail).length
    simp only [List.length_cons];omega
  have invalid : EVM.X.notIn input.stack[0]? valid = true := by
    change (!valid.contains destination) = true
    rw [missing]
    rfl
  have selected : input.stack[1]? ≠ some (⟨0⟩ : UInt256) := by
    change some condition ≠ some (⟨0⟩ : UInt256)
    simpa only [ne_eq,Option.some.injEq] using nonzero
  have gate : Assembly.driverGate valid input .JUMPI = .error .BadJumpDestination := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,
      if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge enoughGas),
      if_neg (Nat.not_lt_of_ge enough),invalid,reduceCtorEq,true_and,and_true,false_and,if_false,bind,Except.bind]
    change (if (Operation.JUMPI : Operation .EVM) = .JUMP then
      .error .BadJumpDestination else _) = _
    rw [if_neg (by decide),if_pos selected]
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.JUMPI,none) :=
    decode_jump_if (jumpMemberSite site destination condition tail)
  constructor
  · rw [checked_jump_if]
    rw [gate]
  · rw [Assembly.X_unfold,decoded]
    dsimp only [Option.getD]
    rw [gate]

#print axioms jump_member_agreement
#print axioms jump_missing_refusal
end SolidityBridge.RoadmapV15.P10
