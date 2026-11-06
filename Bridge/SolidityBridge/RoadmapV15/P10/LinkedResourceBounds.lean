import SolidityBridge.RoadmapV15.P10.LinkedCompletion

/-! Universal resource counterexamples for the actual fetched linked exit.
These retain arbitrary native caller states and legal tails; they do not establish
source-prefix execution, resource abstraction, or transaction correspondence. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- Three units of dispatcher fuel reach STOP with no evaluator fuel left. -/
theorem linked_completion_three_fuel (seed : EVM.State) (tail : List UInt256)
    (room : tail.length+2 ≤ 1024) (gas : 11 ≤ seed.gasAvailable.toNat) :
    EVM.X 3 LinkedJumpFixtures.program.validJumps (linkedCompletionInput seed tail) =
      .error .OutOfFuel := by
  let current := linkedCompletionJump seed tail
  let stopping := linkedCompletionStop seed tail
  have enough : 10 ≤ seed.gasAvailable.toNat := by omega
  have debit : current.gasAvailable.toNat = seed.gasAvailable.toNat-10 :=
    reference_gas_debit seed.gasAvailable 10 enough
  have currentGas : 1 ≤ current.gasAvailable.toNat := by rw [debit];omega
  have currentRoom : current.stack.length ≤ 1024 := by change tail.length ≤ 1024;omega
  have stopRoom : stopping.stack.length ≤ 1024 := by change tail.length ≤ 1024;omega
  have branch := (linked_completion_branch seed tail room enough 1).2
  have decoded : EVM.decode current.executionEnv.code current.pc = some (.JUMPDEST,none) := by
    exact (LinkedJumpFixtures.program.reference 72 (by change 72 ∈ [0,72];decide)).2.2
  have gate : Assembly.driverGate LinkedJumpFixtures.program.validJumps current .JUMPDEST = .ok (current,1) :=
    completion_terminal_gate _ current .JUMPDEST 1 (Or.inl ⟨rfl,rfl⟩) currentGas currentRoom
  have step : EVM.step 1 1 (some (.JUMPDEST,none)) current = .ok stopping := by rfl
  have dest := Assembly.X_continue 0 LinkedJumpFixtures.program.validJumps current current stopping
    (.JUMPDEST,none) 1 decoded gate step (by unfold Assembly.NonhaltingOpcode;decide)
  have stopDecoded : EVM.decode stopping.executionEnv.code stopping.pc = some (.STOP,none) := by rfl
  have stopGate : Assembly.driverGate LinkedJumpFixtures.program.validJumps stopping .STOP = .ok (stopping,0) :=
    completion_terminal_gate _ stopping .STOP 0 (Or.inr ⟨rfl,rfl⟩) (Nat.zero_le _) stopRoom
  refine branch.trans (dest.trans ?_)
  conv_lhs => rw [Assembly.X_unfold]
  simp only [stopDecoded,Option.getD_some,stopGate,EVM.step,bind,Except.bind]

/-- Ten gas pays JUMPI but cannot pay the fetched destination's one gas. -/
theorem linked_completion_ten_gas (seed : EVM.State) (tail : List UInt256)
    (room : tail.length+2 ≤ 1024) (gas : seed.gasAvailable.toNat = 10) (fuel : Nat) :
    EVM.X (fuel+3) LinkedJumpFixtures.program.validJumps (linkedCompletionInput seed tail) =
      .error .OutOfGass := by
  let current := linkedCompletionJump seed tail
  have enough : 10 ≤ seed.gasAvailable.toNat := by omega
  have debit : current.gasAvailable.toNat = 0 := by
    have h := reference_gas_debit seed.gasAvailable 10 enough
    change (seed.gasAvailable-UInt256.ofNat 10).toNat = 0
    rw [h,gas]
  have decoded : EVM.decode current.executionEnv.code current.pc = some (.JUMPDEST,none) := by
    exact (LinkedJumpFixtures.program.reference 72 (by change 72 ∈ [0,72];decide)).2.2
  have expansion : EVM.memoryExpansionCost current .JUMPDEST = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : current.gasAvailable-UInt256.ofNat 0 = current.gasAvailable := by
    change UInt256.mk (current.gasAvailable.val-0) = current.gasAvailable
    rw [sub_zero]
  have refused : Assembly.driverGate LinkedJumpFixtures.program.validJumps current .JUMPDEST = .error .OutOfGass := by
    simp only [Assembly.driverGate,expansion,Nat.not_lt_zero,if_false,charge]
    change (if current.gasAvailable.toNat < 1 then _ else _) = _
    rw [debit]
    rfl
  have branch := (linked_completion_branch seed tail room enough (fuel+1)).2
  refine branch.trans ?_
  change EVM.X (fuel+2) LinkedJumpFixtures.program.validJumps current = .error .OutOfGass
  conv_lhs => rw [Assembly.X_unfold]
  simp only [decoded,Option.getD_some,refused]

#print axioms linked_completion_three_fuel
#print axioms linked_completion_ten_gas
end SolidityBridge.RoadmapV15.P10
