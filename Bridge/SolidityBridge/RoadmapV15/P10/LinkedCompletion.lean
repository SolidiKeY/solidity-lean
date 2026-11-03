import SolidityBridge.RoadmapV15.P10.LinkedCompletionLayout

/-! Actual three-instruction exit completion for arbitrary native caller State
and legal tail. Eleven gas admits JUMPI/JUMPDEST/STOP; resource abstraction,
source-prefix execution and opaque D_J equality remain separate obligations. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem completion_ref72 : 72 ∈ LinkedJumpFixtures.program.checked.image.refs := by
  change 72 ∈ [0,72]
  exact List.Mem.tail 0 (List.Mem.head [])

private theorem completion_destination (seed : EVM.State) (tail : List UInt256) :
    EVM.decode (linkedCompletionJump seed tail).executionEnv.code
      (linkedCompletionJump seed tail).pc = some (.JUMPDEST,none) := by
  exact (LinkedJumpFixtures.program.reference 72 completion_ref72).2.2

private theorem completion_stop_decoded (seed : EVM.State) (tail : List UInt256) :
    EVM.decode (linkedCompletionStop seed tail).executionEnv.code
      (linkedCompletionStop seed tail).pc = some (.STOP,none) := by rfl

theorem linked_completion_branch (seed : EVM.State) (tail : List UInt256)
    (room : tail.length+2 ≤ 1024) (gas : 10 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) LinkedJumpFixtures.program.validJumps
      (linkedCompletionInput seed tail) = .ok (linkedCompletionJump seed tail) ∧
    EVM.X (fuel+2) LinkedJumpFixtures.program.validJumps (linkedCompletionInput seed tail) =
      EVM.X (fuel+1) LinkedJumpFixtures.program.validJumps (linkedCompletionJump seed tail) := by
  exact (linked_reference_jumpi LinkedJumpFixtures.program 72 completion_ref72
    (linkedCompletionSite seed) rfl (.ofNat 1) tail room gas fuel).2.2

theorem linked_completion_suffix (seed : EVM.State) (tail : List UInt256)
    (room : tail.length+2 ≤ 1024) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+3) LinkedJumpFixtures.program.validJumps (linkedCompletionJump seed tail) =
      .ok (.success (linkedCompletionOutput seed tail) .empty) := by
  let current := linkedCompletionJump seed tail
  let stopping := linkedCompletionStop seed tail
  have enoughFirst : 10 ≤ seed.gasAvailable.toNat := by omega
  have debit : current.gasAvailable.toNat = seed.gasAvailable.toNat-10 :=
    reference_gas_debit seed.gasAvailable 10 enoughFirst
  have enough : 1 ≤ current.gasAvailable.toNat := by rw [debit];omega
  have capacity : current.stack.length ≤ 1024 := by change tail.length ≤ 1024;omega
  have stopCapacity : stopping.stack.length ≤ 1024 := by change tail.length ≤ 1024;omega
  apply Assembly.X_destination_stop fuel LinkedJumpFixtures.program.validJumps
    current current stopping 1 0
  · exact completion_destination seed tail
  · exact completion_terminal_gate _ current .JUMPDEST 1 (Or.inl ⟨rfl,rfl⟩) enough capacity
  · change (EVM.decode (linkedCompletionStop seed tail).executionEnv.code
      (linkedCompletionStop seed tail).pc).getD (.STOP,none) = (.STOP,none)
    simp only [completion_stop_decoded,Option.getD_some]
  · exact completion_terminal_gate _ stopping .STOP 0 (Or.inr ⟨rfl,rfl⟩) (Nat.zero_le _) stopCapacity

theorem linked_completion_execution (seed : EVM.State) (tail : List UInt256)
    (room : tail.length+2 ≤ 1024) (gas : 11 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+4) LinkedJumpFixtures.program.validJumps (linkedCompletionInput seed tail) =
      .ok (.success (linkedCompletionOutput seed tail) .empty) := by
  have enough : 10 ≤ seed.gasAvailable.toNat := by omega
  have branch := (linked_completion_branch seed tail room enough (fuel+2)).2
  exact branch.trans (linked_completion_suffix seed tail room gas fuel)

theorem linked_completion_debit (seed : EVM.State) (tail : List UInt256)
    (gas : 11 ≤ seed.gasAvailable.toNat) :
    (linkedCompletionOutput seed tail).gasAvailable.toNat = seed.gasAvailable.toNat-11 := by
  have enough : 10 ≤ seed.gasAvailable.toNat := by omega
  have first := reference_gas_debit seed.gasAvailable 10 enough
  have remaining : 1 ≤ (seed.gasAvailable-UInt256.ofNat 10).toNat := by rw [first];omega
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 10) 1 remaining
  have final := reference_gas_debit ((seed.gasAvailable-UInt256.ofNat 10)-UInt256.ofNat 1) 0 (Nat.zero_le _)
  change (((seed.gasAvailable-UInt256.ofNat 10)-UInt256.ofNat 1)-UInt256.ofNat 0).toNat = _
  rw [final,second,first]
  simp only [Nat.sub_zero,Nat.sub_sub]

#print axioms linked_completion_branch
#print axioms linked_completion_suffix
#print axioms linked_completion_execution
#print axioms linked_completion_debit
end SolidityBridge.RoadmapV15.P10
