import SolidityBridge.RoadmapV15.P10.LinkedCompletion

/-! Whole X success at the eleven-gas boundary, caller-tail/frame observations
and modular low-gas/fuel controls. STOP clears returnData, keeps H_return and
leaves the PC at its actual byte; prefix/source execution remains unproved. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedCompletionControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u)
open LinkedJumpFixtures (program tail)

def observed (gas : Nat) (perm : Bool) (rest : List UInt256) : EVM.State :=
  {linkedCompletionInput (seed gas perm) rest with
    pc := u 73,gasAvailable := u (gas-11),execLength := 44,stack := rest,returnData := .empty}

private theorem execute (rest : List UInt256) (room : rest.length+2 ≤ 1024) :
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 11 false) rest) =
      .ok (.success (observed 11 false rest) .empty) := by
  have h := linked_completion_execution (seed 11 false) rest room (by decide) 0
  simpa only [observed,linkedCompletionOutput,linkedCompletionStop,linkedCompletionJump,
    linkedCompletionInput,linkedCompletionSite,jumpMemberSite,Site.state,seed,u,
    Assembly.stopAfter,Assembly.chargedPrepare,EVM.State.incrPC] using h

theorem exact_budget_static :
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 11 false) tail) =
      .ok (.success (observed 11 false tail) .empty) ∧
    (linkedCompletionOutput (seed 11 false) tail).gasAvailable.toNat = 0 := by
  exact ⟨execute _ (by decide),linked_completion_debit (seed 11 false) tail (by decide)⟩

theorem writable_excess :
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 27 true) tail) =
      .ok (.success (observed 27 true tail) .empty) ∧
    (linkedCompletionOutput (seed 27 true) tail).gasAvailable.toNat = 16 := by
  have h := linked_completion_execution (seed 27 true) tail (by decide) (by decide) 0
  constructor
  · simpa only [observed,linkedCompletionOutput,linkedCompletionStop,linkedCompletionJump,
      linkedCompletionInput,linkedCompletionSite,jumpMemberSite,Site.state,seed,u,
      Assembly.stopAfter,Assembly.chargedPrepare,EVM.State.incrPC] using h
  · exact linked_completion_debit (seed 27 true) tail (by decide)

theorem legal_boundaries :
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 11 false) []) =
      .ok (.success (observed 11 false []) .empty) ∧
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 11 false) (List.replicate 1022 (u 258))) =
      .ok (.success (observed 11 false (List.replicate 1022 (u 258))) .empty) := by
  exact ⟨execute _ (by decide),execute _ (by simp only [List.length_replicate];decide)⟩

theorem exact_gas_and_fuel_refusals :
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 10 false) tail) = .error .OutOfGass ∧
    EVM.X 3 program.validJumps (linkedCompletionInput (seed 11 false) tail) = .error .OutOfFuel := by
  constructor
  · have branch := (linked_completion_branch (seed 10 false) tail (by decide) (by decide) 2).2
    refine branch.trans ?_
    conv_lhs => rw [Assembly.X_unfold]
    rfl
  · let current := linkedCompletionJump (seed 11 false) tail
    let stopping := linkedCompletionStop (seed 11 false) tail
    have branch := (linked_completion_branch (seed 11 false) tail (by decide) (by decide) 1).2
    have decoded : EVM.decode current.executionEnv.code current.pc = some (.JUMPDEST,none) := by rfl
    have gate : Assembly.driverGate program.validJumps current .JUMPDEST = .ok (current,1) :=
      completion_terminal_gate _ current .JUMPDEST 1 (Or.inl ⟨rfl,rfl⟩) (by decide) (by decide)
    have step : EVM.step 1 1 (some (.JUMPDEST,none)) current = .ok stopping := by rfl
    have dest := Assembly.X_continue 0 program.validJumps current current stopping
      (.JUMPDEST,none) 1 decoded gate step (by unfold Assembly.NonhaltingOpcode;decide)
    have stopDecoded : EVM.decode stopping.executionEnv.code stopping.pc = some (.STOP,none) := by rfl
    have stopGate : Assembly.driverGate program.validJumps stopping .STOP = .ok (stopping,0) :=
      completion_terminal_gate _ stopping .STOP 0 (Or.inr ⟨rfl,rfl⟩) (Nat.zero_le _) (by decide)
    refine branch.trans (dest.trans ?_)
    conv_lhs => rw [Assembly.X_unfold]
    simp only [stopDecoded,Option.getD_some,stopGate,EVM.step,bind,Except.bind]

theorem complete_ordered_terminal_state :
    linkedCompletionOutput (seed 11 false) tail = observed 11 false tail ∧
    (linkedCompletionInput (seed 11 false) tail).stack = [u 72,u 1,u 258,u 513] ∧
    (observed 11 false tail).stack = [u 258,u 513] ∧
    (observed 11 false tail).stack ≠ [u 513,u 258] ∧
    (observed 11 false tail).executionEnv.code.data.toList =
      [0x5b,0x5b,0x15,0x7f] ++ List.replicate 31 0 ++
        [0x48,0x57,0x5b,0x7f] ++ List.replicate 32 0 ++ [0x56,0x5b,0x00] ∧
    (observed 11 false tail).pc = u 73 ∧
    (observed 11 false tail).pc ≠ u 74 ∧
    (observed 11 false tail).gasAvailable = u 0 ∧
    (observed 11 false tail).execLength = 44 ∧
    (observed 11 false tail).returnData.data.toList = [] ∧
    (observed 11 false tail).returnData.data.toList ≠ [0xcc,0xdd] ∧
    (observed 11 false tail).H_return.data.toList = [0xee,0xff] ∧
    (observed 11 false tail).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed 11 false tail).activeWords = u 1 ∧
    (observed 11 false tail).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed 11 false tail).accountMap = WordPushFixtures.accounts ∧
    (observed 11 false tail).σ₀ = WordPushFixtures.accounts ∧
    (observed 11 false tail).substate = (seed 11 false).substate := by
  exact ⟨rfl,rfl,rfl,by decide,rfl,rfl,by decide,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms exact_budget_static
#print axioms writable_excess
#print axioms legal_boundaries
#print axioms exact_gas_and_fuel_refusals
#print axioms complete_ordered_terminal_state
end SolidityBridge.RoadmapV15.P10.LinkedCompletionControls
