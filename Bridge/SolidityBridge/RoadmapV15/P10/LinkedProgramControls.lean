import SolidityBridge.RoadmapV15.P10.LinkedProgram
import SolidityBridge.RoadmapV15.P10.LinkedResourceBounds
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Full particular-program witnesses and exact boundary failures. These are
native reference executions, not source origin, transactions or fork approval. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedProgramControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts spill)
open LinkedJumpFixtures (program)

def observed (perm : Bool) (words : Scalar.Stack) : EVM.State :=
  {linkedZeroInput (seed 19 perm) 0 words with
    pc := u 73,gasAvailable := u 0,
    execLength := 48,stack := words.map (fun w => UInt256.mk w.toFin),returnData := .empty}

theorem exact_budget (perm : Bool) (words : Scalar.Stack) (room : words.length+2 ≤ 1024) :
    EVM.X 8 program.validJumps (linkedZeroInput (seed 19 perm) 0 words) =
      .ok (.success (observed perm words) .empty) := by
  have h := linked_program_exit (seed 19 perm) words room (by change 19 ≤ 19;decide) 0
  have gasEq : (linkedProgramOutput (seed 19 perm) words).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact linked_program_debit (seed 19 perm) words (by change 19 ≤ 19;decide)
  have same : linkedProgramOutput (seed 19 perm) words = observed perm words := by
    change ({linkedZeroInput (seed 19 perm) 0 words with
      pc := u 73,
      gasAvailable := (linkedProgramOutput (seed 19 perm) words).gasAvailable,
      execLength := 48,stack := words.map (fun w => UInt256.mk w.toFin),returnData := .empty} : EVM.State) = _
    rw [gasEq]
    rfl
  rw [same] at h
  exact h

theorem legal_boundaries :
    EVM.X 8 program.validJumps (linkedZeroInput (seed 19 false) 0 []) =
      .ok (.success (observed false []) .empty) ∧
    EVM.X 8 program.validJumps (linkedZeroInput (seed 19 true) 0 (List.replicate 1022 513)) =
      .ok (.success (observed true (List.replicate 1022 513)) .empty) := by
  exact ⟨exact_budget _ _ (by decide),
    exact_budget _ _ (by simp only [List.length_replicate];decide)⟩

theorem resource_refusals :
    EVM.X 8 program.validJumps (linkedZeroInput (seed 18 false) 0 spill) = .error .OutOfGass ∧
    EVM.X 7 program.validJumps (linkedZeroInput (seed 19 false) 0 spill) = .error .OutOfFuel := by
  constructor
  · have front := (linked_push_prefix program.validJumps (seed 18 false) 0 spill
      (by decide) (by decide) 3).2
    rw [linked_zero_branch_alignment] at front
    have gas : (linkedPushSeed (seed 18 false) 0 spill).gasAvailable.toNat = 10 :=
      linked_push_debit (seed 18 false) 0 spill (by decide)
    exact front.trans (linked_completion_ten_gas _ _ (by decide) gas 1)
  · have front := (linked_push_prefix program.validJumps (seed 19 false) 0 spill
      (by decide) (by decide) 2).2
    rw [linked_zero_branch_alignment] at front
    have gas : 11 ≤ (linkedPushSeed (seed 19 false) 0 spill).gasAvailable.toNat := by
      rw [linked_push_debit _ _ _ (by decide)]
      decide
    exact front.trans (linked_completion_three_fuel _ _ (by decide) gas)

theorem wrong_jump_table :
    EVM.X 8 #[u 73] (linkedZeroInput (seed 19 false) 0 spill) = .error .BadJumpDestination := by
  have front := (linked_push_prefix #[u 73] (seed 19 false) 0 spill (by decide) (by decide) 3).2
  rw [linked_zero_branch_alignment] at front
  have gas : 10 ≤ (linkedPushSeed (seed 19 false) 0 spill).gasAvailable.toNat := by
    rw [linked_push_debit _ _ _ (by decide)]
    decide
  exact front.trans (jump_missing_refusal #[u 73]
    (linkedCompletionSite (linkedPushSeed (seed 19 false) 0 spill)) (u 72) (u 1)
    (spill.map (fun w : Scalar.Word => UInt256.mk w.toFin)) (by decide) (by decide) gas 3).2

theorem nonzero_push_prefix :
    Assembly.driverSteps 4 5 #[u 73]
      (linkedZeroInput (seed 8 true) (BitVec.ofInt 256 (-1)) spill) =
      .ok (linkedPushOutput (seed 8 true) (BitVec.ofInt 256 (-1)) spill) ∧
    (linkedPushOutput (seed 8 true) (BitVec.ofInt 256 (-1)) spill).stack = [u 72,u 0,u 258,u 513] ∧
    (linkedPushSeed (seed 8 true) (BitVec.ofInt 256 (-1)) spill).gasAvailable.toNat = 0 := by
  exact ⟨(linked_push_prefix _ _ _ _ (by decide) (by decide) 0).1,rfl,
    linked_push_debit _ _ _ (by decide)⟩

theorem complete_ordered_outcome :
    (observed false spill).stack = [u 258,u 513] ∧
    (observed false spill).stack ≠ [u 513,u 258] ∧
    (observed false spill).pc = u 73 ∧
    (observed false spill).pc ≠ u 74 ∧
    (observed false spill).gasAvailable = u 0 ∧
    (observed false spill).execLength = 48 ∧
    (observed false spill).executionEnv.code.data.toList =
      [0x5b,0x5b,0x15,0x7f] ++ List.replicate 31 0 ++ [0x48,0x57,0x5b,0x7f] ++
        List.replicate 32 0 ++ [0x56,0x5b,0x00] ∧
    (observed false spill).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed false spill).activeWords = u 1 ∧
    (observed false spill).returnData.data.toList = [] ∧
    (observed false spill).returnData.data.toList ≠ [0xcc,0xdd] ∧
    (observed false spill).H_return.data.toList = [0xee,0xff] ∧
    (observed false spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed false spill).accountMap = accounts ∧
    (observed false spill).σ₀ = accounts ∧
    (observed false spill).substate = (seed 19 false).substate := by
  exact ⟨rfl,by decide,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl⟩

#print axioms exact_budget
#print axioms legal_boundaries
#print axioms resource_refusals
#print axioms wrong_jump_table
#print axioms nonzero_push_prefix
#print axioms complete_ordered_outcome
end SolidityBridge.RoadmapV15.P10.LinkedProgramControls
