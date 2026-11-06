import SolidityBridge.RoadmapV15.P10.LinkedBackedgePush
import SolidityBridge.RoadmapV15.P10.LinkedProgramControls

/-! Populated final PUSH clients, both permissions and arbitrary tables.
The prefix is not a terminal success; operand zero takes the other real branch. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedBackedgePushControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts spill)

def observed (perm : Bool) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  {linkedZeroInput (seed 22 perm) a words with
    pc := u 71,gasAvailable := u 0,execLength := 48,
    stack := (0::words).map (fun w => UInt256.mk w.toFin)}

theorem exact_budget (valid : Array UInt256) (perm : Bool) (a : Scalar.Word)
    (words : Scalar.Stack) (nonzero : a ≠ 0) (room : words.length+2 ≤ 1024) :
    Assembly.driverSteps 7 8 valid (linkedZeroInput (seed 22 perm) a words) =
      .ok (observed perm a words) := by
  have h := (linked_backedge_prefix valid (seed 22 perm) a words nonzero room
    (by change 22 ≤ 22;decide) 0).1
  have gasEq : (linkedBackedgePush (seed 22 perm) a words).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact linked_backedge_debit (seed 22 perm) a words (by change 22 ≤ 22;decide)
  have same : linkedBackedgePush (seed 22 perm) a words = observed perm a words := by
    change ({linkedZeroInput (seed 22 perm) a words with
      pc := u 71,gasAvailable := (linkedBackedgePush (seed 22 perm) a words).gasAvailable,
      execLength := 48,stack := (0::words).map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
    rw [gasEq]
    rfl
  rw [same] at h
  exact h

theorem signed_and_nonzero_clients :
    Assembly.driverSteps 7 8 #[] (linkedZeroInput (seed 22 false) 258 spill) =
      .ok (observed false 258 spill) ∧
    Assembly.driverSteps 7 8 #[u 73] (linkedZeroInput (seed 22 true) (BitVec.ofInt 256 (-1)) spill) =
      .ok (observed true (BitVec.ofInt 256 (-1)) spill) := by
  exact ⟨exact_budget _ _ _ _ (by decide) (by decide),exact_budget _ _ _ _ (by decide) (by decide)⟩

theorem legal_boundaries :
    Assembly.driverSteps 7 8 #[] (linkedZeroInput (seed 22 false) 1 []) =
      .ok (observed false 1 []) ∧
    Assembly.driverSteps 7 8 #[u 73] (linkedZeroInput (seed 22 true) 1 (List.replicate 1022 513)) =
      .ok (observed true 1 (List.replicate 1022 513)) := by
  exact ⟨exact_budget _ _ _ _ (by decide) (by decide),
    exact_budget _ _ _ _ (by decide) (by simp only [List.length_replicate];decide)⟩

theorem resource_refusals :
    EVM.X 9 #[u 73] (linkedZeroInput (seed 22 false) 1 spill) = .error .OutOfGass ∧
    EVM.X 8 #[u 73] (linkedZeroInput (seed 21 false) 1 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 7 7 #[u 73] (linkedZeroInput (seed 22 false) 1 spill) = .error .OutOfFuel := by
  constructor
  · have h := (linked_backedge_prefix #[u 73] (seed 22 false) 1 spill
      (by decide) (by decide) (by decide) 1).2
    refine h.trans ?_
    conv_lhs => rw [Assembly.X_unfold]
    rfl
  · constructor
    · have h := (linked_fallthrough_body #[u 73] (seed 21 false) 1 spill
        (by decide) (by decide) (by decide) 1).2
      refine h.trans ?_
      conv_lhs => rw [Assembly.X_unfold]
      rfl
    · have h := (linked_fallthrough_body #[u 73] (seed 22 false) 1 spill
        (by decide) (by decide) (by decide) 0).1
      rw [fetched_steps_append 6 1 0,h]
      rfl

/-- Dropping the nonzero condition changes the actual branch and outcome. -/
theorem nonzero_required :
    EVM.X 8 #[u 73] (linkedZeroInput (seed 22 false) 0 spill) = .error .BadJumpDestination := by
  have front := (linked_push_prefix #[u 73] (seed 22 false) 0 spill (by decide) (by decide) 3).2
  rw [linked_zero_branch_alignment] at front
  have gas : 10 ≤ (linkedPushSeed (seed 22 false) 0 spill).gasAvailable.toNat := by
    rw [linked_push_debit _ _ _ (by decide)]
    decide
  exact front.trans (jump_missing_refusal #[u 73]
    (linkedCompletionSite (linkedPushSeed (seed 22 false) 0 spill)) (u 72) (u 1)
    (spill.map (fun w : Scalar.Word => UInt256.mk w.toFin)) (by decide) (by decide) gas 3).2

theorem complete_ordered_boundary :
    (observed false 258 spill).stack = [u 0,u 258,u 513] ∧
    (observed false 258 spill).stack ≠ [u 513,u 258,u 0] ∧
    (observed false 258 spill).pc = u 71 ∧
    (observed false 258 spill).pc ≠ u 73 ∧
    (observed false 258 spill).gasAvailable = u 0 ∧
    (observed false 258 spill).execLength = 48 ∧
    (observed false 258 spill).executionEnv.code.data.toList =
      [0x5b,0x5b,0x15,0x7f] ++ List.replicate 31 0 ++ [0x48,0x57,0x5b,0x7f] ++
        List.replicate 32 0 ++ [0x56,0x5b,0x00] ∧
    (observed false 258 spill).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed false 258 spill).activeWords = u 1 ∧
    (observed false 258 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (observed false 258 spill).returnData.data.toList ≠ [] ∧
    (observed false 258 spill).H_return.data.toList = [0xee,0xff] ∧
    (observed false 258 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed false 258 spill).accountMap = accounts ∧
    (observed false 258 spill).σ₀ = accounts ∧
    (observed false 258 spill).substate = (seed 22 false).substate := by
  exact ⟨rfl,by decide,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl⟩

#print axioms exact_budget
#print axioms signed_and_nonzero_clients
#print axioms legal_boundaries
#print axioms resource_refusals
#print axioms nonzero_required
#print axioms complete_ordered_boundary
end SolidityBridge.RoadmapV15.P10.LinkedBackedgePushControls
