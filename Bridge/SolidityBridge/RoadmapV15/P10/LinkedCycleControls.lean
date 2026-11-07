import SolidityBridge.RoadmapV15.P10.LinkedCycle
import SolidityBridge.RoadmapV15.P10.LinkedProgramControls

/-! Populated finite-cycle clients with the certified linked array.
The cycle returns to JUMPDEST0, not a terminal success; no invariant is assumed. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedCycleControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts spill)

def observed (perm : Bool) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  {linkedZeroInput (seed 30 perm) a words with
    pc := u 0,gasAvailable := u 0,execLength := 49,
    stack := words.map (fun w => UInt256.mk w.toFin)}

theorem exact_budget (perm : Bool) (a : Scalar.Word)
    (words : Scalar.Stack) (nonzero : a ≠ 0) (room : words.length+2 ≤ 1024) :
    Assembly.driverSteps 8 9 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 perm) a words) =
      .ok (observed perm a words) := by
  have h := (linked_cycle (seed 30 perm) a words nonzero room
    (by change 30 ≤ 30;decide) 0).1
  have gasEq : (linkedCycleOutput (seed 30 perm) a words).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact linked_cycle_debit (seed 30 perm) a words (by change 30 ≤ 30;decide)
  have same : linkedCycleOutput (seed 30 perm) a words = observed perm a words := by
    change ({linkedZeroInput (seed 30 perm) a words with
      pc := u 0,gasAvailable := (linkedCycleOutput (seed 30 perm) a words).gasAvailable,
      execLength := 49,stack := words.map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
    rw [gasEq]
    rfl
  rw [same] at h
  exact h

theorem signed_and_nonzero_clients :
    Assembly.driverSteps 8 9 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 false) 258 spill) =
      .ok (observed false 258 spill) ∧
    Assembly.driverSteps 8 9 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 true) (BitVec.ofInt 256 (-1)) spill) =
      .ok (observed true (BitVec.ofInt 256 (-1)) spill) := by
  exact ⟨exact_budget _ _ _ (by decide) (by decide),exact_budget _ _ _ (by decide) (by decide)⟩

theorem legal_boundaries :
    Assembly.driverSteps 8 9 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 false) 1 []) =
      .ok (observed false 1 []) ∧
    Assembly.driverSteps 8 9 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 true) 1 (List.replicate 1022 513)) =
      .ok (observed true 1 (List.replicate 1022 513)) := by
  exact ⟨exact_budget _ _ _ (by decide) (by decide),
    exact_budget _ _ _ (by decide) (by simp only [List.length_replicate];decide)⟩

theorem resource_refusals :
    EVM.X 10 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 false) 1 spill) = .error .OutOfGass ∧
    EVM.X 9 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 29 false) 1 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 8 8 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 false) 1 spill) = .error .OutOfFuel := by
  constructor
  · have h := (linked_cycle (seed 30 false) 1 spill
      (by decide) (by decide) (by decide) 1).2
    refine h.trans ?_
    conv_lhs => rw [Assembly.X_unfold]
    rfl
  · constructor
    · have h := (linked_backedge_prefix LinkedJumpFixtures.program.validJumps (seed 29 false) 1 spill
        (by decide) (by decide) (by decide) 1).2
      refine h.trans ?_
      conv_lhs => rw [Assembly.X_unfold]
      rfl
    · have h := (linked_backedge_prefix LinkedJumpFixtures.program.validJumps (seed 30 false) 1 spill
        (by decide) (by decide) (by decide) 0).1
      rw [fetched_steps_append 7 1 0,h]
      rfl

def zeroObserved : EVM.State :=
  {linkedZeroInput (seed 30 false) 0 spill with
    pc := u 73,gasAvailable := u 11,execLength := 48,
    stack := spill.map (fun w => UInt256.mk w.toFin),returnData := .empty}

/-- Same table, gas, fuel and spill; only the source operand changes to zero. -/
theorem nonzero_required :
    EVM.X 9 LinkedJumpFixtures.program.validJumps (linkedZeroInput (seed 30 false) 0 spill) =
      .ok (.success zeroObserved .empty) ∧
    zeroObserved.pc ≠ (observed false 1 spill).pc ∧
    zeroObserved.gasAvailable = u 11 ∧ zeroObserved.returnData = .empty := by
  have h := linked_program_exit (seed 30 false) spill (by decide) (by decide) 1
  have gasEq : (linkedProgramOutput (seed 30 false) spill).gasAvailable = u 11 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact linked_program_debit (seed 30 false) spill (by decide)
  have same : linkedProgramOutput (seed 30 false) spill = zeroObserved := by
    change ({linkedZeroInput (seed 30 false) 0 spill with
      pc := u 73,gasAvailable := (linkedProgramOutput (seed 30 false) spill).gasAvailable,
      execLength := 48,stack := spill.map (fun w => UInt256.mk w.toFin),returnData := .empty} : EVM.State) = _
    rw [gasEq]
    rfl
  rw [same] at h
  exact ⟨h,by decide,rfl,rfl⟩

/-- The actual JUMP0 needs the supplied table to contain byte zero. -/
theorem backedge_target_required :
    EVM.X 9 #[u 73] (linkedZeroInput (seed 30 false) 1 spill) = .error .BadJumpDestination := by
  have h := (linked_backedge_prefix #[u 73] (seed 30 false) 1 spill
    (by decide) (by decide) (by decide) 1).2
  refine h.trans ?_
  conv_lhs => rw [Assembly.X_unfold]
  rfl

theorem complete_ordered_boundary :
    (observed false 258 spill).stack = [u 258,u 513] ∧
    (observed false 258 spill).stack ≠ [u 513,u 258] ∧
    (observed false 258 spill).pc = u 0 ∧
    (observed false 258 spill).pc ≠ u 73 ∧
    (observed false 258 spill).gasAvailable = u 0 ∧
    (observed false 258 spill).execLength = 49 ∧
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
    (observed false 258 spill).substate = (seed 30 false).substate := by
  exact ⟨rfl,by decide,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl⟩

#print axioms exact_budget
#print axioms signed_and_nonzero_clients
#print axioms legal_boundaries
#print axioms resource_refusals
#print axioms nonzero_required
#print axioms backedge_target_required
#print axioms complete_ordered_boundary
end SolidityBridge.RoadmapV15.P10.LinkedCycleControls
