import SolidityBridge.RoadmapV15.P10.LinkedResourceBounds
import SolidityBridge.RoadmapV15.P10.LinkedCompletionControls

/-! Populated static/writable, full-stack and arbitrary-tail resource clients.
Complete ordered state observations are retained from the original success client.
No refused execution is represented as returning a successful caller state. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedResourceControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u)
open LinkedJumpFixtures (program tail)

/-- Both permissions have the same resource threshold for this nonwriting suffix. -/
theorem permissions (perm : Bool) :
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 10 perm) tail) = .error .OutOfGass ∧
    EVM.X 3 program.validJumps (linkedCompletionInput (seed 27 perm) tail) = .error .OutOfFuel ∧
    EVM.X 4 program.validJumps (linkedCompletionInput (seed 11 perm) tail) =
      .ok (.success (linkedCompletionOutput (seed 11 perm) tail) .empty) := by
  exact ⟨linked_completion_ten_gas _ _ (by decide) (by rfl) 1,
    linked_completion_three_fuel _ _ (by decide) (by change 11 ≤ 27;decide),
    linked_completion_execution _ _ (by decide) (by change 11 ≤ 11;decide) 0⟩

/-- Refusals occur at legal input capacity, not an unreachable overflow stack. -/
theorem full_capacity :
    EVM.X 4 program.validJumps
      (linkedCompletionInput (seed 10 false) (List.replicate 1022 (u 258))) = .error .OutOfGass ∧
    EVM.X 3 program.validJumps
      (linkedCompletionInput (seed 11 true) (List.replicate 1022 (u 513))) = .error .OutOfFuel := by
  exact ⟨linked_completion_ten_gas _ _ (by simp only [List.length_replicate];decide) rfl 1,
    linked_completion_three_fuel _ _ (by simp only [List.length_replicate];decide) (by decide)⟩

/-- Fuel exhaustion is not a successful empty result; ordered buffers survive
in the represented success state, while STOP clears only returnData. -/
theorem observed_boundary :
    EVM.X 3 program.validJumps (linkedCompletionInput (seed 11 false) tail) ≠
      .ok (.success (linkedCompletionOutput (seed 11 false) tail) .empty) ∧
    (linkedCompletionOutput (seed 11 false) tail).stack = [u 258,u 513] ∧
    (linkedCompletionOutput (seed 11 false) tail).memory.data.toList =
      [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (linkedCompletionOutput (seed 11 false) tail).returnData.data.toList = [] ∧
    (linkedCompletionOutput (seed 11 false) tail).H_return.data.toList = [0xee,0xff] := by
  constructor
  · rw [linked_completion_three_fuel _ _ (by decide) (by decide)]
    intro h
    cases h
  · exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms permissions
#print axioms full_capacity
#print axioms observed_boundary
end SolidityBridge.RoadmapV15.P10.LinkedResourceControls
