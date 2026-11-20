import Solidity.Backend.InternalFlow.CallsProgramBridge

/-! Nonvacuity and exhaustion checks for the bridge on the existing fixture. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CallsProgramBridge
open Evm Evm.Memory ScalarSourceCompiler
open DisjointScalarReturn.Client (F)

theorem fixture_cost (depth : Nat) (enough : 3 < depth) :
    cost depth ScalarContinuation.final = 0 := by
  have arena : (Client.selected depth).plan.arenaWords ScalarContinuation.final = 6 :=
    ScalarReentry.arena depth
  simp only [cost, arena, Nat.le_refl, if_true, Client.actual_source depth enough]

theorem fixture_input (depth : Nat) (enough : 3 < depth) :
    StateRepr 1 1 16 F ScalarContinuation.final ScalarContinuation.finalBase ScalarContinuation.target ∧
    1 + (program depth).need ≤ 16 ∧
    AllocationInput 1 16 ((program depth).cost ScalarContinuation.final)
      ScalarContinuation.final ScalarContinuation.finalBase ScalarContinuation.target :=
  ⟨(Client.entered depth).represented, by change 16 ≤ 16; decide, .inl (fixture_cost depth enough)⟩

/-- Initialization preserves the existing fixture machine, whose cursor is 10. -/
theorem fixture_prepared : prepared ScalarContinuation.target = ScalarContinuation.target := by
  have cursor : ScalarContinuation.target.mem 9 = w[10] := ScalarReentry.prefix_cursor
  unfold prepared writeMachine
  congr 1
  funext address
  unfold upd
  split
  · rename_i same
    subst address
    exact cursor.symm
  · rfl

theorem fixture_target : run (program 4).code ScalarContinuation.target =
    .ok ScalarReentry.Endpoint.machine 0 := by
  change run (initCode ++ (Client.selected 4).plan.code) ScalarContinuation.target = _
  rw [run_append_ok (prefix_run _), fixture_prepared]
  exact Client.target

/-- Depth zero remains outside all allocation inputs, whatever the machine. -/
theorem exhausted_cost : cost 0 ScalarContinuation.final = W := by
  unfold cost
  rw [Controls.exhausted_boundary.1]
  split <;> rfl

theorem exhausted_not_input (frame : Nat) (base : Nat → Fin W) (m : Machine) :
    ¬ AllocationInput 1 frame ((program 0).cost ScalarContinuation.final)
      ScalarContinuation.final base m := by
  intro capacity
  have zero := (capacity_facts capacity).1
  rw [exhausted_cost] at zero
  exact (Nat.ne_of_gt W_pos) zero

#print axioms correct
#print axioms fixture_input
#print axioms fixture_target
#print axioms exhausted_not_input
end Solidity.Backend.InternalFlow.RuntimeFrame.CallsProgramBridge
