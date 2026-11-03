import Solidity.Backend.Passes.PositiveAllocationFailure
namespace Solidity.Backend.Passes.PositiveAllocationFailure.Controls
open Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
def nearCursor : Fin W := ⟨W-3,by decide⟩
def nearTarget : Machine := writeMachine (machine nearCursor) 1 w[2]
/-- The stale one-word estimate still physically fits after the assignment. -/
theorem stale_budget_fits : AllocationInput 1 16 (selected.checked.cost before)
    after base nearTarget := by
  rw [initial_cost]
  exact .inr ⟨by decide,nearCursor,
    ((initial nearCursor (by decide)).2).localWrite 1 (by decide) (by decide) w[2],by decide⟩

/-- The SAME header cannot cover the actual reached three-word demand. -/
theorem reached_budget_refused : ¬ AllocationInput 1 16 (selected.checked.cost after)
    after base nearTarget := by
  rw [reached_cost]
  rintro (zero | ⟨positive,actual,allocator,space⟩)
  · cases zero
  · have header : Word.val nearCursor = .val actual := allocator.arrays.free.cell
    have same : nearCursor = actual := Word.val.inj header
    cases same
    change W-3+3 < W at space
    have enough : 3 ≤ W := by decide
    omega

def prefixCode := AssignedBareRevert.assignmentStage
  (.here : Idx Γ (.val .uint)) operand valueCode
def code := prefixCode.code ++ (V3BareRevertProducer.plan selected 8 8).code
def target (tail : List Word) := writeMachine {machine cursor with stack := tail} 1 w[2]
def cells : List Nat := [1,0,8,9]

theorem joined_source :
    (Prog.cons (.assignLocal (.here : Idx Γ (.val .uint)) operand)
      (.cons statement .nil)).run before = .error .revert := instantiated.1

theorem physical (tail : List Word) :
    prefixCode.Input 1 16 base before {machine cursor with stack := tail} ∧
    run prefixCode.code {machine cursor with stack := tail} = .ok (target tail) 0 ∧
    MappedOutput prefixCode 1 16 base before {machine cursor with stack := tail}
      after (target tail) base ∧
    V3BareRevertProducer.admitted selected 8 8 1 16 after base (target tail) 10 ∧
    run (V3BareRevertProducer.plan selected 8 8).code (target tail) = .revert ∧
    run code {machine cursor with stack := tail} = .revert := by
  obtain ⟨word,repr,runs⟩ := instantiated.2
  have fixed : word = w[2] := Restored.value_unique repr (ReprV.uint_of rfl)
  subst word
  exact runs tail

theorem initial_observations : cells.map (machine cursor).mem = [w[0],w[64],w[10],w[99]] := rfl

theorem reached_observations (tail : List Word) :
    (cells.map (target tail).mem,(target tail).stack) = ([w[2],w[64],w[10],w[99]],tail) := rfl

/-- No post-failure machine is asserted. Saved stack is observed at the real
successful assignment prefix, before the allocating body fails. -/
theorem prefix_saved_head (tail : List Word) :
    run prefixCode.code {machine cursor with stack := w[77] :: tail} =
      .ok (target (w[77] :: tail)) 0 ∧
    (target (w[77] :: tail)).stack ≠ w[78] :: tail := by
  refine ⟨(physical (w[77] :: tail)).2.1,?_⟩
  change w[77] :: tail ≠ w[78] :: tail
  intro same
  exact (by decide : (w[77] : Word) ≠ w[78]) (List.cons.inj same).1

theorem reached_input_refused_near_end :
    ¬ V3BareRevertProducer.admitted selected 8 8 1 16 after base nearTarget 10 := by
  intro input
  exact reached_budget_refused input.capacity

theorem prefix_source :
    (Prog.cons (.assignLocal (.here : Idx Γ (.val .uint)) operand) .nil).run before =
      .ok ⟨after,List.prefix_refl _⟩ := by
  first | rfl | decide | omega | with_unfolding_all rfl

/-- Omitting the assignment loses representation of the reached scalar. -/
theorem skipped_assignment_refused :
    ¬ StateRepr 1 1 16 F after base (machine cursor) := by
  intro represented
  have same : (w[0] : Word) = w[2] := Restored.value_unique
    (represented.core.vals (.here : Idx Γ (.val .uint))) (ReprV.uint_of rfl)
  exact (by decide : (w[0] : Word) ≠ w[2]) same

end Solidity.Backend.Passes.PositiveAllocationFailure.Controls
