import Solidity.Source.FailureEvaluatorGrow
import Solidity.Source.FailureRuntimeControls

/-! Inhabited use of the closed planned evaluator induction. Full Source
fixture states remain independent frozen controls, not native comparisons. -/
namespace Solidity.Source.FailureExecution.PlannedGrow.Controls
open EM SemanticsExamples
open RuntimeControls (Ctx caller input glob data points priorEvent endState)

def action (pipeline : Roadmap.Pipeline) (plan : Roadmap.Evm.FailurePoints)
    (horizon : Nat) : EM EB RuntimeControls.Ctx (Roadmap.Outcome × Locals EB.layout []) := do
  let saved ← mark
  sub (L0 EB) (enterInstance (plan := some plan) (glob pipeline) horizon
    thisC user (word 0) data false "C" 1 saved)

theorem action_grow (pipeline : Roadmap.Pipeline) (plan : Roadmap.Evm.FailurePoints)
    (horizon : Nat) : Grow (action pipeline plan horizon) := by
  have ih := growAt (glob pipeline) (points := plan) horizon
  unfold action
  grow_go [mark_grow, ih.enterInstance]

theorem actual_fixture (pipeline : Roadmap.Pipeline) (cut : Option Nat) (horizon : Nat) :
    (action pipeline (points cut) horizon).run (caller,input) = RuntimeControls.run pipeline cut horizon := by rfl

theorem fixture_prefix (pipeline : Roadmap.Pipeline) (cut : Option Nat) (horizon : Nat) :
    input.events <+: (RuntimeControls.run pipeline cut horizon).2.2.events :=
  action_grow pipeline (points cut) horizon (caller,input)

/-- Growth is not equality of completed outcomes across different plans. -/
theorem growth_does_not_fix_outcome (pipeline : Roadmap.Pipeline) :
    ((action pipeline (points none) 20).run (caller,input)).1 ≠
      ((action pipeline (points (some 0)) 20).run (caller,input)).1 := by
  rw [actual_fixture, actual_fixture, RuntimeControls.uncut_success, RuntimeControls.zero_cut]
  intro impossible
  cases impossible

/-- Arbitrary EM mutation is not justified by the actual AST induction. -/
theorem erase_prefix_not_grow :
    ¬ Grow (modSt (fun state => { state with events := [] }) : EM EB RuntimeControls.Ctx Unit) := by
  intro claimed
  have bad := claimed (caller,input)
  change [priorEvent] <+: ([] : List Roadmap.Event) at bad
  obtain ⟨tail,impossible⟩ := bad
  cases impossible

end Solidity.Source.FailureExecution.PlannedGrow.Controls

/-- info: 'Solidity.Source.FailureExecution.PlannedGrow.growAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedGrow.growAt
/-- info: 'Solidity.Source.FailureExecution.PlannedGrow.Controls.action_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedGrow.Controls.action_grow
/-- info: 'Solidity.Source.FailureExecution.PlannedGrow.Controls.actual_fixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedGrow.Controls.actual_fixture
/-- info: 'Solidity.Source.FailureExecution.PlannedGrow.Controls.fixture_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedGrow.Controls.fixture_prefix
/-- info: 'Solidity.Source.FailureExecution.PlannedGrow.Controls.growth_does_not_fix_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedGrow.Controls.growth_does_not_fix_outcome
/-- info: 'Solidity.Source.FailureExecution.PlannedGrow.Controls.erase_prefix_not_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.PlannedGrow.Controls.erase_prefix_not_grow
