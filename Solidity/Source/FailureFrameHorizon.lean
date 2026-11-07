import Solidity.Source.Horizon
import Solidity.Source.FailurePrimitives

/-! Event-prefix growth and horizon approximation for the actual scheduled
frame combinator. Body Grow/Approx are the actual Source relations; no
interpreter agreement is assumed. In particular, attempt alone need not
preserve Approx: its timeout continuation must rethrow without new events. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx} {α : Type}

theorem check_grow (plan : RuntimePlan) : Grow (check plan : EM E Γ Unit) := by
  cases plan <;> simp only [check] <;> grow_go []

theorem emit_plan_grow (plan : RuntimePlan) (event : Roadmap.Event) :
    Grow (Source.emitEvent event plan : EM E Γ Unit) := by
  cases plan <;> simp only [Source.emitEvent] <;> grow_go [check_grow]

theorem frame_grow (plan : RuntimePlan) {body : EM E Γ α} (h : Grow body) :
    Grow (frame plan body) := by
  cases plan with
  | none => exact h
  | some points =>
    simp only [frame]
    grow_go [check_grow,h]

theorem frame_approx (plan : RuntimePlan) {body later : EM E Γ α}
    (h : Approx body later) : Approx (frame plan body) (frame plan later) := by
  cases plan with
  | none => exact h
  | some points =>
    simp only [frame]
    refine Approx.bind (Approx.refl (check_grow _)) fun _ => ?_
    refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_
    refine Approx.attempt_bind ?_ (fun _ => Approx.refl (by grow_go []))
      (fun _ => ⟨rfl, rfl⟩)
    approx_go [h] [check_grow] [] []

end Solidity.Source.FailureExecution

/-- info: 'Solidity.Source.FailureExecution.check_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.check_grow

/-- info: 'Solidity.Source.FailureExecution.emit_plan_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.emit_plan_grow

/-- info: 'Solidity.Source.FailureExecution.frame_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.frame_grow

/-- info: 'Solidity.Source.FailureExecution.frame_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.frame_approx
