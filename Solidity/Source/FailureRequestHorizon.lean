import Solidity.Source.FailureFrameHorizon
import Solidity.Source.FailureRequest

/-! Event growth and horizon approximation of the actual request scope.
These are combinator laws, not whole evaluator coherence, fee installation,
fixed-plan session consistency or a P8 realization inhabitant. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx} {α : Type}

theorem requestScope_grow (points : Roadmap.Evm.FailurePoints)
    {body : Nat → EM E Γ α} (grow : ∀ balance, Grow (body balance)) :
    Grow (requestScope points body) := by
  unfold requestScope
  grow_go [check_grow, grow]

theorem requestScope_approx (points : Roadmap.Evm.FailurePoints)
    {body later : Nat → EM E Γ α} (approx : ∀ balance, Approx (body balance) (later balance)) :
    Approx (requestScope points body) (requestScope points later) := by
  unfold requestScope
  refine Approx.bind (Approx.refl (by grow_go [])) fun state => ?_
  by_cases quiet : state.resource.quiescent = true
  · simp only [dif_pos quiet]
    refine Approx.bind (Approx.refl (by grow_go [])) fun _ => ?_
    split
    · exact Approx.refl (by grow_go [])
    · refine Approx.attempt_bind ?_ (fun _ => Approx.refl (by grow_go []))
        (fun _ => ⟨rfl, rfl⟩)
      approx_go [approx] [check_grow] [] []
  · simp only [dif_neg quiet]
    exact Approx.refl (by grow_go [])

end Solidity.Source.FailureExecution

/-- info: 'Solidity.Source.FailureExecution.requestScope_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.requestScope_grow
/-- info: 'Solidity.Source.FailureExecution.requestScope_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.requestScope_approx
