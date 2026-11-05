import Solidity.Semantics.StaticInvocation
import Solidity.Semantics.CallResume
/-! Mode-dependent resumption of a typed caller after one external frame.
This is the storage-only state operator for callback integration. It does not
itself enforce attempted-write refusal or issue source/native provenance. -/
namespace Solidity
variable {C : Contract} {Γ : Ctx}

/-- Both returning and failed child frames project to the same typed resumption
operator. Rollback is already accounted for by Frame's visible-state policy. -/
theorem StaticInvocation.Frame.resumeCall {mode : CallMode} {σ τ : State C Γ}
    {outcome : StaticInvocation.Outcome} (frame : Frame mode σ outcome τ) :
    τ = σ.resumeCall mode τ.storage τ.net τ.selfBalance := by
  cases mode with
  | call => exact frame.havoc_form
  | static =>
    have shape := frame.havoc_form
    rw [frame.storage] at shape
    exact shape

/-- An existing frame identifies resumption with its exact visible havoc projections.
This uses no additional storage, ledger or balance assumption. -/
theorem StaticInvocation.Frame.resumeCall_eq_havoc {mode : CallMode} {σ τ : State C Γ}
    {outcome : StaticInvocation.Outcome} (frame : Frame mode σ outcome τ) :
    σ.resumeCall mode τ.storage τ.net τ.selfBalance =
      σ.havoc τ.storage τ.net τ.selfBalance := by
  simp only [← frame.resumeCall, ← frame.havoc_form]

/-- info: 'Solidity.State.resumeCall_call' depends on axioms: [propext] -/
#guard_msgs in
#print axioms State.resumeCall_call
/-- info: 'Solidity.State.resumeCall_static' depends on axioms: [propext] -/
#guard_msgs in
#print axioms State.resumeCall_static
/-- info: 'Solidity.StaticInvocation.Frame.resumeCall' depends on axioms: [propext] -/
#guard_msgs in
#print axioms StaticInvocation.Frame.resumeCall
end Solidity
