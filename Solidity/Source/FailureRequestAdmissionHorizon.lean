import Solidity.Source.FailureRequestAdmission
import Solidity.Source.FailureRequestHorizon
import Solidity.Source.FailureScopeStability

/-! Horizon transport of the existing exact-Nat admission API. This extends
requestValueScope rather than installing another admission/runtime operation.
The original plan remains closed over by the body; only its current request
fate is normalized by the existing operation. Session/fee wiring stays open. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx} {α : Type}

theorem requestValueScope_grow (points : Roadmap.Evm.FailurePoints) (request : Roadmap.Request)
    {body : Nat → EM E Γ α} (h : ∀ balance, Grow (body balance)) :
    Grow (requestValueScope points request body) := by
  unfold requestValueScope
  grow_go [requestScope_grow,h]

theorem requestValueScope_below (points : Roadmap.Evm.FailurePoints) (request : Roadmap.Request)
    {body later : Nat → EM E Γ α} (h : ∀ balance, Below (body balance) (later balance)) :
    Below (requestValueScope points request body) (requestValueScope points request later) := by
  unfold requestValueScope
  below_go [requestScope_below,h]

theorem requestValueScope_approx (points : Roadmap.Evm.FailurePoints) (request : Roadmap.Request)
    {body later : Nat → EM E Γ α} (h : ∀ balance, Approx (body balance) (later balance)) :
    Approx (requestValueScope points request body) (requestValueScope points request later) := by
  have bodyGrow : ∀ balance, Grow (body balance) := fun balance => (h balance).1
  have laterGrow : ∀ balance, Grow (later balance) := fun balance => (h balance).2.1
  unfold requestValueScope
  approx_go [requestScope_approx,h] [requestScope_grow,bodyGrow,laterGrow] [] []

end Solidity.Source.FailureExecution
