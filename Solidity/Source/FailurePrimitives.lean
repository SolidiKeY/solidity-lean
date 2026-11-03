import Solidity.Source.Machine

/-! Shared actual-EM failure primitives below Eval. Bodies are extracted
unchanged from FailureMachine; this module installs no evaluator hooks. -/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx}

/-- A reached budget halts exceptionally while retaining its exact owner. -/
def check (plan : RuntimePlan) : EM E Γ Unit :=
  match plan with
  | none => pure ()
  | some _ => do
    let cursor := (← st).resource
    match cursor.stop? with
    | none => pure ()
    | some stop =>
      modSt fun s => { s with resource := { cursor with pending := some stop } }
      halt (.revert [])

/-- Disabled executions do not consult stale cursor metadata. -/
def pending (plan : RuntimePlan) : EM E Γ Bool :=
  match plan with
  | none => pure false
  | some _ => do return (← st).resource.pending.isSome

/-- Enter one compiled-system activation after the caller's refusal checks.
An existing ancestor/request stop prevents entry. Pre/post checks are inside
attempt so an ordinary halt handler cannot turn a resource stop into success.
Body code must retain the cursor protocol; arbitrary EM.modSt cursor forgery is
not prohibited by this helper type. Actual AST/evaluator integration must prove
that invariant rather than assume execution agreement. Pop
only this activation on every body result, retaining ancestor/request stops
and the monotone ordinal. Horizon exhaustion stays timeout. -/
def frame {α : Type} (plan : RuntimePlan) (body : EM E Γ α) : EM E Γ α :=
  match plan with
  | none => body
  | some points => do
    check plan
    modSt fun s => { s with resource := s.resource.enterFrame points }
    let result ← attempt do
      check plan
      let value ← body
      check plan
      pure value
    modSt fun s => { s with resource := s.resource.leaveFrame }
    match result with
    | .ok value => pure value
    | .error why => halt why

end Solidity.Source.FailureExecution
