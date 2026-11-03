import Solidity.Source.Eval

/-!
# Explicit-plan Source frame operations (H16 execution leaf)

These operations run in the actual Source EM and use its existing event
emitter. The immutable plan is a parameter, never a mutable St field. None
is the legacy identity even if arbitrary stale cursor metadata is present.
The frame operation owns only cursor entry/pop: it does not perform logical
rollback, select a catch, dispatch a call or finalize a transaction. Those
remain existing Source operations and still require integration at their
real boundaries. Root indexing/funding decisions are not made here.
-/
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
attempt so a handler in body cannot turn a resource stop into success. Pop
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

/-- Execute the existing Source emitter, then account for its actual event.
A zero cut emits nothing. Receipts must be emitted outside active budgets
by the eventual root driver; this helper does not classify receipt events. -/
def emit (plan : RuntimePlan) (event : Roadmap.Event) : EM E Γ Unit :=
  match plan with
  | none => Source.emitEvent event
  | some _ => do
    check plan
    Source.emitEvent event
    modSt fun s => { s with resource := s.resource.advanceEvent }
    check plan

end Solidity.Source.FailureExecution
