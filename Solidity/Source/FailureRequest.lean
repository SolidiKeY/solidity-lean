import Solidity.Source.FailurePrimitives

/-!
# Actual EM request-budget scope

This operation consumes an actual request ordinal and consults its fate before
running a body. A dropped request never runs the body. For a running request,
the exact natural post-fee sender balance is passed to the body, not projected
or silently installed into the still-word-valued account. Entry and exit checks
prevent a caught resource halt from becoming success. Cleanup pops the request
budget on every result; it does not roll back world state or emit a receipt.

The scope has no Request/value argument and cannot enforce affordability.
The root/session driver must check request value against the exact sender
balance (dropping invalid requests), apply the passed balance using H19's exact monetary
representation, execute actual deployment/request code with the same plan, and
emit receipts outside this scope. Those integrations and consistency are open.
As with frame, arbitrary EM code can forge the cursor: this operation does not
prove cursor coherence of a general body.
-/
namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx}

/-- Scope one actual request, distinguishing dropped from every completed halt.
A non-quiescent entry is rejected instead of discarding an active owner. -/
def requestScope {α : Type} (points : Roadmap.Evm.FailurePoints)
    (body : Nat → EM E Γ α) : EM E Γ (Option α) := do
  let cursor := (← st).resource
  if h : cursor.quiescent = true then
    let (fate, entered) := cursor.enterRequest points h
    modSt fun s => { s with resource := entered }
    match fate with
    | .dropped => pure none
    | .runs balance _ =>
      let result ← attempt do
        check (some points)
        let value ← body balance
        check (some points)
        pure value
      modSt fun s => { s with resource := s.resource.leaveRequest }
      match result with
      | .ok value => pure (some value)
      | .error why => halt why
  else halt (.stuck "active request/frame at request entry")

/-- A constant fate is an executable full plan, not an assumed body outcome. -/
def constantRequestPlan (fate : Roadmap.Evm.TxFate) : Roadmap.Evm.FailurePoints where
  tx _ := fate
  frame _ := none

def requestFinished : Cursor := ⟨1,0,none,[],none⟩

/-- A drop consumes ordinal zero, preserves every non-cursor field and never
executes the arbitrary body, including a halting or state-writing body. -/
theorem request_dropped {α : Type} (l : Locals E.layout Γ) (s : St E)
    (body : Nat → EM E Γ α) :
    (requestScope (constantRequestPlan .dropped) body).run
      (l, { s with resource := Cursor.empty }) =
      (.ok none, (l, { s with resource := requestFinished })) := rfl

/-- The full natural balance, including values beyond2^256, reaches the body. -/
theorem request_balance_exact (balance : Nat) (l : Locals E.layout Γ) (s : St E) :
    (requestScope (constantRequestPlan (.runs balance none))
      (fun b => pure b : Nat → EM E Γ Nat)).run
      (l, { s with resource := Cursor.empty }) =
      (.ok (some balance), (l, { s with resource := requestFinished })) := rfl

/-- Reverts, stuck and timeout remain distinct; cleanup is not world rollback. -/
theorem request_halt_exact (balance : Nat) (why : Halt)
    (l : Locals E.layout Γ) (s : St E) :
    (requestScope (constantRequestPlan (.runs balance none))
      (fun _ => halt why : Nat → EM E Γ Unit)).run
      (l, { s with resource := Cursor.empty }) =
      (.error why, (l, { s with resource := requestFinished })) := rfl

/-- Actual EM local mutation before a full-byte revert is retained, not restored. -/
theorem request_revert_locals (balance : Nat) (data : Roadmap.Bytes)
    (before after : Locals E.layout Γ) (s : St E) :
    (requestScope (constantRequestPlan (.runs balance none))
      (fun _ => do setLocals after; halt (.revert data) : Nat → EM E Γ Unit)).run
      (before, { s with resource := Cursor.empty }) =
      (.error (.revert data), (after, { s with resource := requestFinished })) := rfl

/-- A zero cut suppresses the arbitrary body and consumes the request owner. -/
theorem request_zero_cut {α : Type} (balance : Nat)
    (l : Locals E.layout Γ) (s : St E) (body : Nat → EM E Γ α) :
    (requestScope (constantRequestPlan (.runs balance (some 0))) body).run
      (l, { s with resource := Cursor.empty }) =
      (.error (.revert []), (l, { s with resource := requestFinished })) := rfl

/-- An active frame cannot be overwritten by a new request scope. -/
theorem request_active_refused {α : Type} (points : Roadmap.Evm.FailurePoints)
    (l : Locals E.layout Γ) (s : St E) (body : Nat → EM E Γ α) :
    let active := Cursor.empty.enterFrame points
    (requestScope points body).run (l, { s with resource := active }) =
      (.error (.stuck "active request/frame at request entry"),
        (l, { s with resource := active })) := rfl

/-- A dropped ordinal is not reused. This exercises actual sequential scopes,
not a caller-supplied preinitialized request cursor or a deployment claim. -/
theorem request_dropped_then_runs (balance : Nat)
    (l : Locals E.layout Γ) (s : St E) :
    let points : Roadmap.Evm.FailurePoints := {
      tx := fun i => if i = 0 then .dropped else .runs balance none
      frame := fun _ => none }
    ((do
      let _ ← requestScope points (fun _ => halt (.stuck "poison dropped body") : Nat → EM E Γ Nat)
      requestScope points (fun b => pure b)) : EM E Γ (Option Nat)).run
      (l, { s with resource := Cursor.empty }) =
      (.ok (some balance), (l, { s with resource := ⟨2,0,none,[],none⟩ })) := rfl

end Solidity.Source.FailureExecution

/-- info: 'Solidity.Source.FailureExecution.requestScope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.requestScope

/-- info: 'Solidity.Source.FailureExecution.request_dropped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_dropped

/-- info: 'Solidity.Source.FailureExecution.request_balance_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_balance_exact

/-- info: 'Solidity.Source.FailureExecution.request_halt_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_halt_exact

/-- info: 'Solidity.Source.FailureExecution.request_revert_locals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_revert_locals

/-- info: 'Solidity.Source.FailureExecution.request_zero_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_zero_cut

/-- info: 'Solidity.Source.FailureExecution.request_active_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_active_refused

/-- info: 'Solidity.Source.FailureExecution.request_dropped_then_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.FailureExecution.request_dropped_then_runs
