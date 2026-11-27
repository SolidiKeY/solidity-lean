import Solidity.Source.FailurePrimitives

namespace Solidity.Source.FailureExecution
open EM
variable {E : Env} {Γ : RCtx}

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

example {α : Type} (points : Roadmap.Evm.FailurePoints)
    (body : Nat → EM E Γ α) (locals : Locals E.layout Γ) (state : St E)
    (busy : state.resource.quiescent ≠ true) :
    (requestScope points body).run (locals,state) =
      (.error (.stuck "active request/frame at request entry"),(locals,state)) := by
  unfold requestScope
  change (dite (state.resource.quiescent = true) _ _ : EM E Γ (Option α)).run
    (locals,state) = _
  rw [dif_neg busy]
  rfl

example {α : Type} (points : Roadmap.Evm.FailurePoints)
    (body : Nat → EM E Γ α) (locals : Locals E.layout Γ) (state : St E)
    (quiet : state.resource.quiescent = true)
    (dropped : points.tx state.resource.nextRequest = .dropped) :
    (requestScope points body).run (locals,state) =
      (.ok none,(locals,{state with resource :=
        (state.resource.enterRequest points quiet).2})) := by
  unfold requestScope
  change (dite (state.resource.quiescent = true) _ _ : EM E Γ (Option α)).run
    (locals,state) = _
  rw [dif_pos quiet]
  simp only [Cursor.enterRequest, dropped]
  rfl


def constantRequestPlan (fate : Roadmap.Evm.TxFate) : Roadmap.Evm.FailurePoints where
  tx _ := fate
  frame _ := none

def requestFinished : Cursor := ⟨1,0,none,[],none⟩

theorem request_dropped {α : Type} (l : Locals E.layout Γ) (s : St E)
    (body : Nat → EM E Γ α) :
    (requestScope (constantRequestPlan .dropped) body).run
      (l, { s with resource := Cursor.empty }) =
      (.ok none, (l, { s with resource := requestFinished })) := rfl

theorem request_balance_exact (balance : Nat) (l : Locals E.layout Γ) (s : St E) :
    (requestScope (constantRequestPlan (.runs balance none))
      (fun b => pure b : Nat → EM E Γ Nat)).run
      (l, { s with resource := Cursor.empty }) =
      (.ok (some balance), (l, { s with resource := requestFinished })) := rfl

theorem request_halt_exact (balance : Nat) (why : Halt)
    (l : Locals E.layout Γ) (s : St E) :
    (requestScope (constantRequestPlan (.runs balance none))
      (fun _ => halt why : Nat → EM E Γ Unit)).run
      (l, { s with resource := Cursor.empty }) =
      (.error why, (l, { s with resource := requestFinished })) := rfl

theorem request_revert_locals (balance : Nat) (data : Roadmap.Bytes)
    (before after : Locals E.layout Γ) (s : St E) :
    (requestScope (constantRequestPlan (.runs balance none))
      (fun _ => do setLocals after; halt (.revert data) : Nat → EM E Γ Unit)).run
      (before, { s with resource := Cursor.empty }) =
      (.error (.revert data), (after, { s with resource := requestFinished })) := rfl

theorem request_zero_cut {α : Type} (balance : Nat)
    (l : Locals E.layout Γ) (s : St E) (body : Nat → EM E Γ α) :
    (requestScope (constantRequestPlan (.runs balance (some 0))) body).run
      (l, { s with resource := Cursor.empty }) =
      (.error (.revert []), (l, { s with resource := requestFinished })) := rfl

theorem request_active_refused {α : Type} (points : Roadmap.Evm.FailurePoints)
    (l : Locals E.layout Γ) (s : St E) (body : Nat → EM E Γ α) :
    let active := Cursor.empty.enterFrame points
    (requestScope points body).run (l, { s with resource := active }) =
      (.error (.stuck "active request/frame at request entry"),
        (l, { s with resource := active })) := rfl

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
