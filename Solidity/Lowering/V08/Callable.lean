import Solidity.Semantics.ContractWorld

/-!
# Result observations of actual typed callable frames

These adapters preserve the supplied typed body and its paid frame. They do
not resolve source declarations, certify source execution, or replace a decoder.
The observation function runs only after the original result decoder succeeds.
-/
namespace Solidity.Lowering.V08
open Solidity.ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- Extend a callable result observation without changing its typed frame. -/
def observeEntry {C : Contract} {α β : Type} (entry : Entry C α) (observe : α → β) : Entry C β :=
  { locals := entry.locals, body := entry.body, payable := entry.payable,
    result := fun state => (entry.result state).map observe }

/-- Observation extension executes precisely the original body and settlement. -/
theorem callFrame_observeEntry {α β : Type} (w : World contracts) {k : K}
    (self : Handle k) (entry : Entry (contracts k) α) (ctx : Context) (observe : α → β) :
    w.callFrame self (observeEntry entry observe) ctx = w.callFrame self entry ctx := rfl

/-- Return observation extension keeps the world and every exact halt. -/
theorem call_observeEntry {α β : Type} (w : World contracts) {k : K}
    (self : Handle k) (entry : Entry (contracts k) α) (ctx : Context) (observe : α → β) :
    w.call self (observeEntry entry observe) ctx =
      (w.call self entry ctx).map (fun pair => (pair.1, observe pair.2)) := by
  unfold World.call
  rw [callFrame_observeEntry]
  cases hf : w.callFrame self entry ctx with
  | error halt => rfl
  | ok pair =>
    obtain ⟨next, state⟩ := pair
    simp only [bind, Except.bind]
    change (do let value ← (entry.result state).map observe; pure (next, value)) = _
    cases hr : entry.result state <;> rfl

/-- A failed result decoder cannot be hidden by extending observations. -/
theorem call_observeEntry_error_iff {α β : Type} (w : World contracts) {k : K}
    (self : Handle k) (entry : Entry (contracts k) α) (ctx : Context)
    (observe : α → β) (halt : THalt) :
    w.call self (observeEntry entry observe) ctx = .error halt ↔
      w.call self entry ctx = .error halt := by
  rw [call_observeEntry]
  cases w.call self entry ctx with
  | error error => simp only [Except.map, Except.error.injEq]
  | ok pair => constructor <;> intro impossible <;> cases impossible

/-- Repeated extensions compose without rerunning the callable. -/
theorem call_observeEntry_comp {α β γ : Type} (w : World contracts) {k : K}
    (self : Handle k) (entry : Entry (contracts k) α) (ctx : Context)
    (first : α → β) (second : β → γ) :
    w.call self (observeEntry (observeEntry entry first) second) ctx =
      w.call self (observeEntry entry (fun value => second (first value))) ctx := by
  rw [call_observeEntry, call_observeEntry, call_observeEntry]
  cases w.call self entry ctx <;> rfl

end Solidity.Lowering.V08
