import Solidity.Roadmap.V16.Relational
import Solidity.Roadmap.Controls
import Solidity.Source.SemanticsExamples

/-!
# Event-bearing controls of published source session executions

Reuse the published PS/PB example and sessionFrom execution semantics. The
chosen environment has no outside code and therefore is Allowed. No new Lang,
source semantics, admitted profile or compiler certificate is defined. The
published example's toy hash is not a pinned-Keccak/full-SourceSpec witness.
-/
namespace Solidity.Roadmap.V16.SessionControls
open Solidity.Source
open Solidity.Source.SemanticsExamples

/-- An actual allowed input to the existing session interpreter. -/
def environment : SessionEnv := { envS with hasCode := fun _ _ => false }

theorem allowed : environment.Allowed :=
  ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- Abbreviation of an existing execution, at its existing explicit address. -/
abbrev execution : Prefixes Nat Event Outcome := sessionFrom PS environment (addr 0)

theorem completes : (execution 30).final = some (.success (wordBytes (toWord 12))) := by
  decide +kernel

theorem event_count : (execution 30).events.length = 2 := by decide +kernel

theorem no_credit : Event.credit Address.zero 0 ∉ (execution 30).events := by decide +kernel

/-- Exact ordered completed prefixes survive NEW relational composition,
for an event-bearing actual execution in an allowed environment. -/
theorem composed_session_observation : ∃ n, True ∧ execution n = execution 30 :=
  composed_observation (refinement_refl (fun _ => True) execution)
    (refinement_refl (fun _ => True) execution) trivial completes

/-- Directly exercise NEW observation transport to reject event erasure. -/
theorem no_erasing_refinement (target : Prefixes Nat Event Outcome)
    (erased : ∀ n, (target n).events = []) :
    ¬ Refines (fun _ => True) (fun _ => True) execution target := by
  intro h
  obtain ⟨n, _, heq⟩ := composed_observation (refinement_refl (fun _ => True) execution)
    h trivial completes
  have hevents : (execution 30).events = [] := by rw [← heq, erased n]
  have hc := event_count
  rw [hevents] at hc
  cases hc

/-- A wrong event is also rejected, even when a target keeps events. -/
theorem no_wrong_event_refinement (target : Prefixes Nat Event Outcome)
    (wrong : ∀ n, Event.credit Address.zero 0 ∈ (target n).events) :
    ¬ Refines (fun _ => True) (fun _ => True) execution target := by
  intro h
  obtain ⟨n, _, heq⟩ := composed_observation (refinement_refl (fun _ => True) execution)
    h trivial completes
  have hx := wrong n
  rw [heq] at hx
  exact no_credit hx

/-- A property known to exclude an observed event cannot serve as the
source safety premise of NEW composed_safety. -/
theorem invalid_event_invariant :
    ¬ (∀ n, True → (execution n).events = []) := by
  intro hs
  have transported := composed_safety (refinement_refl (fun _ => True) execution)
    (refinement_refl (fun _ => True) execution) (fun p => p.events = [])
    (fun a b hab hb => by
      have hl : a.events.length ≤ b.events.length := hab.1.length_le
      rw [hb] at hl
      exact List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hl)) hs
  have he := transported 30 trivial
  have hc := event_count
  rw [he] at hc
  cases hc
end Solidity.Roadmap.V16.SessionControls
