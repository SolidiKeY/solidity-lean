import Solidity.Semantics.Lifetime

/-!
# Induction over the published intrinsic lifetime semantics

No new execution relation is introduced. These theorems lift an explicit
step/deployment relation over Lifetime.Step/Trace/Reachable. They do not supply
backend/runtime simulation premises or treat exhaustion as a completed call.
-/
namespace Solidity.Roadmap.V16
open Solidity.Lifetime

section
variable {C₁ C₂ : Contract} {D₁ D₂ A₁ A₂ : Type}
    {M₁ : System C₁ D₁ A₁} {M₂ : System C₂ D₂ A₂}

/-- Lift an event-preserving step relation to actual finite traces.
The same event map applies at every step, retaining list order and length. -/
theorem trace_transport (R : World C₁ → World C₂ → Prop)
    (event : Lifetime.Event A₁ → Lifetime.Event A₂)
    (step : ∀ {s t u a}, R s u → Lifetime.Step M₁ s a t →
      ∃ v, Lifetime.Step M₂ u (event a) v ∧ R t v)
    {s t : World C₁} {as : List (Lifetime.Event A₁)}
    (path : Lifetime.Trace M₁ s as t) {u : World C₂} (hu : R s u) :
    ∃ v, Lifetime.Trace M₂ u (as.map event) v ∧ R t v := by
  induction path generalizing u with
  | nil s => exact ⟨u, .nil u, hu⟩
  | cons next rest ih =>
    obtain ⟨v, hv, hrel⟩ := step hu next
    obtain ⟨w, hw, hlast⟩ := ih hrel
    exact ⟨w, .cons hv hw, hlast⟩

/-- Constructor-rooted reachable states transport only with actual target
initialization and step evidence; neither premise is manufactured here. -/
theorem reachable_transport (R : World C₁ → World C₂ → Prop)
    (event : Lifetime.Event A₁ → Lifetime.Event A₂)
    (initial : ∀ s, M₁.Init s → ∃ u, M₂.Init u ∧ R s u)
    (step : ∀ {s t u a}, R s u → Lifetime.Step M₁ s a t →
      ∃ v, Lifetime.Step M₂ u (event a) v ∧ R t v)
    {s : World C₁} (hs : Lifetime.Reachable M₁ s) :
    ∃ u, Lifetime.Reachable M₂ u ∧ R s u := by
  induction hs with
  | init deployed =>
    obtain ⟨u, hu, hr⟩ := initial _ deployed
    exact ⟨u, .init hu, hr⟩
  | step before next ih =>
    obtain ⟨u, hu, hr⟩ := ih
    obtain ⟨v, hv, hrel⟩ := step hr next
    exact ⟨v, .step hu hv, hrel⟩

/-- Pull a source invariant to every target reachable state. The backward
initial/step direction is explicit; forward simulation alone is insufficient
for target safety against additional target interactions. -/
theorem reachable_invariant (R : World C₁ → World C₂ → Prop)
    (event : Lifetime.Event A₂ → Lifetime.Event A₁)
    (initial : ∀ t, M₂.Init t → ∃ s, M₁.Init s ∧ R s t)
    (step : ∀ {s t u a}, R s t → Lifetime.Step M₂ t a u →
      ∃ v, Lifetime.Step M₁ s (event a) v ∧ R v u)
    (P : World C₁ → Prop) (Q : World C₂ → Prop)
    (source : Lifetime.Invariant M₁ P) (reflect : ∀ s t, R s t → P s → Q t) :
    Lifetime.AG M₂ Q := by
  intro t ht
  obtain ⟨s, hs, hr⟩ := reachable_transport (fun t s => R s t) event initial
    (fun h next => step h next) ht
  exact reflect s t hr (source.always s hs)

/-- An inductive invariant holds at both ends of every actual continuation,
without a new reachability assumption for its initial state. -/
theorem trace_invariant {C : Contract} {D A : Type} {M : System C D A}
    {P : World C → Prop} (inv : Lifetime.Invariant M P)
    {s t : World C} {as : List (Lifetime.Event A)}
    (path : Lifetime.Trace M s as t) (hs : P s) : P t := by
  induction path with
  | nil _ => exact hs
  | cons next rest ih => exact ih (inv.preserved hs next)
end
end Solidity.Roadmap.V16
