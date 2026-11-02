import Solidity.Roadmap.Evm

/-!
# Source failure resources (S05 checkpoint 5, resource interface only)

The source session currently uses a bare horizon. This module gives its future
resource parameter the existing G06 request/frame failure choices, with an
order that extends only the horizon at fixed choices. It does not change
`sourceLangEvents` or claim that the evaluator consults these choices yet.
-/
namespace Solidity.Source.FailureResources
open Solidity.Roadmap.Evm

/-- An independent choice for each request and each external frame, plus the
interpreter horizon. Different choices are different executions, not longer
prefixes of one execution. -/
abbrev Bound := Nat × FailurePoints

def Bound.horizon (r : Bound) : Nat := r.1
def Bound.points (r : Bound) : FailurePoints := r.2

instance : LE Bound := ⟨fun a b => a.points = b.points ∧ a.horizon ≤ b.horizon⟩

theorem Bound.le_refl (a : Bound) : a ≤ a := ⟨rfl, Nat.le_refl _⟩
theorem Bound.le_trans {a b c : Bound} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  ⟨hab.1.trans hbc.1, Nat.le_trans hab.2 hbc.2⟩

/-- Replace the failure choices without changing the horizon. -/
def Bound.withFailures (r : Bound) (p : FailurePoints) : Bound := (r.1, p)

theorem Bound.failures_with (r : Bound) (p : FailurePoints) :
    (r.withFailures p).points = p := rfl

theorem Bound.horizon_with (r : Bound) (p : FailurePoints) :
    (r.withFailures p).horizon = r.horizon := rfl

/-- Replacement of the choices keeps a horizon extension a horizon extension. -/
theorem Bound.withFailures_mono {r s : Bound} (h : r ≤ s) (p : FailurePoints) :
    r.withFailures p ≤ s.withFailures p := ⟨rfl, h.2⟩

/-- No invalid/dropped request, no request gas failure, and no scheduled external-frame
resource failure. Fixed depth-limit failures are not removed. The sender balance remains explicit; this does not assert
that the request's value is affordable. -/
def NoFail (p : FailurePoints) : Prop :=
  (∀ i, ∃ balance, p.tx i = .runs balance none) ∧ ∀ k, p.frame k = none

/-- Failure-free choices still retain arbitrary post-fee sender balances. -/
def noFailures (balances : Nat → Nat) : FailurePoints where
  tx i := .runs (balances i) none
  frame _ := none

theorem noFailures_noFail (balances : Nat → Nat) : NoFail (noFailures balances) :=
  ⟨fun i => ⟨balances i, rfl⟩, fun _ => rfl⟩

/-- All failure-free choices have exactly this form; this is not a finite
sampling of requests or frames. -/
theorem noFail_iff (p : FailurePoints) :
    NoFail p ↔ ∃ balances, p = noFailures balances := by
  classical
  constructor
  · intro h
    let balances := fun i => Classical.choose (h.1 i)
    refine ⟨balances, ?_⟩
    have ht : p.tx = (noFailures balances).tx :=
      funext fun i => Classical.choose_spec (h.1 i)
    have hf : p.frame = (noFailures balances).frame := funext h.2
    cases p with
    | mk tx frame =>
      simp only [noFailures, FailurePoints.mk.injEq] at ht hf ⊢
      exact ⟨ht, hf⟩
  · rintro ⟨balances, rfl⟩
    exact noFailures_noFail balances

/-- A dropped request is a real failure choice, even if every frame is clear. -/
theorem dropped_not_noFail {p : FailurePoints} {i : Nat} (h : p.tx i = .dropped) :
    ¬ NoFail p := by
  intro hn
  obtain ⟨balance, hb⟩ := hn.1 i
  rw [h] at hb
  cases hb

/-- A frame failure at any index is incompatible with the no-failure bound. -/
theorem frame_not_noFail {p : FailurePoints} {k cut : Nat} (h : p.frame k = some cut) :
    ¬ NoFail p := by
  intro hn
  have hf := hn.2 k
  rw [h] at hf
  cases hf

/-- A different failure schedule cannot be substituted as a longer prefix. -/
theorem Bound.not_le_of_points_ne {r s : Bound} (h : r.points ≠ s.points) : ¬ r ≤ s :=
  fun hrs => h hrs.1

/-- The current bare `Nat` horizon cannot encode G06's independent frame
choices with the retraction demanded by `SourceSpec.failures_with`. The
explicit diagonal uses only frame choices, so no cardinality axiom is needed.
A failure-aware source must extend its resource, not ignore the schedule. -/
theorem no_horizon_retraction (extract : Nat → FailurePoints)
    (replace : Nat → FailurePoints → Nat)
    (rightInverse : ∀ n p, extract (replace n p) = p) : False := by
  let diagonal : FailurePoints := {
    tx := fun _ => .dropped
    frame := fun n => match (extract n).frame n with
      | none => some 0
      | some _ => none }
  let j := replace 0 diagonal
  have h := congrArg (fun p : FailurePoints => p.frame j) (rightInverse 0 diagonal)
  change (extract j).frame j = (match (extract j).frame j with
    | none => some 0
    | some _ => none) at h
  cases he : (extract j).frame j with
  | none => rw [he] at h; cases h
  | some cut => rw [he] at h; cases h

end Solidity.Source.FailureResources
