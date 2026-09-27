import Solidity.Calculus.Symex
import Solidity.Calculus.Notation

/-!
# Progress: symbolic execution never gets stuck

`Stmt.step` (`Completeness.lean`) is total, so a statement at the front of a
modality always has a rule; this module lifts that to formulas (the second
half of mini-solkey's `Ch11_Completeness`).  A modality can sit under an
update, right of an implication, or in either conjunct of a branch's goals,
and `Fml.stepAt` looks through all three, so the strategy of `Symex.lean`
stops **exactly** when no modality is left: `Fml.active_iff_step`.

That it does stop is `Termination.lean`.
-/

namespace Solidity

variable {C : Contract}

/-- A formula that takes a step has a modality left.

Example: `dl!{ [ x = 1; ] x == 1 }` steps by `localValueAssign`;
`dl!{ { x := 1 } x = 1 }` has no modality, and nothing steps it. -/
theorem Fml.stepAt_active {k : Nat} :
    ∀ {φ ψ : Fml C}, φ.stepAt k = some ψ → φ.active = true
  | .upd _ _ φ, _, h | .imp _ φ, _, h | .havoc φ, _, h => by
    simp only [Fml.stepAt, Option.map_eq_some_iff] at h
    obtain ⟨_, h, -⟩ := h
    simpa [Fml.active] using Fml.stepAt_active h
  | .and φ₁ φ₂, _, h => by
    simp only [Fml.stepAt] at h
    split at h <;> simp only [Option.map_eq_some_iff] at h <;> obtain ⟨_, h, -⟩ := h
    · simp [Fml.active, *]
    · simp [Fml.active, Fml.stepAt_active h]
  | .modal .., _, _ => rfl
  | .tt, _, h | .eq .., _, h | .not _, _, h => by simp [Fml.stepAt] at h

/-- A formula with a modality left steps, wherever the modality sits: under
an update, right of an implication, or in either conjunct.

Example: `dl!{ a != b → [ total = 1; ] total == 1 }` steps by
`storageRootWriteStore`, inside the implication. -/
theorem Fml.stepAt_of_active (k : Nat) :
    ∀ {φ : Fml C}, φ.active = true → ∃ ψ, φ.stepAt k = some ψ
  | .upd m U φ, h => by
    obtain ⟨ψ, hs⟩ := Fml.stepAt_of_active k (φ := φ) (by simpa [Fml.active] using h)
    exact ⟨.upd m U ψ, by simp [Fml.stepAt, hs]⟩
  | .imp a φ, h => by
    obtain ⟨ψ, hs⟩ := Fml.stepAt_of_active k (φ := φ) (by simpa [Fml.active] using h)
    exact ⟨.imp a ψ, by simp [Fml.stepAt, hs]⟩
  | .havoc φ, h => by
    obtain ⟨ψ, hs⟩ := Fml.stepAt_of_active k (φ := φ) (by simpa [Fml.active] using h)
    exact ⟨.havoc ψ, by simp [Fml.stepAt, hs]⟩
  | .and φ₁ φ₂, h => by
    by_cases h₁ : φ₁.active = true
    · obtain ⟨ψ, hs⟩ := Fml.stepAt_of_active k h₁
      exact ⟨.and ψ φ₂, by simp [Fml.stepAt, h₁, hs]⟩
    · have h₂ : φ₂.active = true := by simp_all [Fml.active]
      obtain ⟨ψ, hs⟩ := Fml.stepAt_of_active k h₂
      exact ⟨.and φ₁ ψ, by simp [Fml.stepAt, h₁, hs]⟩
  | .modal _ [] φ, _ => ⟨φ, rfl⟩
  | .modal _ (_ :: _) _, _ => ⟨_, rfl⟩
  | .tt, h | .eq .., h | .not _, h => by simp [Fml.active] at h

/-- **Progress.**  A formula with a modality left takes a step, and only such
a formula does: the strategy stops exactly when the formula is first order.

Example: `dl!{ [ x = 1; ] x == 1 }` is active and steps (to
`{ x := 1 } [ ] x = 1`); `dl!{ { x := 1 } x = 1 }` is not, and does not. -/
theorem Fml.active_iff_step (φ : Fml C) : φ.active = true ↔ ∃ ψ, φ.step = some ψ :=
  ⟨Fml.stepAt_of_active _, fun ⟨_, h⟩ => Fml.stepAt_active h⟩

/-- A formula the strategy cannot step has no modality left: it is first
order.

Example: symbolic execution of `total = 1;` stops at
`{ storage := store(storage, total, 1) } select(storage, total) = 1`, which
has no modality. -/
theorem Fml.step_eq_none {φ : Fml C} (h : φ.step = none) : φ.active = false := by
  cases ha : φ.active
  · rfl
  · obtain ⟨_, h'⟩ := (Fml.active_iff_step φ).1 ha
    simp [h] at h'

/-! ## Try it -/

section Examples

local instance : InContract := ⟨StandardExample⟩

-- a statement under a modality: the strategy has a step
example : ∃ ψ, (dl!{ [ x = 1; ] x == 1 }).step = some ψ := (Fml.active_iff_step _).1 rfl

-- a first-order formula: none
#guard (dl!{ x == 1 }).step.isNone

end Examples

end Solidity
