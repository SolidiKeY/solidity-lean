import Solidity.Calculus.Logic
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Set.Lattice

/-!
# Predicate transformers of the actual modalities

Predicates live in Mathlib's complete lattice of sets. The transformer is
`Modality.afterRunTR`, so panic is rejected by both modalities and exhaustion
is accepted by both. Consequently box preserves nonempty intersections;
it preserves the empty intersection only when no run panics. Diamond/box
duality needs both panic and exhaustion excluded, even for terminating runs.
-/

namespace Solidity.Bridge

variable {α β : Type}

/-- The precondition computed by a typed run with the model's halt policy. -/
def wp (m : Modality) (run : α → TRes β) (q : Set β) : Set α :=
  {s | m.afterRunTR (· ∈ q) (run s)}

theorem wp_mono (m : Modality) (run : α → TRes β) : Monotone (wp m run) := by
  intro p q hpq s hs
  cases h : run s with
  | ok v =>
    simp only [wp, Set.mem_setOf_eq, Modality.afterRunTR, h] at hs ⊢
    exact ⟨hpq hs.1, hs.2⟩
  | error e =>
    simpa only [wp, Set.mem_setOf_eq, Modality.afterRunTR, h] using hs

/-- The modality is a Mathlib order homomorphism on predicates. -/
def wpOrderHom (m : Modality) (run : α → TRes β) : Set β →o Set α :=
  ⟨wp m run, wp_mono m run⟩

/-- Every sufficient precondition is contained in this one. -/
theorem wp_weakest (m : Modality) (run : α → TRes β) (p : Set α) (q : Set β) :
    p ⊆ wp m run q ↔ ∀ s ∈ p, m.afterRunTR (· ∈ q) (run s) := Iff.rfl

/-- The formula modality uses this transformer, including its frames. -/
theorem holds_modal {C : Contract} {Γ Γ₁ Γ₀ : Ctx} (m : Modality)
    (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (σ : State C Γ) :
    holds σ (.modal m P κ φ) ↔ σ ∈ wp m (fun s => Prog.runFrames s P κ) {s | holds s φ} :=
  Iff.rfl

theorem wp_iInter (m : Modality) (run : α → TRes β) {ι : Type} [Nonempty ι]
    (q : ι → Set β) : wp m run (⋂ i, q i) = ⋂ i, wp m run (q i) := by
  ext s
  cases h : run s with
  | ok v => simp only [wp, Set.mem_setOf_eq, Modality.afterRunTR, h,
      Set.mem_iInter, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  | error e =>
    simp only [wp, Set.mem_setOf_eq, Modality.afterRunTR, h, Set.mem_iInter]
    exact ⟨fun he _ => he, fun he => he (Classical.choice ‹Nonempty ι›)⟩

/-- Box of top is exactly panic freedom, rather than unconditionally top. -/
theorem wp_box_univ (run : α → TRes β) :
    wp .box run Set.univ = {s | run s ≠ .error .panic} := by
  ext s
  cases h : run s with
  | ok v => simp only [wp, Set.mem_setOf_eq, Modality.afterRunTR, h,
      Set.mem_univ, ne_eq, reduceCtorEq, not_false_eq_true, and_self]
  | error e => cases e <;> simp only [wp, Set.mem_setOf_eq, Modality.afterRunTR, h,
      Modality.onTHalt, ne_eq, not_true_eq_false, true_and]

theorem wp_dual (run : α → TRes β) (q : Set β)
    (hp : ∀ s, run s ≠ .error .panic) (he : ∀ s, run s ≠ .error .exhausted) :
    wp .diamond run q = (wp .box run qᶜ)ᶜ := by
  ext s
  cases h : run s with
  | ok v => simp only [wp, Set.mem_setOf_eq, Modality.afterRunTR, h,
      Set.mem_compl_iff, ne_eq, reduceCtorEq, not_false_eq_true, and_true, not_not]
  | error e =>
    cases e <;> simp_all only [wp, Set.mem_setOf_eq, Modality.afterRunTR,
      Set.mem_compl_iff, Modality.onTHalt, ne_eq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false, and_true]

end Solidity.Bridge
