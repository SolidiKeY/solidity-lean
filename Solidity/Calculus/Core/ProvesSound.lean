import Solidity.Calculus.Core.Proves
import Solidity.Calculus.Core.SoundKit

/-!
# The scoped sequent is sound

`H ⊢ φ` (`Calculus/Core/Proves.lean`) gives `H.wrap φ` in every state of the
outer scope (`Proves.sound`), and a goal with an empty context is valid
(`Proves.valid`), given that every rule the strategy fires is sound
(`Stmt.Sound`): the premise `p` of `s.step k m = some p`, in front of any
rest, frames and postcondition, with its cover under the diamond
(`Calculus/Core/Cover.lean`), gives the modality over `s` (`Premise.Sound`,
`Calculus/Core/SoundKit.lean`).  That hypothesis is the per-arm soundness,
stated per statement as `Stmt.StepSound` and collected by
`Stmt.Sound.of_stepSound`, from the arms' `Stmt.stepSound`
(`Calculus/Core/SoundStep.lean`, given the block arms and `WkRuns`).  This
module is the structural part, which does not depend on any arm.

The hypothesis holds in untyped states too: a branch on a condition that is
stuck (a `bool` local holding no `bool`, which a formula's binders allow)
satisfies the box, and under the diamond the cover goal (`Proves.split`'s,
`Proves.inv`'s) rules it out.

A rule's goals are the conjuncts of its premise's formula, each under the
context: the context is monotone and keeps a conjunction
(`Hyps.wrap_and`), as every entry is an implication, an update or a
universal.  A rule with no goal would not be sound behind a diamond update
that halts, so `branches` and `cases` have at least one goal, and
`closeTrue` asks the context to have no diamond update but scope ends
(`Hyps.wrap_valid`).
-/

namespace Solidity.Core

open Solidity (Modality RuleSet)

variable {C : Contract}

/-! ## The per-arm interface -/

/-- **Every rule the strategy fires is sound** in every state, at any fresh
index (a rule's fresh locals are positions, so soundness needs no freshness
premise), given its cover: what `Proves.sound` asks of the arms. -/
def Stmt.Sound (C : Contract) : Prop :=
  ∀ (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ'),
    s.step k m = some p → ∀ σ : State C Γ, Premise.Sound m s p σ

/-- The arms' interface (`Calculus/Core/SoundKit.lean`) gives it. -/
theorem Stmt.Sound.of_stepSound
    (hS : ∀ (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ'), Stmt.StepSound k m s) :
    Stmt.Sound C :=
  fun k m _ _ s p hp σ => hS k m s σ p hp

/-! ## Outcomes -/

theorem _root_.Solidity.Modality.afterC_and {α : Type} {m : Modality} {p q r : α → Prop} {x : Semantics.Res α}
    (hp : m.afterC p x) (hq : m.afterC q x) (h : ∀ a, p a → q a → r a) : m.afterC r x := by
  cases x with
  | ok a => exact h a hp hq
  | error _ => exact hp

/-- A pop or a drop never halts. -/
theorem Upd.apply_popsOnly {Γ : Ctx} (σ : State C Γ) {Δ : Ctx} (U : Upd C Γ Δ)
    (h : U.popsOnly = true) : ∃ τ, U.apply σ = .ok τ := by
  induction U with
  | nil => exact ⟨σ, rfl⟩
  | snoc _ _ => exact absurd h Bool.false_ne_true
  | decl _ _ _ => exact absurd h Bool.false_ne_true
  | pop U e ih =>
    obtain ⟨τ, hτ⟩ := ih h
    exact ⟨τ.drop e, by rw [Upd.apply, hτ]; rfl⟩
  | drop U e ih =>
    obtain ⟨τ, hτ⟩ := ih h
    exact ⟨τ.thin e, by rw [Upd.apply, hτ]; rfl⟩

/-! ## The context -/

section Wrap

variable {Γ₀ : Ctx}

/-- Two formulas under the context give a third that follows from both. -/
theorem Hyps.wrap_and {Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    ∀ {φ ψ χ : Fml C Γ}, (∀ τ, holds τ φ → holds τ ψ → holds τ χ) →
      ∀ σ, holds σ (H.wrap φ) → holds σ (H.wrap ψ) → holds σ (H.wrap χ) := by
  induction H with
  | nil => intro φ ψ χ h σ; exact h σ
  | pre H a ih =>
    intro φ ψ χ h
    exact ih (φ := .imp a φ) (ψ := .imp a ψ) (χ := .imp a χ) fun τ f g ha => h τ (f ha) (g ha)
  | upd H m U ih =>
    intro φ ψ χ h
    exact ih (φ := .upd m U φ) (ψ := .upd m U ψ) (χ := .upd m U χ) fun τ f g =>
      Modality.afterC_and f g h
  | havoc H ih =>
    intro φ ψ χ h
    exact ih (φ := .havoc φ) (ψ := .havoc ψ) (χ := .havoc χ) fun τ f g st nt =>
      h _ (f st nt) (g st nt)
  | all H x p ih =>
    intro φ ψ χ h
    exact ih (φ := .all x p φ) (ψ := .all x p ψ) (χ := .all x p χ) fun τ f g v hv =>
      h _ (f v hv) (g v hv)
  | bind H x t ih =>
    intro φ ψ χ h
    exact ih (φ := .bind x t φ) (ψ := .bind x t ψ) (χ := .bind x t χ) fun τ f g v => h _ (f v) (g v)
  | anon H xs ih =>
    intro φ ψ χ h
    exact ih (φ := .anon xs φ) (ψ := .anon xs ψ) (χ := .anon xs χ) fun τ f g b => h _ (f b) (g b)

/-- The context is monotone. -/
theorem Hyps.wrap_mono {Γ : Ctx} (H : Hyps C Γ₀ Γ) {φ ψ : Fml C Γ}
    (h : ∀ τ, holds τ φ → holds τ ψ) (σ : State C Γ₀) (hφ : holds σ (H.wrap φ)) :
    holds σ (H.wrap ψ) :=
  H.wrap_and (fun τ a _ => h τ a) σ hφ hφ

/-- A conjunction of at least one formula, each under the context. -/
theorem Hyps.wrap_conj {Γ : Ctx} (H : Hyps C Γ₀ Γ) (σ : State C Γ₀) :
    ∀ (ψs : List (Fml C Γ)), ψs ≠ [] → (∀ ψ ∈ ψs, holds σ (H.wrap ψ)) →
      holds σ (H.wrap (Fml.conj ψs))
  | [], hne, _ => absurd rfl hne
  | [φ], _, h => h φ (List.mem_singleton_self φ)
  | φ :: ψ :: ψs, _, h =>
    H.wrap_and (φ := φ) (ψ := Fml.conj (ψ :: ψs)) (χ := .and φ (Fml.conj (ψ :: ψs)))
      (fun _ a b => ⟨a, b⟩) σ (h φ List.mem_cons_self)
      (H.wrap_conj σ (ψ :: ψs) (List.cons_ne_nil _ _) fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))

/-- A valid formula behind a context with no diamond update but scope ends
holds. -/
theorem Hyps.wrap_valid {Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    ∀ {φ : Fml C Γ}, H.boxOnly = true → (∀ τ, holds τ φ) → ∀ σ, holds σ (H.wrap φ) := by
  induction H with
  | nil => intro φ _ h σ; exact h σ
  | pre H a ih => intro φ hb h; exact ih (φ := .imp a φ) hb fun τ _ => h τ
  | upd H m U ih =>
    intro φ hb h
    cases m with
    | box =>
      refine ih (φ := .upd .box U φ) hb fun τ => ?_
      show Modality.afterC .box _ _
      cases U.apply τ with
      | ok a => exact h a
      | error _ => trivial
    | diamond =>
      have hb' : U.popsOnly = true ∧ H.boxOnly = true := Bool.and_eq_true_iff.mp hb
      refine ih (φ := .upd .diamond U φ) hb'.2 fun τ => ?_
      obtain ⟨a, ha⟩ := Upd.apply_popsOnly τ U hb'.1
      show Modality.afterC .diamond _ _
      rw [ha]
      exact h a
  | havoc H ih => intro φ hb h; exact ih (φ := .havoc φ) hb fun τ _ _ => h _
  | all H x p ih => intro φ hb h; exact ih (φ := .all x p φ) hb fun τ _ _ => h _
  | bind H x t ih => intro φ hb h; exact ih (φ := .bind x t φ) hb fun τ _ => h _
  | anon H xs ih => intro φ hb h; exact ih (φ := .anon xs φ) hb fun τ _ => h _

theorem Hyps.wrap_anonHavoc {Γ : Ctx} (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t))
    (hv : Bool) (φ : Fml C Γ) : (H.anonHavoc xs hv).wrap φ = H.wrap (Fml.anonHavoc xs hv φ) := by
  cases hv <;> rfl

end Wrap

/-! ## Soundness -/

/-- **Soundness of the scoped sequent**: what `H ⊢ φ` proves holds, its
context in front, in every state of the outer scope, given that every rule
the strategy fires is sound. -/
theorem Proves.sound (hS : Stmt.Sound C) {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ}
    {φ : Fml C Γ} (d : Proves C R Γ₀ H φ) : ∀ σ, holds σ (H.wrap φ) := by
  induction d with
  | intro _ ih => exact ih
  | allIntro _ ih => exact ih
  | updIntro _ ih => exact ih
  | bindIntro _ ih => exact ih
  | @update Γ Γ' Γ₁ Γ₂ H m s ω κ φ U d _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.update U).fml m ω κ φ) (fun τ h => hS _ _ s _ d τ ω κ φ h (by cases m <;> trivial)) σ (ih σ)
  | @unfold Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.unfold P e).fml m ω κ φ) (fun τ h => hS _ _ s _ d τ ω κ φ h (by cases m <;> trivial)) σ (ih σ)
  | @bind Γ Γ' Γ₁ Γ₂ H m s ω κ φ x t P d _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.bind x t P).fml m ω κ φ) (fun τ h => hS _ _ s _ d τ ω κ φ h (by cases m <;> trivial)) σ (ih σ)
  | @split Γ Γ₁ Γ₂ Δ₁ Δ₂ H m s ω κ φ b c c' P Q d _ _ _ ihT ihE ihC =>
    intro σ
    have hTE : holds σ (H.wrap ((Premise.split b c c' P Q).fml m ω κ φ)) :=
      H.wrap_and (χ := (Premise.split b c c' P Q).fml m ω κ φ) (fun _ x y => ⟨x, y⟩) σ
        (ihT σ) (ihE σ)
    cases m with
    | box => exact H.wrap_mono (fun τ h => hS _ _ s _ d τ ω κ φ h trivial) σ hTE
    | diamond => exact H.wrap_and (fun τ h hc => hS _ _ s _ d τ ω κ φ h hc) σ hTE (ihC rfl σ)
  | @check Γ Γ₁ Γ₂ H m s ω κ φ c d _ _ ihT ihE =>
    exact fun σ => H.wrap_and
      (fun τ a b => hS _ _ s _ d τ ω κ φ (show holds τ ((Premise.check c).fml m ω κ φ)
        from ⟨a, b⟩) (by cases m <;> trivial)) σ (ihT σ) (ihE σ)
  | @done Γ Γ' Γ₁ Γ₂ H m s ω κ φ b d _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.done b).fml m ω κ φ) (fun τ h => hS _ _ s _ d τ ω κ φ h (by cases m <;> trivial)) σ (ih σ)
  | @branches Γ Γ₁ Γ₂ H m s ω κ φ bs d hne _ ih =>
    intro σ
    refine H.wrap_mono (φ := (Premise.branches bs).fml m ω κ φ) (fun τ h => hS _ _ s _ d τ ω κ φ h (by cases m <;> trivial)) σ ?_
    refine H.wrap_conj σ _ ?_ ?_
    · cases bs with
      | nil => exact nomatch hne
      | cons _ _ => exact List.cons_ne_nil _ _
    · intro ψ hψ
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ
      exact ih b hb σ
  | @cases Γ Γ₁ Γ₂ H m s ω κ φ fs us d hne _ _ ihF ihU =>
    intro σ
    refine H.wrap_mono (φ := (Premise.cases fs us).fml m ω κ φ) (fun τ h => hS _ _ s _ d τ ω κ φ h (by cases m <;> trivial)) σ ?_
    refine H.wrap_conj σ _ ?_ ?_
    · cases fs with
      | cons _ _ => exact List.cons_ne_nil _ _
      | nil =>
        cases us with
        | nil => exact nomatch hne
        | cons _ _ => exact List.cons_ne_nil _ _
    · intro ψ hψ
      rcases List.mem_append.mp hψ with hf | hu
      · exact ihF ψ hf σ
      · obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hu
        exact ihU U hU σ
  | @inv Γ Γ₁ Γ₂ Δ₀ Δ Γ₃ H m s ω κ φ I xs hv U c c' hu hb P post d _ _ _ _ ihI ihT ihE ihC =>
    intro σ
    let A : Fml C Δ := .upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil) post)
    let B : Fml C Δ := .upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)
    let X : Fml C Γ := .imp I (.upd m U (.and (.imp c A) (.imp c' B)))
    have hX : holds σ ((H.anonHavoc xs hv).wrap X) :=
      (H.anonHavoc xs hv).wrap_and (φ := .imp I (.upd m U (.imp c A)))
        (ψ := .imp I (.upd m U (.imp c' B))) (χ := X)
        (fun τ x y hI => Modality.afterC_and (x hI) (y hI) fun _ f g => ⟨f, g⟩) σ (ihT σ) (ihE σ)
    rw [Hyps.wrap_anonHavoc] at hX
    have hF : holds σ (H.wrap ((Premise.inv I xs hv U c c' hu hb P post).fml m ω κ φ)) :=
      H.wrap_and (φ := I) (ψ := Fml.anonHavoc xs hv X) (χ := .and I (Fml.anonHavoc xs hv X))
        (fun _ x y => ⟨x, y⟩) σ (ihI σ) hX
    cases m with
    | box => exact H.wrap_mono (fun τ h => hS _ _ s _ d τ ω κ φ h trivial) σ hF
    | diamond =>
      have hC : holds σ (H.wrap (Fml.anonHavoc xs hv (.imp I (.upd .diamond U (.or c c'))))) := by
        rw [← Hyps.wrap_anonHavoc]; exact ihC rfl σ
      exact H.wrap_and (fun τ h hc => hS _ _ s _ d τ ω κ φ h hc) σ hF hC
  | @inline Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.inline P e).fml m ω κ φ) (fun τ h => hS _ _ s _ d τ ω κ φ h (by cases m <;> trivial)) σ (ih σ)
  | @empty Γ Γ₂ H m κ φ _ ih =>
    exact fun σ => H.wrap_mono (φ := κ.exit m φ) (ψ := .modal m .nil κ φ)
      (fun τ h => (holds_exit m κ φ τ).1 h) σ (ih σ)
  | @closeTrue Γ H h => exact H.wrap_valid (φ := .tt) h fun _ => trivial

/-- **A goal proved with an empty context is valid.** -/
theorem Proves.valid (hS : Stmt.Sound C) {R : RuleSet} {φ : Fml C []}
    (d : Proves C R [] .nil φ) : Valid φ :=
  Proves.sound hS d

/-- `∀ bool b; [ if (b) { } else { } ] true` is valid, by `allRight`,
`ifElseSplit` and in each goal the block's end and `closeTrue`, given the
rules sound. -/
example (hS : Stmt.Sound StandardExample) :
    Valid (C := StandardExample) (.all (.user "b") .bool
      (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt)) :=
  Proves.valid (R := .all) hS
    (.allIntro (.split rfl (.updIntro (.closeTrue rfl)) (.updIntro (.closeTrue rfl)) nofun))

end Solidity.Core
