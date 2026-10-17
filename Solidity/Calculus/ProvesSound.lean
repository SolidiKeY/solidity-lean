import Solidity.Calculus.Proves
import Solidity.Calculus.PremiseSound

/-!
# The scoped sequent is sound: the structure

What `H ⊢ φ` proves holds, its context in front, in every typed state of the
outer scope (`Proves.sound_of`, `holds`, `Calculus/Logic.lean`), given
that every rule the strategy fires is sound there (`Stmt.Sound`, the arms'
part, `Premise.Sound` per premise, proved in `Calculus/Sound.lean`:
`Stmt.sound`, `Proves.sound`, `Proves.valid`).  This module is the
structural part, which does not depend on any arm: the context is monotone
and keeps a conjunction (`Hyps.wrap_and`), as every entry is an
implication, an update or a universal; `closeTrue` holds behind a context
with no diamond update but scope ends (`Hyps.wrap_valid`; a rule with no
goal would not be sound behind a diamond update that halts, so `branches`
and `cases` have at least one goal); `emptyModality` goes into the frames
(`holds_exit`).

An update's reading asks of every typed state it lands on, so a rule's
premise gives its conclusion in the state the typed run ends in, one of
them: only that direction is needed here.
-/

namespace Solidity
open Solidity (Modality RuleSet)

variable {C : Contract}

/-- A pop or a drop never halts. -/
theorem Upd.popsOnly_globT {Γ : Ctx} (σ : State C Γ) {Δ : Ctx} (U : Upd C Γ Δ)
    (h : U.popsOnly = true) : U.globT σ = some σ.globG := by
  induction U with
  | nil => rfl
  | snoc _ _ => exact absurd h Bool.false_ne_true
  | decl _ _ _ => exact absurd h Bool.false_ne_true
  | pop U e ih => exact ih h
  | drop U e ih => exact ih h

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
      Upd.afterT_and f g fun σ' x y => h σ' x y
  | havoc H ih =>
    intro φ ψ χ h
    exact ih (φ := .havoc φ) (ψ := .havoc ψ) (χ := .havoc χ) fun τ f g st nt =>
      h _ (f st nt) (g st nt)
  | all H x p ih =>
    intro φ ψ χ h
    exact ih (φ := .all x p φ) (ψ := .all x p ψ) (χ := .all x p χ) fun τ f g v => h _ (f v) (g v)
  | bind H m x t ih =>
    intro φ ψ χ h
    exact ih (φ := .bind m x t φ) (ψ := .bind m x t ψ) (χ := .bind m x t χ) fun τ f g =>
      Modality.forallB_and (fun _ a b => h _ a b) f g
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
      exact ih (φ := .upd .box U φ) hb fun τ =>
        Upd.afterT_intro (fun _ => trivial) fun _ σ' _ => h σ'
    | diamond =>
      have hb' : U.popsOnly = true ∧ H.boxOnly = true := Bool.and_eq_true_iff.mp hb
      refine ih (φ := .upd .diamond U φ) hb'.2 fun τ => ?_
      refine Upd.afterT_intro (fun he => ?_) fun _ σ' _ => h σ'
      rw [Upd.popsOnly_globT τ U hb'.1] at he
      cases he
  | havoc H ih => intro φ hb h; exact ih (φ := .havoc φ) hb fun τ _ _ => h _
  | all H x p ih => intro φ hb h; exact ih (φ := .all x p φ) hb fun τ _ => h _
  | bind H m x t ih =>
    intro φ hb h
    exact ih (φ := .bind m x t φ) hb fun τ v => h _
  | anon H xs ih => intro φ hb h; exact ih (φ := .anon xs φ) hb fun τ _ => h _

theorem Hyps.wrap_binds {Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    (bs : List (Modality × Var × LTy)) → (φ : Fml C (Binds.ctx bs Γ)) →
      (H.binds bs).wrap φ = H.wrap (Fml.binds bs φ)
  | [], _ => rfl
  | (_, _, _) :: bs, φ => Hyps.wrap_binds _ bs φ

/-- Hidden binders are monotone. -/
theorem Fml.binds_mono : {Γ : Ctx} → (bs : List (Modality × Var × LTy)) →
    {φ ψ : Fml C (Binds.ctx bs Γ)} → (∀ τ, holds τ φ → holds τ ψ) →
      ∀ σ : State C Γ, holds σ (Fml.binds bs φ) → holds σ (Fml.binds bs ψ)
  | _, [], _, _, h, σ, hσ => h σ hσ
  | _, (_, _, _) :: bs, _, _, h, _, hσ =>
    Modality.forallB_imp (fun _ hv => Fml.binds_mono bs h _ hv) hσ

theorem Hyps.wrap_anonHavoc {Γ : Ctx} (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t))
    (hv : Bool) (φ : Fml C Γ) : (H.anonHavoc xs hv).wrap φ = H.wrap (Fml.anonHavoc xs hv φ) := by
  cases hv <;> rfl

end Wrap

/-- Rewriting the context and the goal is rewriting the sequent. -/
theorem Hyps.wrap_rwEqC {p : PrimTy} (q : Tm C [] (.val p) × Tm C [] (.val p)) {Γ₀ : Ctx} :
    {Γ : Ctx} → (H : Hyps C Γ₀ Γ) → (φ : Fml C Γ) →
      (H.rwEqC q).wrap (φ.rwEqC q) = (H.wrap φ).rwEqC q
  | _, .nil, _ => rfl
  | _, .pre H a, φ => Hyps.wrap_rwEqC q H (.imp a φ)
  | _, .upd H m U, φ => Hyps.wrap_rwEqC q H (.upd m U φ)
  | _, .havoc H, φ => Hyps.wrap_rwEqC q H (.havoc φ)
  | _, .all H x p, φ => Hyps.wrap_rwEqC q H (.all x p φ)
  | _, .bind H m x t, φ => Hyps.wrap_rwEqC q H (.bind m x t φ)
  | _, .anon H xs, φ => Hyps.wrap_rwEqC q H (.anon xs φ)

/-! ## Soundness -/

/-- **Soundness of the scoped sequent over the typed state**, given the
arms' (`Stmt.Sound`): what `H ⊢ φ` proves holds, its context in front, in
every typed state of the outer scope.  The arms' are proved in
`Calculus/Sound.lean` (`Stmt.sound`, `Proves.sound`). -/
theorem Proves.sound_of (hS : Stmt.Sound C) {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ}
    {φ : Fml C Γ} (d : Proves C R Γ₀ H φ) : ∀ σ, holds σ (H.wrap φ) := by
  induction d with
  | intro _ ih => exact ih
  | @andIntro Γ H φ ψ _ _ ih₁ ih₂ =>
    exact fun σ => H.wrap_and (χ := .and φ ψ) (fun _ a b => ⟨a, b⟩) σ (ih₁ σ) (ih₂ σ)
  | allIntro _ ih => exact ih
  | updIntro _ ih => exact ih
  | bindIntro _ ih => exact ih
  | @update Γ Γ' Γ₁ Γ₂ H m s ω κ φ U d _ _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.update U).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @updates Γ Δ Γ' Γ₁ Γ₂ H m s ω κ φ U V d _ _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.updates U V).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @guardedUpdates Γ Δ Γ₁ Γ₂ H m s ω κ φ c U V d _ _ _ ihT ihE =>
    intro σ
    have hTE : holds σ (H.wrap ((Premise.guardedUpdates c U V).fml m ω κ φ)) :=
      H.wrap_and (χ := (Premise.guardedUpdates c U V).fml m ω κ φ)
        (fun _ x y => ⟨x, y⟩) σ (ihT σ) (ihE σ)
    exact H.wrap_mono (fun τ h => hS _ _ s _ d τ ω κ φ h) σ hTE
  | @unfold Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.unfold P e).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @bind Γ Γ' Γ₁ Γ₂ H m s ω κ φ x t P d _ _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.bind x t P).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @split Γ Γ₁ Γ₂ Δ₁ Δ₂ H m s ω κ φ b c c' P Q d _ _ _ ihT ihE =>
    intro σ
    have hTE : holds σ (H.wrap ((Premise.split b c c' P Q).fml m ω κ φ)) :=
      H.wrap_and (χ := (Premise.split b c c' P Q).fml m ω κ φ) (fun _ x y => ⟨x, y⟩) σ
        (ihT σ) (ihE σ)
    exact H.wrap_mono (fun τ h => hS _ _ s _ d τ ω κ φ h) σ hTE
  | @check Γ Γ₁ Γ₂ H m s ω κ φ c d _ _ _ ihT ihE =>
    exact fun σ => H.wrap_and
      (fun τ a b => hS _ _ s _ d τ ω κ φ (show holds τ ((Premise.check c).fml m ω κ φ)
        from ⟨a, b⟩)) σ (ihT σ) (ihE σ)
  | @done Γ Γ' Γ₁ Γ₂ H m s ω κ φ b d _ _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.done b).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @branches Γ Γ₁ Γ₂ H m s ω κ φ bs d hne _ _ ih =>
    intro σ
    refine H.wrap_mono (φ := (Premise.branches bs).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ ?_
    refine H.wrap_conj σ _ ?_ ?_
    · cases bs with
      | nil => exact nomatch hne
      | cons _ _ => exact List.cons_ne_nil _ _
    · intro ψ hψ
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ
      exact ih b hb σ
  | @cases Γ Γ₁ Γ₂ H m s ω κ φ fs us d hne _ _ _ ihF ihU =>
    intro σ
    refine H.wrap_mono (φ := (Premise.cases fs us).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ ?_
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
  | @inv Γ Γ₁ Γ₂ Δ₀ Δ Γ₃ H m s ω κ φ I Bk xs hv U c c' hu hb P post d _ _ _ _ ihI ihT ihE =>
    intro σ
    let A : Fml C Δ := .upd m (Upd.nil.pop hb)
      (.modalK m P (.pop .block P.ext .nil) (Fml.invPost m hu ω κ φ post Bk))
    let B : Fml C Δ := .upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)
    let X : Fml C Γ := .imp (I.invHyp Bk) (.upd m U (.and (.imp c A) (.imp c' B)))
    have hX : holds σ ((H.anonHavoc xs hv).wrap X) :=
      (H.anonHavoc xs hv).wrap_and (φ := .imp (I.invHyp Bk) (.upd m U (.imp c A)))
        (ψ := .imp (I.invHyp Bk) (.upd m U (.imp c' B))) (χ := X)
        (fun τ x y hI => Upd.afterT_and (x hI) (y hI) fun _ f g => ⟨f, g⟩) σ (ihT σ) (ihE σ)
    rw [Hyps.wrap_anonHavoc] at hX
    have hF : holds σ (H.wrap ((Premise.inv I Bk xs hv U c c' hu hb P post).fml m ω κ φ)) :=
      H.wrap_and (φ := I.invHyp Bk) (ψ := Fml.anonHavoc xs hv X)
        (χ := .and (I.invHyp Bk) (Fml.anonHavoc xs hv X))
        (fun _ x y => ⟨x, y⟩) σ (ihI σ) hX
    exact H.wrap_mono (fun τ h => hS _ _ s _ d τ ω κ φ h) σ hF
  | @inline Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.inline P e).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @empty Γ Γ₂ H m κ φ _ ih =>
    exact fun σ => H.wrap_mono (φ := κ.exit m φ) (ψ := .modal m .nil κ φ)
      (fun τ h => holds_exit m κ φ τ h) σ (ih σ)
  | @closeTrue Γ H h => exact H.wrap_valid (φ := .tt) h fun _ => trivial
  | @closeFalse Γ H φ _ ih =>
    exact fun σ => H.wrap_mono (φ := .ff) (fun _ h => (h trivial).elim) σ (ih σ)
  | @merge Γ Δ Ε H m bs U U' V W φ hU hW _ ih =>
    intro σ
    have h : holds σ (H.wrap (Fml.binds bs (.upd m W φ))) := by
      have := ih σ
      rwa [show ((H.binds bs).upd m W).wrap φ = (H.binds bs).wrap (.upd m W φ) from rfl,
        Hyps.wrap_binds] at this
    rw [show (((H.upd m U).binds bs).upd m V).wrap φ = ((H.upd m U).binds bs).wrap (.upd m V φ)
      from rfl, Hyps.wrap_binds]
    exact H.wrap_mono (φ := Fml.binds bs (.upd m W φ))
      (ψ := .upd m U (Fml.binds bs (.upd m V φ)))
      (fun τ hτ => holds_liftBinds bs hU τ
        (Fml.binds_mono bs (fun ρ hρ => holds_upd_seqPar hW ρ hρ) τ hτ)) σ h
  | @updRw Γ Δ H U φ p q hq _ ih =>
    exact fun σ => H.wrap_mono (φ := .upd .box (U.rwC q) φ) (ψ := .upd .box U φ)
      (fun τ hτ => holds_upd_rwC hq τ hτ) σ (ih σ)
  | @rewrite Γ H φ p q hq _ ih =>
    intro σ
    have h := ih σ
    rw [Hyps.wrap_rwEqC] at h
    exact (Fml.rwEqC_holds hq _ σ).1 h
  | closeHolds h _ => exact h

end Solidity
