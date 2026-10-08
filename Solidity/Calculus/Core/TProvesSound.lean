import Solidity.Calculus.Core.ProvesSound
import Solidity.Calculus.Core.TCloseErase

/-!
# The scoped sequent is sound over the typed state: the structure

`Calculus/Core/ProvesSound.lean`'s `Proves.sound`, read over the typed
state (`tholds`, `Calculus/Core/TLogic.lean`): what `H ⊢ φ` proves holds,
its context in front, in every typed state of the outer scope
(`Proves.tsound`), given that every rule the strategy fires is sound there
(`Stmt.TSound`, the arms' part, `Premise.TSound` per premise).  This module
is the structural part, which does not depend on any arm: the context is
monotone and keeps a conjunction (`Hyps.twrap_and`), `closeTrue` holds
behind a context with no diamond update but scope ends
(`Hyps.twrap_valid`), `emptyModality` goes into the frames
(`tholds_exit`), and `close` is `tholds_of_erase_valid`
(`Calculus/Core/TCloseErase.lean`).

**Not provable as stated until decisions 2 and 3** (`docs/intrinsic.md`,
W2 `sound`): `Stmt.TSound C` is false for a contract with a `bool` mapping
key (`close` proves `[ v = m[true]; ] false`) and under the diamond on a
length past `uint`'s range, and `Proves.tvalid` is vacuous there.  The
decision taken goes into `Stmt.TSound`, as a restriction, not a false
hypothesis.

An update's typed reading asks of every typed state that erases to the one
it ends in, so a rule's premise gives its conclusion in the state the typed
run ends in, one of them: only that direction is needed here.
-/

namespace Solidity.Core

open Solidity (Modality RuleSet)

variable {C : Contract}

/-! ## The per-arm interface -/

/-- **A premise is sound** for the statement `s` in the typed state `σ`
under `m`: in front of any rest, frames and postcondition, it gives
`⟨ s; ω κ ⟩ φ` (`Premise.Sound`, over `TState`). -/
def Premise.TSound (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
    (σ : TState C Γ) : Prop :=
  ∀ {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀),
    tholds σ (p.fml m ω κ φ) → tholds σ (.modal m (.cons s ω) κ φ)

/-- **Every rule the strategy fires is sound** over the typed state, in
every typed state, at any fresh index (`Stmt.Sound`, over `TState`). -/
def Stmt.TSound (C : Contract) : Prop :=
  ∀ (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ'),
    s.step k m = some p → ∀ σ : TState C Γ, Premise.TSound m s p σ

/-! ## Scope ends -/

theorem TEnv.thin_erase {H : HTy} : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : TEnv C H Δ) →
    TEnv.erase Γ (TEnv.thin h e) = Env.thin h (TEnv.erase Δ e)
  | _, _, .refl, _ => rfl
  | _, _, .keep h, e => congrArg (Prod.mk _) (TEnv.thin_erase h e.2)
  | _, _, .drop h, e => TEnv.thin_erase h e.2

theorem TState.thin_erase {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : TState C Δ) :
    (σ.thin h).erase = σ.erase.thin h := by
  simp only [TState.erase, TState.thin, TState.withEnv, State.thin, State.withEnv, TEnv.thin_erase]

theorem Prog.trunFrames_seq {Γ Γ₁ Γ₀ : Ctx} (σ : TState C Γ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) : Prog.trunFrames σ .nil (.seq ω κ) = Prog.trunFrames σ ω κ := by
  simp only [Prog.trunFrames, Prog.trun_nil, Frames.trun, TRun.seq, bind, Except.bind]
  cases Prog.trun σ ω with
  | error => rfl
  | ok o =>
    simp only [Except.map]
    cases Frames.trun o.st κ <;> rfl

/-- A finished program's frames, as the formula `emptyModality` leaves
(`Frames.exit`), give the modality: each scope end's update is read in the
state the frame pops to, one of the states its erasure reaches. -/
theorem tholds_exit (m : Modality) {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ (φ : Fml C Γ₀) (σ : TState C Γ), tholds σ (κ.exit m φ) → tholds σ (.modal m .nil κ φ)
  | _, .nil, φ, σ, h => ⟨h, nofun⟩
  | _, .seq .nil κ, φ, σ, h => by
    show m.afterRunTR (tholds · φ) (Prog.trunFrames σ .nil (.seq .nil κ))
    rw [Prog.trunFrames_seq]
    exact tholds_exit m κ φ σ h
  | _, .seq (.cons s ω) κ, φ, σ, h => by
    show m.afterRunTR (tholds · φ) (Prog.trunFrames σ .nil (.seq (.cons s ω) κ))
    rw [Prog.trunFrames_seq]
    exact h
  | _, .pop _ e κ, φ, σ, h =>
    tholds_exit m κ φ (σ.drop e) (h (σ.drop e) (TState.drop_erase e σ))
  | _, .drop e κ, φ, σ, h =>
    tholds_exit m κ φ (σ.thin e) (h (σ.thin e) (TState.thin_erase e σ))

/-! ## The context -/

section Wrap

variable {Γ₀ : Ctx}

/-- Two formulas under the context give a third that follows from both. -/
theorem Hyps.twrap_and {Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    ∀ {φ ψ χ : Fml C Γ}, (∀ τ, tholds τ φ → tholds τ ψ → tholds τ χ) →
      ∀ σ, tholds σ (H.wrap φ) → tholds σ (H.wrap ψ) → tholds σ (H.wrap χ) := by
  induction H with
  | nil => intro φ ψ χ h σ; exact h σ
  | pre H a ih =>
    intro φ ψ χ h
    exact ih (φ := .imp a φ) (ψ := .imp a ψ) (χ := .imp a χ) fun τ f g ha => h τ (f ha) (g ha)
  | upd H m U ih =>
    intro φ ψ χ h
    exact ih (φ := .upd m U φ) (ψ := .upd m U ψ) (χ := .upd m U χ) fun τ f g =>
      Modality.afterC_and f g fun _ x y σ' e => h σ' (x σ' e) (y σ' e)
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
theorem Hyps.twrap_mono {Γ : Ctx} (H : Hyps C Γ₀ Γ) {φ ψ : Fml C Γ}
    (h : ∀ τ, tholds τ φ → tholds τ ψ) (σ : TState C Γ₀) (hφ : tholds σ (H.wrap φ)) :
    tholds σ (H.wrap ψ) :=
  H.twrap_and (fun τ a _ => h τ a) σ hφ hφ

/-- A conjunction of at least one formula, each under the context. -/
theorem Hyps.twrap_conj {Γ : Ctx} (H : Hyps C Γ₀ Γ) (σ : TState C Γ₀) :
    ∀ (ψs : List (Fml C Γ)), ψs ≠ [] → (∀ ψ ∈ ψs, tholds σ (H.wrap ψ)) →
      tholds σ (H.wrap (Fml.conj ψs))
  | [], hne, _ => absurd rfl hne
  | [φ], _, h => h φ (List.mem_singleton_self φ)
  | φ :: ψ :: ψs, _, h =>
    H.twrap_and (φ := φ) (ψ := Fml.conj (ψ :: ψs)) (χ := .and φ (Fml.conj (ψ :: ψs)))
      (fun _ a b => ⟨a, b⟩) σ (h φ List.mem_cons_self)
      (H.twrap_conj σ (ψ :: ψs) (List.cons_ne_nil _ _) fun χ hχ => h χ (List.mem_cons_of_mem _ hχ))

/-- A valid formula behind a context with no diamond update but scope ends
holds. -/
theorem Hyps.twrap_valid {Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    ∀ {φ : Fml C Γ}, H.boxOnly = true → (∀ τ, tholds τ φ) → ∀ σ, tholds σ (H.wrap φ) := by
  induction H with
  | nil => intro φ _ h σ; exact h σ
  | pre H a ih => intro φ hb h; exact ih (φ := .imp a φ) hb fun τ _ => h τ
  | upd H m U ih =>
    intro φ hb h
    cases m with
    | box =>
      refine ih (φ := .upd .box U φ) hb fun τ => ?_
      show Modality.afterC .box _ _
      cases U.apply τ.erase with
      | ok _ => exact fun σ' _ => h σ'
      | error _ => trivial
    | diamond =>
      have hb' : U.popsOnly = true ∧ H.boxOnly = true := Bool.and_eq_true_iff.mp hb
      refine ih (φ := .upd .diamond U φ) hb'.2 fun τ => ?_
      obtain ⟨a, ha, _⟩ := Upd.apply_popsOnly τ.erase U hb'.1
      show Modality.afterC .diamond _ _
      rw [ha]
      exact fun σ' _ => h σ'
  | havoc H ih => intro φ hb h; exact ih (φ := .havoc φ) hb fun τ _ _ => h _
  | all H x p ih => intro φ hb h; exact ih (φ := .all x p φ) hb fun τ _ => h _
  | bind H m x t ih =>
    intro φ hb h
    cases m with
    | box => exact ih (φ := .bind .box x t φ) hb fun τ v => h _
    | diamond =>
      have hb' := Bool.and_eq_true_iff.mp hb
      exact ih (φ := .bind .diamond x t φ) hb'.2 fun τ =>
        Modality.forallB_intro (fun _ => LTy.tdenote_nonempty t hb'.1) fun _ => h _
  | anon H xs ih => intro φ hb h; exact ih (φ := .anon xs φ) hb fun τ _ => h _

end Wrap

/-! ## Soundness -/

/-- **Soundness of the scoped sequent over the typed state**, given the
arms' (`Stmt.TSound`): what `H ⊢ φ` proves holds, its context in front, in
every typed state of the outer scope. -/
theorem Proves.tsound (hS : Stmt.TSound C) {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ}
    {φ : Fml C Γ} (d : Proves C R Γ₀ H φ) : ∀ σ, tholds σ (H.wrap φ) := by
  induction d with
  | intro _ ih => exact ih
  | allIntro _ ih => exact ih
  | updIntro _ ih => exact ih
  | bindIntro _ ih => exact ih
  | @update Γ Γ' Γ₁ Γ₂ H m s ω κ φ U d _ ih =>
    exact fun σ => H.twrap_mono (φ := (Premise.update U).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @unfold Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ ih =>
    exact fun σ => H.twrap_mono (φ := (Premise.unfold P e).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @bind Γ Γ' Γ₁ Γ₂ H m s ω κ φ x t P d _ ih =>
    exact fun σ => H.twrap_mono (φ := (Premise.bind x t P).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @split Γ Γ₁ Γ₂ Δ₁ Δ₂ H m s ω κ φ b c c' P Q d _ _ ihT ihE =>
    intro σ
    have hTE : tholds σ (H.wrap ((Premise.split b c c' P Q).fml m ω κ φ)) :=
      H.twrap_and (χ := (Premise.split b c c' P Q).fml m ω κ φ) (fun _ x y => ⟨x, y⟩) σ
        (ihT σ) (ihE σ)
    exact H.twrap_mono (fun τ h => hS _ _ s _ d τ ω κ φ h) σ hTE
  | @check Γ Γ₁ Γ₂ H m s ω κ φ c d _ _ ihT ihE =>
    exact fun σ => H.twrap_and
      (fun τ a b => hS _ _ s _ d τ ω κ φ (show tholds τ ((Premise.check c).fml m ω κ φ)
        from ⟨a, b⟩)) σ (ihT σ) (ihE σ)
  | @done Γ Γ' Γ₁ Γ₂ H m s ω κ φ b d _ ih =>
    exact fun σ => H.twrap_mono (φ := (Premise.done b).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @branches Γ Γ₁ Γ₂ H m s ω κ φ bs d hne _ ih =>
    intro σ
    refine H.twrap_mono (φ := (Premise.branches bs).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ ?_
    refine H.twrap_conj σ _ ?_ ?_
    · cases bs with
      | nil => exact nomatch hne
      | cons _ _ => exact List.cons_ne_nil _ _
    · intro ψ hψ
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ
      exact ih b hb σ
  | @cases Γ Γ₁ Γ₂ H m s ω κ φ fs us d hne _ _ ihF ihU =>
    intro σ
    refine H.twrap_mono (φ := (Premise.cases fs us).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ ?_
    refine H.twrap_conj σ _ ?_ ?_
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
  | @inv Γ Γ₁ Γ₂ Δ₀ Δ Γ₃ H m s ω κ φ I xs hv U c c' hu hb P post d _ _ _ ihI ihT ihE =>
    intro σ
    let A : Fml C Δ := .upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil) post)
    let B : Fml C Δ := .upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)
    let X : Fml C Γ := .imp I (.upd m U (.and (.imp c A) (.imp c' B)))
    have hX : tholds σ ((H.anonHavoc xs hv).wrap X) :=
      (H.anonHavoc xs hv).twrap_and (φ := .imp I (.upd m U (.imp c A)))
        (ψ := .imp I (.upd m U (.imp c' B))) (χ := X)
        (fun τ x y hI => Modality.afterC_and (x hI) (y hI) fun _ f g σ' e =>
          ⟨f σ' e, g σ' e⟩) σ (ihT σ) (ihE σ)
    rw [Hyps.wrap_anonHavoc] at hX
    have hF : tholds σ (H.wrap ((Premise.inv I xs hv U c c' hu hb P post).fml m ω κ φ)) :=
      H.twrap_and (φ := I) (ψ := Fml.anonHavoc xs hv X) (χ := .and I (Fml.anonHavoc xs hv X))
        (fun _ x y => ⟨x, y⟩) σ (ihI σ) hX
    exact H.twrap_mono (fun τ h => hS _ _ s _ d τ ω κ φ h) σ hF
  | @inline Γ Γ' Γ'' Γ₁ Γ₂ H m s ω κ φ P e d _ ih =>
    exact fun σ => H.twrap_mono (φ := (Premise.inline P e).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
  | @empty Γ Γ₂ H m κ φ _ ih =>
    exact fun σ => H.twrap_mono (φ := κ.exit m φ) (ψ := .modal m .nil κ φ)
      (fun τ h => tholds_exit m κ φ τ h) σ (ih σ)
  | @closeTrue Γ H h => exact H.twrap_valid (φ := .tt) h fun _ => trivial
  | close ns hlen hnd h hc hB =>
    exact fun σ => tholds_of_erase_valid _ hlen hnd (Fml.closableB_tclosable hc) hB h σ

/-- **A goal proved with an empty context is valid over the typed state**,
given the arms'. -/
theorem Proves.tvalid (hS : Stmt.TSound C) {R : RuleSet} {φ : Fml C []}
    (d : Proves C R [] .nil φ) : TValid φ :=
  Proves.tsound hS d

end Solidity.Core
