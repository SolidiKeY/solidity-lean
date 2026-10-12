import Solidity.Calculus.Proves
import Solidity.Semantics.StateErase

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

An update's reading asks of every typed state that erases to the one it
ends in, so a rule's premise gives its conclusion in the state the typed
run ends in, one of them: only that direction is needed here.
-/

namespace Solidity
open Solidity (Modality RuleSet)

variable {C : Contract}

/-! ## The per-arm interface -/

/-- **A premise is sound** for the statement `s` in the typed state `σ`
under `m`: in front of any rest, frames and postcondition, it gives
`⟨ s; ω κ ⟩ φ` (`Premise.Sound`, over `State`). -/
def Premise.Sound (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
    (σ : State C Γ) : Prop :=
  ∀ {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀),
    holds σ (p.fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ)

/-- **Every rule the strategy fires is sound** over the typed state, in
every typed state, at any fresh index (`Stmt.Sound`, over `State`). -/
def Stmt.Sound (C : Contract) : Prop :=
  ∀ (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ'),
    s.step k m = p → ∀ σ : State C Γ, Premise.Sound m s p σ

/-! ## Scope ends -/

theorem TEnv.thin_erase {H : HTy} : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : TEnv C H Δ) →
    TEnv.erase Γ (TEnv.thin h e) = Env.thin h (TEnv.erase Δ e)
  | _, _, .refl, _ => rfl
  | _, _, .keep h, e => congrArg (Prod.mk _) (TEnv.thin_erase h e.2)
  | _, _, .drop h, e => TEnv.thin_erase h e.2

theorem State.thin_erase {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    (σ.thin h).erase = σ.erase.thin h := by
  simp only [State.erase, State.thin, State.withEnv, EState.thin, EState.withEnv, TEnv.thin_erase]

theorem Prog.runFrames_seq {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) : Prog.runFrames σ .nil (.seq ω κ) = Prog.runFrames σ ω κ := by
  simp only [Prog.runFrames, Prog.run_nil, Frames.run, TRun.seq, bind, Except.bind]
  cases Prog.run σ ω with
  | error => rfl
  | ok o =>
    simp only [Except.map]
    cases Frames.run o.st κ <;> rfl

/-- A finished program's frames, as the formula `emptyModality` leaves
(`Frames.exit`), give the modality: each scope end's update is read in the
state the frame pops to, one of the states its erasure reaches. -/
theorem holds_exit (m : Modality) {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ (φ : Fml C Γ₀) (σ : State C Γ), holds σ (κ.exit m φ) → holds σ (.modal m .nil κ φ)
  | _, .nil, φ, σ, h => ⟨h, nofun⟩
  | _, .seq .nil κ, φ, σ, h => by
    show m.afterRunTR (holds · φ) (Prog.runFrames σ .nil (.seq .nil κ))
    rw [Prog.runFrames_seq]
    exact holds_exit m κ φ σ h
  | _, .seq (.cons s ω) κ, φ, σ, h => by
    show m.afterRunTR (holds · φ) (Prog.runFrames σ .nil (.seq (.cons s ω) κ))
    rw [Prog.runFrames_seq]
    exact h
  | _, .pop _ e κ, φ, σ, h =>
    holds_exit m κ φ (σ.drop e) (h (σ.drop e) (State.drop_erase e σ) (List.prefix_refl _))
  | _, .drop e κ, φ, σ, h =>
    holds_exit m κ φ (σ.thin e) (h (σ.thin e) (State.thin_erase e σ) (List.prefix_refl _))

/-! ## Outcomes -/

theorem _root_.Solidity.Modality.afterC_and {α : Type} {m : Modality} {p q r : α → Prop} {x : Semantics.Res α}
    (hp : m.afterC p x) (hq : m.afterC q x) (h : ∀ a, p a → q a → r a) : m.afterC r x := by
  cases x with
  | ok a => exact h a hp hq
  | error _ => exact hp

/-- A pop or a drop never halts. -/
theorem Upd.apply_popsOnly {Γ : Ctx} (σ : EState C Γ) {Δ : Ctx} (U : Upd C Γ Δ)
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
      Modality.afterC_and f g fun _ x y σ' e hx => h σ' (x σ' e hx) (y σ' e hx)
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
      refine ih (φ := .upd .box U φ) hb fun τ => ?_
      show Modality.afterC .box _ _
      cases U.apply τ.erase with
      | ok _ => exact fun σ' _ _ => h σ'
      | error _ => trivial
    | diamond =>
      have hb' : U.popsOnly = true ∧ H.boxOnly = true := Bool.and_eq_true_iff.mp hb
      refine ih (φ := .upd .diamond U φ) hb'.2 fun τ => ?_
      obtain ⟨a, ha⟩ := Upd.apply_popsOnly τ.erase U hb'.1
      show Modality.afterC .diamond _ _
      rw [ha]
      exact fun σ' _ _ => h σ'
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
theorem Hyps.wrap_rwEqC (q : Tm C [] .val × Tm C [] .val) {Γ₀ : Ctx} :
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
  | allIntro _ ih => exact ih
  | updIntro _ ih => exact ih
  | bindIntro _ ih => exact ih
  | @update Γ Γ' Γ₁ Γ₂ H m s ω κ φ U d _ _ ih =>
    exact fun σ => H.wrap_mono (φ := (Premise.update U).fml m ω κ φ)
      (fun τ h => hS _ _ s _ d τ ω κ φ h) σ (ih σ)
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
  | @inv Γ Γ₁ Γ₂ Δ₀ Δ Γ₃ H m s ω κ φ I xs hv U c c' hu hb P post d _ _ _ _ ihI ihT ihE =>
    intro σ
    let A : Fml C Δ := .upd m (Upd.nil.pop hb) (.modalK m P (.pop .block P.ext .nil) post)
    let B : Fml C Δ := .upd m (Upd.nil.pop (hu.trans hb)) (.modalK m ω κ φ)
    let X : Fml C Γ := .imp I (.upd m U (.and (.imp c A) (.imp c' B)))
    have hX : holds σ ((H.anonHavoc xs hv).wrap X) :=
      (H.anonHavoc xs hv).wrap_and (φ := .imp I (.upd m U (.imp c A)))
        (ψ := .imp I (.upd m U (.imp c' B))) (χ := X)
        (fun τ x y hI => Modality.afterC_and (x hI) (y hI) fun _ f g σ' e hx =>
          ⟨f σ' e hx, g σ' e hx⟩) σ (ihT σ) (ihE σ)
    rw [Hyps.wrap_anonHavoc] at hX
    have hF : holds σ (H.wrap ((Premise.inv I xs hv U c c' hu hb P post).fml m ω κ φ)) :=
      H.wrap_and (φ := I) (ψ := Fml.anonHavoc xs hv X) (χ := .and I (Fml.anonHavoc xs hv X))
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
  | @updRw Γ Δ H U φ q hq _ ih =>
    exact fun σ => H.wrap_mono (φ := .upd .box (U.rwC q) φ) (ψ := .upd .box U φ)
      (fun τ hτ => holds_upd_rwC hq τ hτ) σ (ih σ)
  | @rewrite Γ H φ q hq _ ih =>
    intro σ
    have h := ih σ
    rw [Hyps.wrap_rwEqC] at h
    exact (Fml.rwEqC_holds hq _ σ).1 h
  | closeHolds h _ => exact h

end Solidity
