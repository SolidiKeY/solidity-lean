import Solidity.Calculus.CallerModelRun

/-!
# Valid under a caller model: the endpoints and the weakening theorem

The readings `ValidM M ts φ` (`Calculus/CallerModel.lean`), proved:

* **the endpoints are today's readings**: `ValidM .any ts φ ↔ ValidT ts φ`
  (`validM_any`, from `holdsR_any_iff`), and `ValidM .none ts φ` is
  `Fml.Valid φ`, so `ValidT (.noCallback I) φ` for a formula with no `try`
  and no value call (`validM_none_iff_noCallback`);
* **the weakening theorem** (`ValidM.weaken`): valid under a stronger
  attacker is valid under a weaker one, `M ≤ M'`, for a formula whose
  modalities stand positively (`Fml.posModal true`, every
  `pre → [ P ] post` with a first-order `pre`).  A modality in a negative
  position would turn the inclusion of runs around; such formulas are not
  monotone in the attacker under any reading.

The inclusion of runs is `ExecPM.mono` (`Calculus/CallerModelRun.lean`):
`CallerModel.Le.allows` says a weaker model allows less at each
resumption; below every model, `none`'s deterministic run is a run of each
(`Prog.execM_run`).
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-! ## The order on what a callee may leave -/

namespace CallerModel

/-- **A weaker model allows less**: `M ≤ M'` includes `M`'s resumptions in
`M'`'s. -/
theorem Le.allows {M M' : CallerModel C} (h : M.Le M') (J : StateInv C) {Γ : Ctx}
    (σ : State C Γ) (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) :
    M.Allows J σ st nt sb → M'.Allows J σ st nt sb := by
  cases h with
  | refl => exact id
  | none M' =>
    intro ⟨hs, hn, hb⟩
    subst hs hn hb
    exact M'.allows_refl J σ
  | any => intro _; trivial
  | staticNr R =>
    intro ⟨hs, hn, hb⟩
    subst hs hn hb
    exact Reentry.Chain.refl _

/-- The order is transitive. -/
theorem Le.trans {M₁ M₂ M₃ : CallerModel C} (h₁ : M₁.Le M₂) (h₂ : M₂.Le M₃) : M₁.Le M₃ := by
  cases h₁ with
  | refl => exact h₂
  | none => exact .none _
  | any => cases h₂ with
    | refl => exact .any _
    | any => exact .any _
  | staticNr R => cases h₂ with
    | refl => exact .staticNr R
    | any => exact .any _

end CallerModel

/-! ## Re-entry under the lock -/

namespace Reentry

variable {R : Reentry C} {J : StateInv C}

/-- What the lock lets a callee reach, a callee calling any entry reaches. -/
theorem Reach.toAny {g g' : State C []} (h : R.Reach J g g') : R.ReachAny J g g' := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .tail ih (hs.elim fun f hf => ⟨f, hf.2⟩)

/-- **What the lock gives**: from a state in which the lock is held, when
every guarded entry is guarded (`Guards`, the lock judgment) and no unguarded
one releases the lock (`KeepsHeld`), a callee calling back into any entry
reaches exactly what the lock lets one reach (`Reach`). -/
theorem reachAny_iff (hG : R.Guards J) (hK : R.KeepsHeld J) {g g' : State C []}
    (hh : R.held g.storage) : R.ReachAny J g g' ↔ R.Reach J g g' := by
  refine ⟨fun h => ?_, Reach.toAny⟩
  have key : R.Reach J g g' ∧ R.held g'.storage := by
    induction h with
    | refl => exact ⟨.refl _, hh⟩
    | tail _ hs ih =>
      obtain ⟨hr, hb⟩ := ih
      obtain ⟨f, hc⟩ := hs
      cases hf : R.guarded f with
      | true => exact absurd hc (hG f hf _ _ hb)
      | false => exact ⟨.tail hr ⟨f, .inl hf, hc⟩, hK f hf _ _ hb hc⟩
  exact key.1

end Reentry

/-! ## `any` is today's callback reading -/

section Any

variable {J : StateInv C}

/-- `COut.after` is monotone in its postcondition. -/
theorem COut.after_imp {H : HTy} {Γ : Ctx} {m : Modality} {p q : State C Γ → Prop}
    (hpq : ∀ τ, p τ → q τ) : (o : COut C H Γ) → o.after m p → o.after m q
  | .ok _, h => hpq _ h
  | .halt _, h => h
  | .violated, h => h

/-- Under `any`, `thenFM` is `thenF`. -/
theorem COut.thenFM_any_iff {H : HTy} {Γ₁ Γ₀ : Ctx} (κ : Frames C Γ₁ Γ₀) (m : Modality)
    (p : State C Γ₀ → Prop) : (o : COut C H Γ₁) → (o.thenFM .any J κ m p ↔ o.thenF J κ m p)
  | .ok _ => ⟨fun h o' hf => h o' (ExecF.ofExecFM hf), fun h o' hf => h o' (ExecFM.toExecF hf)⟩
  | .halt _ => Iff.rfl
  | .violated => Iff.rfl

/-- **Under `any`, the reading is `holdsC`.** -/
theorem holdsR_any_iff {I : Fml C []} {pay : Bool} : {Γ : Ctx} → (φ : Fml C Γ) →
    ∀ σ : State C Γ, (holdsR .any I pay σ φ ↔ holdsC I pay σ φ)
  | _, .tt, _ | _, .eq _ _, _ | _, .wellFormed _, _ => Iff.rfl
  | _, .not φ, σ => not_congr (holdsR_any_iff φ σ)
  | _, .and φ ψ, σ => and_congr (holdsR_any_iff φ σ) (holdsR_any_iff ψ σ)
  | _, .imp φ ψ, σ => imp_congr (holdsR_any_iff φ σ) (holdsR_any_iff ψ σ)
  | _, .upd m U φ, σ => by
    have e : (holdsR .any I pay · φ) = (holdsC I pay · φ) :=
      funext fun τ => propext (holdsR_any_iff φ τ)
    show U.afterT m σ _ ↔ U.afterT m σ _
    rw [e]
  | _, .modal m P κ φ, σ => by
    have e : (holdsR .any I pay · φ) = (holdsC I pay · φ) :=
      funext fun τ => propext (holdsR_any_iff φ τ)
    show (∀ o, ExecPM .any _ σ P o → o.thenFM .any _ κ m (holdsR .any I pay · φ)) ↔
      (∀ o, ExecP _ σ P o → o.thenF _ κ m (holdsC I pay · φ))
    rw [e]
    exact ⟨fun h o hp => (COut.thenFM_any_iff κ m _ o).1 (h o (ExecP.ofExecPM hp)),
      fun h o hp => (COut.thenFM_any_iff κ m _ o).2 (h o (ExecPM.toExecP hp))⟩
  | _, .havoc φ, _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => holdsR_any_iff φ _
  | _, .all _ _ φ, _ => forall_congr' fun _ => holdsR_any_iff φ _
  | _, .bind m _ t φ, σ => by
    have e : (fun v : t.TDenote C σ.H => holdsR .any I pay (σ.push v) φ) =
        (fun v : t.TDenote C σ.H => holdsC I pay (σ.push v) φ) :=
      funext fun v => propext (holdsR_any_iff φ (σ.push v))
    show m.forallB _ ↔ m.forallB _
    rw [e]
  | _, .anon _ φ, _ => forall_congr' fun _ => holdsR_any_iff φ _
  | _, .allocAll _ _ φ, _ => forall_congr' fun _ => holdsR_any_iff φ _
  | _, .grow φ, _ => forall_congr' fun _ => forall_congr' fun _ => holdsR_any_iff φ _

/-- **`any` is today's reading**: valid under `any` is `ValidT`. -/
theorem validM_any {ts : TransferSem C} {φ : Fml C []} : ValidM .any ts φ ↔ ValidT ts φ :=
  forall_congr' fun σ => holdsR_any_iff φ σ

/-- **`none` is the deterministic reading.** -/
theorem validM_none {ts : TransferSem C} {φ : Fml C []} : ValidM .none ts φ ↔ Fml.Valid φ :=
  Iff.rfl

/-- **`none` is today's `noCallback`**, for a formula with no `try` and no
value call (`validT_noCallback_iff`). -/
theorem validM_none_iff_noCallback {ts : TransferSem C} {I : Invariant C} {φ : Fml C []}
    (h : φ.callsBack false = false) : ValidM .none ts φ ↔ ValidT (.noCallback I) φ :=
  (validT_noCallback_iff h).symm

end Any

/-! ## Polarity -/

/-- Whether every modality of `φ` stands in a position of polarity `p`
(`true`: positive), so that `φ`'s truth falls as the runs grow. -/
def Fml.posModal : Bool → {Γ : Ctx} → Fml C Γ → Bool
  | _, _, .tt | _, _, .eq _ _ | _, _, .wellFormed _ => true
  | p, _, .not φ => Fml.posModal (!p) φ
  | p, _, .and φ ψ => Fml.posModal p φ && Fml.posModal p ψ
  | p, _, .imp φ ψ => Fml.posModal (!p) φ && Fml.posModal p ψ
  | p, _, .upd _ _ φ => Fml.posModal p φ
  | p, _, .modal _ _ _ φ => p && Fml.posModal p φ
  | p, _, .havoc φ | p, _, .all _ _ φ | p, _, .bind _ _ _ φ | p, _, .anon _ φ
  | p, _, .allocAll _ _ φ | p, _, .grow φ => Fml.posModal p φ

/-- `a` gives `b` at a positive polarity, `b` gives `a` at a negative one. -/
def Polar : Bool → Prop → Prop → Prop
  | true, a, b => a → b
  | false, a, b => b → a

/-- Polarity through a negation: flipped. -/
theorem Polar.not {p : Bool} {a b : Prop} (h : Polar (!p) a b) : Polar p (¬ a) (¬ b) := by
  cases p with
  | true => exact fun ha hb => ha (h hb)
  | false => exact fun hb ha => hb (h ha)

/-- Polarity through a conjunction. -/
theorem Polar.and {p : Bool} {a b c d : Prop} (h₁ : Polar p a b) (h₂ : Polar p c d) :
    Polar p (a ∧ c) (b ∧ d) := by
  cases p with
  | true => exact fun h => ⟨h₁ h.1, h₂ h.2⟩
  | false => exact fun h => ⟨h₁ h.1, h₂ h.2⟩

/-- Polarity through an implication: flipped on the left. -/
theorem Polar.imp {p : Bool} {a b c d : Prop} (h₁ : Polar (!p) a b) (h₂ : Polar p c d) :
    Polar p (a → c) (b → d) := by
  cases p with
  | true => exact fun h hb => h₂ (h (h₁ hb))
  | false => exact fun h ha => h₂ (h (h₁ ha))

/-- Polarity through a quantifier. -/
theorem Polar.forall {p : Bool} {α : Sort _} {a b : α → Prop} (h : ∀ x, Polar p (a x) (b x)) :
    Polar p (∀ x, a x) (∀ x, b x) := by
  cases p with
  | true => exact fun ha x => h x (ha x)
  | false => exact fun hb x => h x (hb x)

/-- Polarity through an update. -/
theorem Polar.afterT {p : Bool} {Γ Δ : Ctx} {m : Modality} {σ : State C Γ} {U : Upd C Γ Δ}
    {a b : State C Δ → Prop} (h : ∀ τ, Polar p (a τ) (b τ)) :
    Polar p (U.afterT m σ a) (U.afterT m σ b) := by
  cases p with
  | true => exact fun ha => Upd.afterT_imp ha h
  | false => exact fun hb => Upd.afterT_imp hb h

/-! ## Weakening between models that call back -/

section Mono

variable {M M' : CallerModel C} {I : Fml C []} {pay : Bool}

/-- `thenFM` falls as the model grows and rises with its postcondition. -/
theorem COut.thenFM_mono
    (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb,
      M.Allows (I.stateInv pay) σ st nt sb → M'.Allows (I.stateInv pay) σ st nt sb)
    {H : HTy} {Γ₁ Γ₀ : Ctx} {κ : Frames C Γ₁ Γ₀} {m : Modality} {p q : State C Γ₀ → Prop}
    (hpq : ∀ τ, p τ → q τ) :
    (o : COut C H Γ₁) → o.thenFM M' (I.stateInv pay) κ m p → o.thenFM M (I.stateInv pay) κ m q
  | .ok _, h => fun o' hf => COut.after_imp hpq o' (h o' (ExecFM.mono hA hf))
  | .halt _, h => h
  | .violated, h => h

/-- **The reading falls as the attacker grows**, at the polarity `φ`'s
modalities stand in: a positive formula true under `M'` is true under a
model `M` allowing less, a negative one the other way. -/
theorem holdsR_mono
    (hA : ∀ {Γ : Ctx} (σ : State C Γ) st nt sb,
      M.Allows (I.stateInv pay) σ st nt sb → M'.Allows (I.stateInv pay) σ st nt sb) :
    (p : Bool) → {Γ : Ctx} → (φ : Fml C Γ) → φ.posModal p = true → ∀ σ : State C Γ,
      Polar p (holdsR M' I pay σ φ) (holdsR M I pay σ φ)
  | p, _, .tt, _, _ | p, _, .eq _ _, _, _ | p, _, .wellFormed _, _, _ => by
    cases p <;> exact id
  | p, _, .not φ, h, σ => Polar.not (holdsR_mono hA (!p) φ h σ)
  | p, _, .and φ ψ, h, σ => by
    have h' : (φ.posModal p && ψ.posModal p) = true := h
    rw [Bool.and_eq_true] at h'
    exact Polar.and (holdsR_mono hA p φ h'.1 σ) (holdsR_mono hA p ψ h'.2 σ)
  | p, _, .imp φ ψ, h, σ => by
    have h' : (φ.posModal (!p) && ψ.posModal p) = true := h
    rw [Bool.and_eq_true] at h'
    exact Polar.imp (holdsR_mono hA (!p) φ h'.1 σ) (holdsR_mono hA p ψ h'.2 σ)
  | p, _, .upd m U φ, h, σ => Polar.afterT (U := U) fun τ => holdsR_mono hA p φ h τ
  | p, _, .modal m P κ φ, h, σ => by
    have h' : (p && φ.posModal p) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hp, hφ⟩ := h'
    subst hp
    intro H o hr
    exact COut.thenFM_mono hA (fun τ => holdsR_mono hA true φ hφ τ) o (H o (ExecPM.mono hA hr))
  | p, _, .havoc φ, h, σ =>
    Polar.forall fun _ => Polar.forall fun _ => Polar.forall fun _ => holdsR_mono hA p φ h _
  | p, _, .all _ _ φ, h, σ => Polar.forall fun _ => holdsR_mono hA p φ h _
  | p, _, .bind m _ t φ, h, σ => Polar.forall (α := t.TDenote C σ.H) fun v => holdsR_mono hA p φ h _
  | p, _, .anon _ φ, h, σ => Polar.forall fun _ => holdsR_mono hA p φ h _
  | p, _, .allocAll _ _ φ, h, σ => Polar.forall fun _ => holdsR_mono hA p φ h _
  | p, _, .grow φ, h, σ =>
    Polar.forall fun _ => Polar.forall fun _ => holdsR_mono hA p φ h _

end Mono

/-! ## Below every model: the deterministic reading -/

section None

variable {M : CallerModel C} {I : Fml C []} {pay : Bool}

/-- **A positive formula true under a model is true without callbacks**: the
deterministic run, through the program and its frames, is a run under every
model (`Prog.execM_run`, `Frames.execM_run`), unless it breaks the
invariant, which no run under `M` may. -/
theorem holds_of_holdsR :
    (p : Bool) → {Γ : Ctx} → (φ : Fml C Γ) → φ.posModal p = true → ∀ σ : State C Γ,
      Polar p (holdsR M I pay σ φ) (holds σ φ)
  | p, _, .tt, _, _ | p, _, .eq _ _, _, _ | p, _, .wellFormed _, _, _ => by
    cases p <;> exact id
  | p, _, .not φ, h, σ => Polar.not (holds_of_holdsR (!p) φ h σ)
  | p, _, .and φ ψ, h, σ => by
    have h' : (φ.posModal p && ψ.posModal p) = true := h
    rw [Bool.and_eq_true] at h'
    exact Polar.and (holds_of_holdsR p φ h'.1 σ) (holds_of_holdsR p ψ h'.2 σ)
  | p, _, .imp φ ψ, h, σ => by
    have h' : (φ.posModal (!p) && ψ.posModal p) = true := h
    rw [Bool.and_eq_true] at h'
    exact Polar.imp (holds_of_holdsR (!p) φ h'.1 σ) (holds_of_holdsR p ψ h'.2 σ)
  | p, _, .upd m U φ, h, σ => Polar.afterT (U := U) fun τ => holds_of_holdsR p φ h τ
  | p, _, .modal m P κ φ, h, σ => by
    have h' : (p && φ.posModal p) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hp, hφ⟩ := h'
    subst hp
    intro H
    change ∀ o, ExecPM M (I.stateInv pay) σ P o →
      o.thenFM M (I.stateInv pay) κ m (holdsR M I pay · φ) at H
    show m.afterRunTR (holds · φ) (Prog.runFrames σ P κ)
    rcases Prog.execM_run M (I.stateInv pay) P σ with he | he
    · have H₁ := H _ he
      cases hr : Prog.run σ P with
      | error e =>
        rw [hr] at H₁
        rw [Prog.runFrames_error κ hr, afterRunTR_error]
        exact H₁
      | ok o =>
        rw [hr] at H₁
        rw [Prog.runFrames_ok κ hr]
        rcases Frames.execM_run M (I.stateInv pay) κ o.st with hf | hf
        · have H₂ := H₁ _ hf
          cases hk : Frames.run o.st κ with
          | error e =>
            rw [hk] at H₂
            exact (afterRunTR_error m _ e).2 H₂
          | ok o' =>
            rw [hk] at H₂
            exact (afterRunTR_ok m _ o'.st).2 (holds_of_holdsR true φ hφ o'.st H₂)
        · exact (H₁ _ hf).elim
    · exact (H _ he).elim
  | p, _, .havoc φ, h, σ =>
    Polar.forall fun _ => Polar.forall fun _ => Polar.forall fun _ => holds_of_holdsR p φ h _
  | p, _, .all _ _ φ, h, σ => Polar.forall fun _ => holds_of_holdsR p φ h _
  | p, _, .bind m _ t φ, h, σ => Polar.forall (α := t.TDenote C σ.H) fun v => holds_of_holdsR p φ h _
  | p, _, .anon _ φ, h, σ => Polar.forall fun _ => holds_of_holdsR p φ h _
  | p, _, .allocAll _ _ φ, h, σ => Polar.forall fun _ => holds_of_holdsR p φ h _
  | p, _, .grow φ, h, σ =>
    Polar.forall fun _ => Polar.forall fun _ => holds_of_holdsR p φ h _

end None

/-! ## The weakening theorem -/

/-- `ValidM` at a model that calls back is its `holdsR` in every state. -/
theorem validM_of_ne_none {M : CallerModel C} (hM : M ≠ .none) {ts : TransferSem C}
    {φ : Fml C []} : ValidM M ts φ ↔ ∀ σ : State C [], holdsR M ts.inv.fml ts.pay σ φ := by
  cases M with
  | none => exact absurd rfl hM
  | staticOnly | nonReentrant _ | any => exact Iff.rfl

/-- **The weakening theorem**: valid under a stronger attacker is valid
under a weaker one (`M ≤ M'`), for a formula whose modalities stand
positively. -/
theorem ValidM.weaken {M M' : CallerModel C} (hle : M.Le M') {ts : TransferSem C}
    {φ : Fml C []} (hφ : φ.posModal true = true) (h : ValidM M' ts φ) : ValidM M ts φ := by
  by_cases hM' : M' = .none
  · subst hM'
    cases hle with
    | refl | none => exact h
  · have h' := (validM_of_ne_none hM').1 h
    by_cases hM : M = .none
    · subst hM
      exact fun σ => holds_of_holdsR true φ hφ σ (h' σ)
    · exact (validM_of_ne_none hM).2 fun σ =>
        holdsR_mono (fun σ st nt sb => hle.allows _ σ st nt sb) true φ hφ σ (h' σ)

/-- Valid under today's callback reading is valid under every caller model. -/
theorem ValidM.of_validT {M : CallerModel C} {ts : TransferSem C} {φ : Fml C []}
    (hφ : φ.posModal true = true) (h : ValidT ts φ) : ValidM M ts φ :=
  ValidM.weaken (.any M) hφ (validM_any.2 h)

end Solidity

/-- info: 'Solidity.ValidM.weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.ValidM.weaken
/-- info: 'Solidity.validM_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.validM_any
/-- info: 'Solidity.Reentry.reachAny_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Reentry.reachAny_iff
