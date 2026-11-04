import Solidity.Calculus.CallerModelValid

/-!
# Callees that change nothing

A caller model *changes nothing* when every resumption it allows leaves the
storage, the ledger and the balance as control left them
(`CallerModel.Inert`): `staticOnly`, and `nonReentrant R` for an `R` with
no unguarded entry (`Reentry.inert`).  Under such a model, with an
invariant that holds everywhere, a `transfer`'s only runs are its
deterministic one (`ExecSM.transfer_inert`), so a program whose only
callbacks are transfers (`Prog.inertSafe`) has one run, its typed run
(`ExecPM.eq_run_inert`): `Fml.Valid` decides a modality over it
(`holdsR_modal_inert`).  The separating examples
(`Examples/Tactics/CallerModel.lean`) read their valid sides so.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-- `M` allows only a callee that changes nothing. -/
def CallerModel.Inert (M : CallerModel C) (J : StateInv C) : Prop :=
  ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, M.Allows J σ st nt sb →
    st = σ.storage ∧ nt = σ.net ∧ sb = σ.selfBalance

theorem CallerModel.inert_staticOnly (J : StateInv C) : (CallerModel.staticOnly).Inert J :=
  fun _ _ _ _ h => h

/-- With no unguarded entry, a callee re-entering only into unguarded
entries reaches nothing new. -/
theorem Reentry.reach_eq {R : Reentry C} {J : StateInv C} (hR : ∀ f, R.guarded f = true)
    {g g' : State C []} (h : R.Reach J g g') : g' = g := by
  induction h with
  | refl => rfl
  | tail _ hs _ =>
    obtain ⟨f, hf, -⟩ := hs
    rw [hR f] at hf
    cases hf

theorem Reentry.inert {R : Reentry C} {J : StateInv C} (hR : ∀ f, R.guarded f = true) :
    (CallerModel.nonReentrant R).Inert J := by
  intro Γ σ st nt sb h
  have e := Reentry.reach_eq hR h
  exact ⟨congrArg State.storage e, congrArg State.net e, congrArg State.selfBalance e⟩

/-! ## The runs -/

section Runs

variable {M : CallerModel C} {J : StateInv C}

/-- **A transfer under a model that changes nothing**, its invariant holding
everywhere: its deterministic run. -/
theorem ExecSM.transfer_inert (hM : M.Inert J) (hJ : ∀ x, J.holds x) {Γ : Ctx}
    {σ : State C Γ} {r a : Val C Γ .uint} {o : COut C σ.H Γ}
    (h : ExecSM M J σ (.transfer r a) o) : o = .ofRes (TRun.transfer r a σ) := by
  cases h with
  | det _ => rfl
  | transferHalt _ he => rw [he]; rfl
  | transferViolated _ _ hv => exact absurd (hJ _) hv
  | transferResume _ ht _ _ hA =>
    obtain ⟨hs, hn, hb⟩ := hM _ _ _ _ hA
    subst hs hn hb
    rw [ht]
    rfl

/-- A statement is a `transfer`. -/
def Stmt.isTransfer {Γ Γ' : Ctx} : Stmt C Γ Γ' → Bool
  | .transfer _ _ => true
  | _ => false

/-- A program whose statements are transfers or call nobody back. -/
def Prog.inertSafe (pay : Bool) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, .nil => true
  | _, _, .cons s P => (s.isTransfer || !s.callsBack pay) && Prog.inertSafe pay P

theorem Stmt.eq_run_inert (hM : M.Inert J) (hJ : ∀ x, J.holds x) {Γ Γ' : Ctx}
    (s : Stmt C Γ Γ') (hs : (s.isTransfer || !s.callsBack J.pay) = true) {σ : State C Γ}
    {o : COut C σ.H Γ'} (h : ExecSM M J σ s o) : o = .ofRes (s.run σ) := by
  cases hc : s.callsBack J.pay with
  | false => exact ExecS.eq_run (ExecSM.toExecS h) hc
  | true =>
    rw [hc] at hs
    cases s <;> simp only [Stmt.isTransfer, Bool.not_true, Bool.or_false,
      Bool.false_eq_true] at hs
    exact ExecSM.transfer_inert hM hJ h

/-- **A program whose only callbacks are transfers has one run** under a
model that changes nothing, its invariant holding everywhere. -/
theorem ExecPM.eq_run_inert (hM : M.Inert J) (hJ : ∀ x, J.holds x) : {Γ Γ' : Ctx} →
    (P : Prog C Γ Γ') → Prog.inertSafe J.pay P = true → ∀ {σ : State C Γ} {o : COut C σ.H Γ'},
      ExecPM M J σ P o → o = .ofRes (Prog.run σ P)
  | _, _, .nil, _, _, _, h => by cases h; rfl
  | _, _, .cons s P, ht, σ, _, h => by
    have ht' : ((s.isTransfer || !s.callsBack J.pay) && Prog.inertSafe J.pay P) = true := ht
    rw [Bool.and_eq_true] at ht'
    cases h with
    | @cons _ _ _ _ _ _ o₁ _ hs hP =>
      have e₁ := Stmt.eq_run_inert hM hJ s ht'.1 hs
      have hs' : Stmt.run σ s = .ok o₁ := by
        revert e₁
        cases Stmt.run σ s with
        | error _ => exact fun e₁ => nomatch e₁
        | ok _ => intro e₁; cases e₁; rfl
      rw [Prog.run_cons_ok hs', ExecPM.eq_run_inert hM hJ P ht'.2 hP, COut.map_ofRes]
      rfl
    | @halt _ _ _ _ _ _ e hs =>
      have e₁ : (COut.halt e : COut C σ.H _) = COut.ofRes (s.runR σ) :=
        Stmt.eq_run_inert hM hJ s ht'.1 hs
      show _ = COut.ofRes (TRun.seq s.runR P.runR σ)
      unfold TRun.seq
      revert e₁
      cases s.runR σ with
      | error _ => intro e₁; cases e₁; rfl
      | ok _ => exact fun e₁ => nomatch e₁
    | violated hs =>
      have e₁ := Stmt.eq_run_inert hM hJ s ht'.1 hs
      revert e₁
      cases Stmt.run σ s <;> exact fun e₁ => nomatch e₁

end Runs

/-! ## The reading -/

/-- **A box over such a program is its deterministic reading**, for a
postcondition that calls nobody back and no frames after it. -/
theorem holdsR_box_inert {M : CallerModel C} {I : Invariant C} {pay : Bool}
    (hM : M.Inert (I.fml.stateInv pay)) (hI : ∀ x : State C [], holds x I.fml) {Γ Γ₁ : Ctx}
    {σ : State C Γ} {P : Prog C Γ Γ₁} (hP : Prog.inertSafe pay P = true) {φ : Fml C Γ₁}
    (hφ : ∀ τ, holdsR M I.fml pay τ φ ↔ holds τ φ)
    (h : holds σ (.modal .box P .nil φ)) : holdsR M I.fml pay σ (.modal .box P .nil φ) := by
  intro o ho
  have e := ExecPM.eq_run_inert hM hI P hP ho
  subst e
  change Modality.box.afterRunTR (holds · φ) (Prog.runFrames σ P .nil) at h
  cases hr : Prog.run σ P with
  | error e =>
    rw [Prog.runFrames_error .nil hr, afterRunTR_error] at h
    exact h
  | ok o =>
    rw [Prog.runFrames_ok .nil hr] at h
    intro o' hf
    cases hf
    exact (hφ o.st).2 ((afterRunTR_ok Modality.box (holds · φ) o.st).1 h)

end Solidity
