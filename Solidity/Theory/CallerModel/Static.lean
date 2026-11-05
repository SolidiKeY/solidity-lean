import Solidity.Calculus.CallerModelValid

/-!
# Callees that change nothing

A caller model *changes nothing* where `Q` holds when every resumption it
allows from a state whose storage satisfies `Q` leaves the storage, the
ledger and the balance as control left them (`CallerModel.InertAt`):
`staticOnly` everywhere, and `nonReentrant R` for an `R` that guards every
entry wherever its lock is held (`Reentry.inertAt`).  Under such a model,
with an invariant that holds everywhere, a `transfer` from a `Q` state has
one run, its deterministic one (`ExecSM.transfer_inert`), so a program
whose only callbacks are transfers (`Prog.inertSafe`), `Q` holding before
each (`Prog.LockedAt`), has one run, its typed run (`ExecPM.eq_run_inert`),
and a box over it holds where it holds deterministically
(`holdsR_box_inert`).  `Examples/Tactics/CallerModel.lean` reads its valid
sides so.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-- `M` allows only a callee that changes nothing, from a state whose
storage satisfies `Q`. -/
def CallerModel.InertAt (M : CallerModel C) (J : StateInv C) (Q : Storage C → Prop) : Prop :=
  ∀ {Γ : Ctx} (σ : State C Γ) st nt sb, Q σ.storage → M.Allows J σ st nt sb →
    st = σ.storage ∧ nt = σ.net ∧ sb = σ.selfBalance

/-- A callee calling back by `STATICCALL` changes nothing, from any state. -/
theorem CallerModel.inert_staticOnly (J : StateInv C) (Q : Storage C → Prop) :
    (CallerModel.staticOnly).InertAt J Q :=
  fun _ _ _ _ _ h => h

/-- With every entry guarded, a callee that finds the lock held reaches
nothing new: the lock lets no call through. -/
theorem Reentry.reach_eq {R : Reentry C} {J : StateInv C} (hR : ∀ f, R.guarded f = true)
    {g g' : State C []} (h : R.Reach J g g') (hh : R.held g.storage) : g' = g := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    have e := ih
    subst e
    obtain ⟨f, hf, -⟩ := hs
    rw [hR f] at hf
    rcases hf with hf | hf
    · cases hf
    · exact absurd hh hf

/-- With every entry guarded, `nonReentrant R` changes nothing where the lock
is held. -/
theorem Reentry.inertAt {R : Reentry C} {J : StateInv C} (hR : ∀ f, R.guarded f = true) :
    (CallerModel.nonReentrant R).InertAt J R.held := by
  intro Γ σ st nt sb hh h
  have e := Reentry.reach_eq hR h hh
  exact ⟨congrArg State.storage e, congrArg State.net e, congrArg State.selfBalance e⟩

/-- A transfer keeps the storage. -/
theorem TRun.transfer_storage {Γ : Ctx} {r a : Val C Γ .uint} {σ : State C Γ}
    {o₁ : Out C σ.H Γ} (h : TRun.transfer r a σ = .ok o₁) : o₁.st.storage = σ.storage := by
  unfold TRun.transfer at h
  cases hr : r.evalT σ with
  | error e => simp only [hr, bind, Except.bind] at h; cases h
  | ok addr =>
    cases ha : a.evalT σ with
    | error e => simp only [hr, ha, bind, Except.bind] at h; cases h
    | ok amt =>
      simp only [hr, ha, bind, Except.bind] at h
      split at h
      · cases h; rfl
      · cases h

/-! ## The runs -/

section Runs

variable {M : CallerModel C} {J : StateInv C}

/-- **A transfer under a model that changes nothing**, its invariant holding
everywhere: its deterministic run. -/
theorem ExecSM.transfer_inert {Q : Storage C → Prop} (hM : M.InertAt J Q)
    (hJ : ∀ x, J.holds x) {Γ : Ctx} {σ : State C Γ} {r a : Val C Γ .uint} {o : COut C σ.H Γ}
    (hQ : Q σ.storage) (h : ExecSM M J σ (.transfer r a) o) :
    o = .ofRes (TRun.transfer r a σ) := by
  cases h with
  | det _ => rfl
  | transferHalt _ he => rw [he]; rfl
  | transferViolated _ _ hv => exact absurd (hJ _) hv
  | transferResume _ ht _ _ hA =>
    obtain ⟨hs, hn, hb⟩ := hM _ _ _ _ (by rw [TRun.transfer_storage ht]; exact hQ) hA
    subst hs hn hb
    rw [ht]
    rfl

/-- A statement is a `transfer`. -/
def Stmt.isTransfer {Γ Γ' : Ctx} : Stmt C Γ Γ' → Bool
  | .transfer _ _ => true
  | _ => false

/-- `Q` holds of the storage before each transfer of `P`'s typed run from
`σ`. -/
def Prog.LockedAt (Q : Storage C → Prop) : {Γ Γ' : Ctx} → State C Γ → Prog C Γ Γ' → Prop
  | _, _, _, .nil => True
  | _, _, σ, .cons s P => (s.isTransfer = true → Q σ.storage) ∧
      ∀ o₁, s.run σ = .ok o₁ → Prog.LockedAt Q o₁.st P

/-- What holds of every storage holds before every transfer. -/
theorem Prog.lockedAt_true : {Γ Γ' : Ctx} → (σ : State C Γ) → (P : Prog C Γ Γ') →
    Prog.LockedAt (fun _ => True) σ P
  | _, _, _, .nil => trivial
  | _, _, _, .cons _ P => ⟨fun _ => trivial, fun o₁ _ => Prog.lockedAt_true o₁.st P⟩

/-- A program whose statements are transfers or call nobody back. -/
def Prog.inertSafe (pay : Bool) : {Γ Γ' : Ctx} → Prog C Γ Γ' → Bool
  | _, _, .nil => true
  | _, _, .cons s P => (s.isTransfer || !s.callsBack pay) && Prog.inertSafe pay P

/-- **A transfer or a statement that calls nobody back has one run** under a
model that changes nothing where `Q` holds, from such a state. -/
theorem Stmt.eq_run_inert {Q : Storage C → Prop} (hM : M.InertAt J Q) (hJ : ∀ x, J.holds x)
    {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (hs : (s.isTransfer || !s.callsBack J.pay) = true)
    {σ : State C Γ} (hQ : s.isTransfer = true → Q σ.storage)
    {o : COut C σ.H Γ'} (h : ExecSM M J σ s o) : o = .ofRes (s.run σ) := by
  cases hc : s.callsBack J.pay with
  | false => exact ExecS.eq_run (ExecSM.toExecS h) hc
  | true =>
    rw [hc] at hs
    cases s <;> simp only [Stmt.isTransfer, Bool.not_true, Bool.or_false,
      Bool.false_eq_true] at hs
    exact ExecSM.transfer_inert hM hJ (hQ rfl) h

/-- **A program whose only callbacks are transfers has one run** under a
model that changes nothing, its invariant holding everywhere. -/
theorem ExecPM.eq_run_inert {Q : Storage C → Prop} (hM : M.InertAt J Q) (hJ : ∀ x, J.holds x) :
    {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → Prog.inertSafe J.pay P = true →
      ∀ {σ : State C Γ} {o : COut C σ.H Γ'}, Prog.LockedAt Q σ P →
        ExecPM M J σ P o → o = .ofRes (Prog.run σ P)
  | _, _, .nil, _, _, _, _, h => by cases h; rfl
  | _, _, .cons s P, ht, σ, _, hL, h => by
    have ht' : ((s.isTransfer || !s.callsBack J.pay) && Prog.inertSafe J.pay P) = true := ht
    rw [Bool.and_eq_true] at ht'
    cases h with
    | @cons _ _ _ _ _ _ o₁ _ hs hP =>
      have e₁ := Stmt.eq_run_inert hM hJ s ht'.1 hL.1 hs
      have hs' : Stmt.run σ s = .ok o₁ := by
        revert e₁
        cases Stmt.run σ s with
        | error _ => exact fun e₁ => nomatch e₁
        | ok _ => intro e₁; cases e₁; rfl
      rw [Prog.run_cons_ok hs', ExecPM.eq_run_inert hM hJ P ht'.2 (hL.2 o₁ hs') hP,
        COut.map_ofRes]
      rfl
    | @halt _ _ _ _ _ _ e hs =>
      have e₁ : (COut.halt e : COut C σ.H _) = COut.ofRes (s.runR σ) :=
        Stmt.eq_run_inert hM hJ s ht'.1 hL.1 hs
      show _ = COut.ofRes (TRun.seq s.runR P.runR σ)
      unfold TRun.seq
      revert e₁
      cases s.runR σ with
      | error _ => intro e₁; cases e₁; rfl
      | ok _ => exact fun e₁ => nomatch e₁
    | violated hs =>
      have e₁ := Stmt.eq_run_inert hM hJ s ht'.1 hL.1 hs
      revert e₁
      cases Stmt.run σ s <;> exact fun e₁ => nomatch e₁

end Runs

/-! ## The reading -/

/-- **A box over such a program holds if it holds deterministically**, for
no frames after it and a postcondition read alike both ways. -/
theorem holdsR_box_inert {M : CallerModel C} {I : Invariant C} {pay : Bool}
    {Q : Storage C → Prop} (hM : M.InertAt (I.fml.stateInv pay) Q)
    (hI : ∀ x : State C [], holds x I.fml) {Γ Γ₁ : Ctx}
    {σ : State C Γ} {P : Prog C Γ Γ₁} (hP : Prog.inertSafe pay P = true)
    (hL : Prog.LockedAt Q σ P) {φ : Fml C Γ₁}
    (hφ : ∀ τ, holdsR M I.fml pay τ φ ↔ holds τ φ)
    (h : holds σ (.modal .box P .nil φ)) : holdsR M I.fml pay σ (.modal .box P .nil φ) := by
  intro o ho
  have e := ExecPM.eq_run_inert hM hI P hP hL ho
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
