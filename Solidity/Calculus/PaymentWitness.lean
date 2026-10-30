import Solidity.Calculus.CallbackHolds

/-!
# Payment witnesses at the diamond boundary

The SolKey transfer diamond needs additional fundedness/acceptance evidence in
this runtime. These semantic rules retain that evidence rather than replacing
`transferDiamond` by an unconditional booking. Callback outcomes are universal:
a positive witness must cover every invariant-preserving resumption.
-/

namespace Solidity.PaymentWitness

variable {C : Contract} {Γ : Ctx}

/-- Both simple operands evaluate, and the recipient and live balance decide
whether a transfer returns normally. -/
theorem transfer_run (σ : State C Γ) (r a : Simple C Γ .uint) :
    TRun.transfer (.simple r) (.simple a) σ =
      if σ.canPay (r.evalT σ) (a.evalT σ) then
        .ok ⟨σ.pay (r.evalT σ) (a.evalT σ).1, List.prefix_refl _⟩
      else .error .revert := by
  rfl

/-- Exact deterministic diamond rule: booking alone is insufficient. -/
theorem transferNoCallbackDiamond (σ : State C Γ) (r a : Simple C Γ .uint)
    (post : State C Γ → Prop) :
    Modality.diamond.afterRunTR (fun o => post o.st)
      (TRun.transfer (.simple r) (.simple a) σ) ↔
      σ.canPay (r.evalT σ) (a.evalT σ) = true ∧
        post (σ.pay (r.evalT σ) (a.evalT σ).1) := by
  rw [transfer_run]
  cases σ.canPay (r.evalT σ) (a.evalT σ) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Modality.afterRunTR,
      Modality.onTHalt, reduceCtorEq, false_and]
  | true =>
    simp only [↓reduceIte, Modality.afterRunTR, true_and]
    exact and_iff_left (by intro h; cases h)

/-- A send always returns for simple operands, including refusal. The `full`
flag belongs to callback selection, not the deterministic payment operation. -/
theorem send_run (σ : State C Γ) (pv : Idx Γ (.val .bool))
    (r a : Simple C Γ .uint) :
    TRun.send pv (.simple r) (.simple a) σ =
      .ok (sendT σ pv (r.evalT σ) (a.evalT σ)) := by
  rfl

/-- Exact deterministic send diamond, preserving the false return on refusal. -/
theorem sendNoCallbackDiamond (σ : State C Γ) (pv : Idx Γ (.val .bool))
    (r a : Simple C Γ .uint) (post : State C Γ → Prop) :
    Modality.diamond.afterRunTR (fun o => post o.st)
      (TRun.send pv (.simple r) (.simple a) σ) ↔
      post (sendT σ pv (r.evalT σ) (a.evalT σ)).st := by
  rw [send_run]
  exact and_iff_left (by intro h; cases h)

/-- A refused transfer is a callback countercontrol too: a callback cannot
repair a payment that never left the caller. -/
theorem transfer_refused (J : StateInv C) (hp : J.pay = true)
    (σ : State C Γ) (r a : Simple C Γ .uint)
    (h : σ.canPay (r.evalT σ) (a.evalT σ) = false) :
    ExecS J σ (.transfer (.simple r) (.simple a)) (.halt .revert) := by
  apply ExecS.transferHalt hp
  rw [transfer_run, h]
  rfl

/-- Witness form of SolKey's callback diamond: acceptance, invariant on exit,
and the postcondition after every allowed callback. No failure is discarded. -/
theorem transferWithCallbackDiamond (J : StateInv C) (hp : J.pay = true)
    (σ : State C Γ) (r a : Simple C Γ .uint) (post : State C Γ → Prop)
    (accepted : σ.canPay (r.evalT σ) (a.evalT σ) = true)
    (exit : J.at (σ.pay (r.evalT σ) (a.evalT σ).1))
    (resume : ∀ st nt sb,
      J.at ((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb) →
      post ((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb)) :
    ∀ o, ExecS J σ (.transfer (.simple r) (.simple a)) o →
      o.after .diamond post := by
  intro o he
  have run : TRun.transfer (.simple r) (.simple a) σ =
      .ok ⟨σ.pay (r.evalT σ) (a.evalT σ).1, List.prefix_refl _⟩ := by
    rw [transfer_run, accepted]
    rfl
  cases he with
  | det h => simp only [Stmt.forksIn, hp, Bool.true_eq_false] at h
  | transferHalt _ h => rw [run] at h; cases h
  | transferViolated _ h hn =>
    rw [run] at h
    cases h
    exact (hn exit).elim
  | transferResume _ h _ hj =>
    rw [run] at h
    cases h
    exact resume _ _ _ hj

/-- The callback transfer witness is exact: a diamond cannot hide refusal,
a broken exit invariant, or an invariant-preserving bad resumption. -/
theorem transferWithCallbackDiamond_iff (J : StateInv C) (hp : J.pay = true)
    (σ : State C Γ) (r a : Simple C Γ .uint) (post : State C Γ → Prop) :
    (∀ o, ExecS J σ (.transfer (.simple r) (.simple a)) o → o.after .diamond post) ↔
      σ.canPay (r.evalT σ) (a.evalT σ) = true ∧
      J.at (σ.pay (r.evalT σ) (a.evalT σ).1) ∧
      ∀ st nt sb, J.at ((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb) →
        post ((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb) := by
  constructor
  · intro h
    have accepted : σ.canPay (r.evalT σ) (a.evalT σ) = true := by
      cases hc : σ.canPay (r.evalT σ) (a.evalT σ) with
      | false =>
        have bad : Modality.diamond.onTHalt .revert :=
          (h _ (transfer_refused J hp σ r a hc)).1
        cases bad
      | true => rfl
    have run : TRun.transfer (.simple r) (.simple a) σ =
        .ok ⟨σ.pay (r.evalT σ) (a.evalT σ).1, List.prefix_refl _⟩ := by
      rw [transfer_run, accepted]
      rfl
    have exit : J.at (σ.pay (r.evalT σ) (a.evalT σ).1) := by
      classical
      apply Classical.byContradiction
      intro hn
      exact h _ (.transferViolated hp run hn)
    exact ⟨accepted, exit, fun _ _ _ hj => h _ (.transferResume hp run exit hj)⟩
  · rintro ⟨accepted, exit, resume⟩
    exact transferWithCallbackDiamond J hp σ r a post accepted exit resume

/-- Callback send diamond: success and failure continuations are both required,
even when the deterministic oracle accepts. Full-gas sends fork under either
payment option. -/
theorem sendWithCallbackDiamond (J : StateInv C) (full : Bool)
    (hp : (J.pay || full) = true) (σ : State C Γ)
    (pv : Idx Γ (.val .bool)) (r a : Simple C Γ .uint) (post : State C Γ → Prop)
    (exit : ∀ paid, TRun.transfer (.simple r) (.simple a) σ = .ok paid → J.at paid.st)
    (succeeded : ∀ paid st nt sb,
      TRun.transfer (.simple r) (.simple a) σ = .ok paid →
      J.at (paid.st.havoc st nt sb) → post ((paid.st.havoc st nt sb).setLocal pv (true : Bool)))
    (failed : post (σ.setLocal pv (false : Bool))) :
    ∀ o, ExecS J σ (.send pv (.simple r) (.simple a) full) o →
      o.after .diamond post := by
  intro o he
  cases he with
  | det h => simp only [Stmt.forksIn, hp, Bool.true_eq_false] at h
  | sendHalt _ h => rw [send_run] at h; cases h
  | sendFailed _ _ => exact failed
  | sendRefused _ _ => exact failed
  | sendViolated _ h hn => exact (hn (exit _ h)).elim
  | sendResume _ h _ hj => exact succeeded _ _ _ _ h hj

#print axioms transferNoCallbackDiamond
#print axioms sendNoCallbackDiamond
#print axioms transferWithCallbackDiamond
#print axioms transferWithCallbackDiamond_iff
#print axioms sendWithCallbackDiamond

end Solidity.PaymentWitness
