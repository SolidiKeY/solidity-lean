import Solidity.Calculus.CallbackSound.Rules
import Solidity.Calculus.PaymentWitness

/-!
# Payment diamonds with normality

The existing formula `¬ [r.transfer(a);] false` supplies acceptance without
an oracle atom. Both callback obligations remain separate. The unconditional
SolKey transfer diamond remains outside `Taclet.toStep`.
-/

namespace Solidity

variable {C : Contract} {I : Fml C []} {pay : Bool} {Γ : Ctx}

/-- Refusal makes the simple-transfer box with false postcondition true:
only revert is possible, in either payment reading. -/
theorem holdsC_transfer_refused_false (σ : State C Γ) (r a : Simple C Γ .uint)
    (refused : σ.canPay (r.evalT σ) (a.evalT σ) = false) :
    holdsC I pay σ (.modal .box (.cons (.transfer (.simple r) (.simple a)) .nil) .nil .ff) := by
  have run : TRun.transfer (.simple r) (.simple a) σ = .error .revert := by
    rw [PaymentWitness.transfer_run, refused]
    rfl
  refine holdsC_cons fun o he => ?_
  cases he with
  | det _ =>
    change COut.thenF _ _ _ _ (COut.ofRes (TRun.transfer _ _ σ))
    rw [run]
    exact ⟨trivial, by decide⟩
  | transferHalt _ h =>
    rw [run] at h
    cases h
    exact ⟨trivial, by decide⟩
  | transferViolated _ h _ => rw [run] at h; cases h
  | transferResume _ h _ _ => rw [run] at h; cases h

/-- Normality is an existing modal formula, not a new acceptance atom. -/
theorem holdsC_transfer_normal_accepted (σ : State C Γ) (r a : Simple C Γ .uint)
    (normal : holdsC I pay σ (.not
      (.modal .box (.cons (.transfer (.simple r) (.simple a)) .nil) .nil .ff))) :
    σ.canPay (r.evalT σ) (a.evalT σ) = true := by
  cases h : σ.canPay (r.evalT σ) (a.evalT σ) with
  | false => exact (normal (holdsC_transfer_refused_false σ r a h)).elim
  | true => rfl

/-- The transfer diamond with callbacks needs normality as well as both
SolKey callback obligations. Refusal is never silently booked. -/
theorem holdsC_transferCbDiamond {Γ₁ Γ₀ : Ctx} {σ : State C Γ}
    {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (hI : I.FO = true) (hT : I.hasTransfer = false) (r a : Simple C Γ .uint)
    (normal : holdsC I pay σ (.not
      (.modal .box (.cons (.transfer (.simple r) (.simple a)) .nil) .nil .ff)))
    (exit : holdsC I pay σ (.upd .diamond (Upd.nil.snoc (UpdElem.payTo r a)) (Fml.closedAt I)))
    (resume : holdsC I pay σ (.upd .diamond (Upd.nil.snoc (UpdElem.payTo r a))
      (.havoc (.imp (Fml.closedAt I) (Fml.modalK .diamond ω κ φ))))) :
    holdsC I pay σ (.modal .diamond (.cons (.transfer (.simple r) (.simple a)) ω) κ φ) := by
  have accepted : σ.canPay (r.evalT σ) (a.evalT σ) = true :=
    holdsC_transfer_normal_accepted σ r a normal
  have run : TRun.transfer (.simple r) (.simple a) σ =
      .ok ⟨σ.pay (r.evalT σ) (a.evalT σ).1, List.prefix_refl _⟩ := by
    rw [PaymentWitness.transfer_run, accepted]
    rfl
  refine holdsC_cons fun o he => ?_
  cases he with
  | det _ =>
    change COut.thenF _ _ _ _ (COut.ofRes (TRun.transfer _ _ σ))
    rw [run]
    have landed : (Upd.nil.snoc (UpdElem.payTo r a)).Lands σ
        (Upd.lands_of_applyP (transfer_booking r a run)).choose
        (σ.pay (r.evalT σ) (a.evalT σ).1) :=
      (Upd.lands_of_applyP (transfer_booking r a run)).choose_spec
    have hj : (I.stateInv pay).at (σ.pay (r.evalT σ) (a.evalT σ).1) :=
      (holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands exit landed)
    exact COut.after_seq (holdsC_modalK _ ω κ φ
      (Upd.afterT.of_lands resume landed _ _ _ ((holdsC_closedAt_iff hI hT _).2 hj)))
  | transferHalt _ h => rw [run] at h; cases h
  | transferViolated _ h hn =>
    exact (hn ((holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands exit
      (Upd.lands_of_applyP (transfer_booking r a h)).choose_spec))).elim
  | transferResume _ h _ hj =>
    exact COut.after_seq (holdsC_modalK _ ω κ φ
      (Upd.afterT.of_lands resume (Upd.lands_of_applyP (transfer_booking r a h)).choose_spec _ _ _
        ((holdsC_closedAt_iff hI hT _).2 hj)))

/-- Without payment callbacks, normality and the booked continuation suffice;
there is no havoc and no callback exit obligation. -/
theorem holdsC_transferDetDiamond {Γ₁ Γ₀ : Ctx} {σ : State C Γ}
    {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (hp : pay = false) (r a : Simple C Γ .uint)
    (normal : holdsC I pay σ (.not
      (.modal .box (.cons (.transfer (.simple r) (.simple a)) .nil) .nil .ff)))
    (rest : holdsC I pay σ (.upd .diamond (Upd.nil.snoc (UpdElem.payTo r a))
      (Fml.modalK .diamond ω κ φ))) :
    holdsC I pay σ (.modal .diamond (.cons (.transfer (.simple r) (.simple a)) ω) κ φ) := by
  have accepted : σ.canPay (r.evalT σ) (a.evalT σ) = true :=
    holdsC_transfer_normal_accepted σ r a normal
  have run : TRun.transfer (.simple r) (.simple a) σ =
      .ok ⟨σ.pay (r.evalT σ) (a.evalT σ).1, List.prefix_refl _⟩ := by
    rw [PaymentWitness.transfer_run, accepted]
    rfl
  refine holdsC_cons fun o he => ?_
  rw [ExecS.detIn_inv he (by change pay = false; exact hp)]
  change COut.thenF _ _ _ _ (COut.ofRes (TRun.transfer _ _ σ))
  rw [run]
  exact COut.after_seq (holdsC_modalK _ ω κ φ
    (Upd.afterT.of_lands rest (Upd.lands_of_applyP (transfer_booking r a run)).choose_spec))

#print axioms holdsC_transfer_normal_accepted
#print axioms holdsC_transferCbDiamond
#print axioms holdsC_transferDetDiamond

end Solidity
