import Solidity.Calculus.SoundKit
import Solidity.Semantics.CallbackCapture

/-!
# A payment's operands captured, with callbacks

`transfer_unfold_rightSndArgument`, `transfer_unfold_leftFstReceiver`,
`send_unfold_rightSndArgument`, `send_unfold_leftFstReceiver`: a payment
whose receiver or amount is not simple captures it into a fresh `uint`
first (`Calculus/Arms.lean`'s `transferStep`, `sendStep`).  The payment
calls back (`pay` set, or a value call's `full`), the capture does not:
each run of the payment with callbacks is one of the captured program's,
the fresh local popped (`Stmt.CapturesAs`, read by `ProvesC.capture`).
The payment reads its operands at the fresh local as it read them before
(`Val.evalT_up`), and what it books, the callee's `{havoc}` and the flag it
sets leave the local alone.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

namespace CapturePayments

/-- An outcome with a value local pushed on top. -/
abbrev pushOut {H : HTy} (v : PrimTy.uint.Denote) (x : Out C H Γ) : Out C H (.val .uint :: Γ) :=
  ⟨x.st.push (t := .val .uint) v, x.ext⟩

/-- A transfer that reads, at a pushed local, what another read without it
runs with callbacks as the other does, the local kept. -/
theorem transfer_push {J : StateInv C} (hp : J.pay = true) {r a : Val C Γ .uint}
    {r' a' : Val C (.val .uint :: Γ) .uint} {σ : State C Γ} {v : PrimTy.uint.Denote}
    (h : TRun.transfer r' a' (σ.push (t := .val .uint) v) =
      (TRun.transfer r a σ).map (pushOut v))
    {o : COut C σ.H Γ} (he : ExecS J σ (.transfer r a) o) :
    ExecS J (σ.push (t := .val .uint) v) (.transfer r' a') (o.map (pushOut v)) := by
  cases he with
  | det hf => exact absurd (hp.symm.trans hf) (by decide)
  | transferHalt hpay ht => exact .transferHalt hpay (by rw [h, ht]; rfl)
  | transferViolated hpay ht hj => exact .transferViolated hpay (by rw [h, ht]; rfl) hj
  | @transferResume _ _ _ _ o₁ _ _ hpay ht hj hk =>
    exact ExecS.transferResume (σ := σ.push (t := .val .uint) v) (o₁ := pushOut v o₁) hpay
      (by rw [h, ht]; rfl) hj hk

/-- `transfer_push` for a send. -/
theorem send_push {J : StateInv C} {full : Bool} (hp : (J.pay || full) = true)
    {pv : Idx Γ (.val .bool)} {r a : Val C Γ .uint}
    {r' a' : Val C (.val .uint :: Γ) .uint} {σ : State C Γ} {v : PrimTy.uint.Denote}
    (h : TRun.transfer r' a' (σ.push (t := .val .uint) v) =
      (TRun.transfer r a σ).map (pushOut v))
    {o : COut C σ.H Γ} (he : ExecS J σ (.send pv r a full) o) :
    ExecS J (σ.push (t := .val .uint) v) (.send pv.there r' a' full) (o.map (pushOut v)) := by
  cases he with
  | det hf => exact absurd (hp.symm.trans hf) (by decide)
  | sendHalt hpay ht => exact .sendHalt hpay (by rw [h, ht]; rfl)
  | sendFailed hpay ht => exact .sendFailed hpay (by rw [h, ht]; rfl)
  | sendViolated hpay ht hj => exact .sendViolated hpay (by rw [h, ht]; rfl) hj
  | @sendResume _ _ _ _ _ _ o₁ _ _ hpay ht hj hk =>
    exact ExecS.sendResume (σ := σ.push (t := .val .uint) v) (o₁ := pushOut v o₁) hpay
      (by rw [h, ht]; rfl) hj hk

/-- A capture `uint x = e; s'` of a statement `s` that halts where `e` does
and otherwise runs as `s'` at `e`'s value. -/
theorem capture_of {J : StateInv C} {s' : Stmt C (.val .uint :: Γ) (.val .uint :: Γ)}
    {e : Val C Γ .uint} {x : Var} {σ : State C Γ} {o : COut C σ.H Γ}
    (herr : ∀ err, e.evalT σ = .error err → o = .halt err)
    (hok : ∀ v, e.evalT σ = .ok v →
      ExecS J (σ.push (t := .val .uint) v) s' (o.map (pushOut v))) :
    ∃ o', ExecP J σ (.cons (.declLocal .uint x (some e)) (.cons s' .nil)) o' ∧
      o'.map (Out.drop (.push .refl)) = o := by
  cases hv : e.evalT σ with
  | error err =>
    have hr : (Stmt.declLocal .uint x (some e)).run σ = .error err := by
      show TRun.declLocal .uint (some e) σ = _; simp only [TRun.declLocal, hv]; rfl
    have hd := ExecS.det (J := J) (σ := σ) (s := Stmt.declLocal .uint x (some e)) rfl
    rw [hr] at hd
    exact ⟨.halt err, .halt hd, (herr err hv).symm⟩
  | ok v =>
    have hr : (Stmt.declLocal .uint x (some e)).run σ =
        .ok ⟨σ.push (t := .val .uint) v, List.prefix_refl _⟩ := by
      show TRun.declLocal .uint (some e) σ = _; simp only [TRun.declLocal, hv]; rfl
    have hd := ExecS.det (J := J) (σ := σ) (s := Stmt.declLocal .uint x (some e)) rfl
    rw [hr] at hd
    refine ⟨_, .cons hd (CallbackCapture.execP_single (hok v hv)), ?_⟩
    cases o <;> rfl

end CapturePayments

open CapturePayments

/-- **`transfer_unfold_rightSndArgument` with callbacks**: `r.transfer(nse)`
runs as `uint se = nse; r.transfer(se)`. -/
theorem Stmt.CapturesAs.transferAmt {m : Modality} {sadr : Simple C Γ .uint}
    {a : Val C Γ .uint} {x : Var} (hp : pay = true) :
    (Stmt.transfer (.simple sadr) a).CapturesAs pay m
      (.cons (.declLocal .uint x (some a))
        (.cons (.transfer (.simple sadr.up) (.simple (.local .here))) .nil)) (.push .refl) := by
  intro J hJ σ o he
  refine .inr (capture_of (fun err hv => ?_) (fun v hv => transfer_push (hJ.trans hp) ?_ he))
  · have ht : TRun.transfer (.simple sadr) a σ = .error err := by
      simp only [TRun.transfer, Val.evalT, hv]; rfl
    cases he with
    | det hf => exact absurd ((hJ.trans hp).symm.trans hf) (by decide)
    | transferHalt _ ht' => rw [ht] at ht'; cases ht'; rfl
    | transferViolated _ ht' => rw [ht] at ht'; cases ht'
    | transferResume _ ht' => rw [ht] at ht'; cases ht'
  · simp only [TRun.transfer, Val.evalT, Simple.evalT_up, hv]; rfl

/-- **`transfer_unfold_leftFstReceiver` with callbacks**: `nse.transfer(a)`
runs as `uint se = nse; se.transfer(a)`. -/
theorem Stmt.CapturesAs.transferRecv {m : Modality} {r a : Val C Γ .uint} {x : Var}
    (hp : pay = true) :
    (Stmt.transfer r a).CapturesAs pay m
      (.cons (.declLocal .uint x (some r))
        (.cons (.transfer (.simple (.local .here)) a.up) .nil)) (.push .refl) := by
  intro J hJ σ o he
  refine .inr (capture_of (fun err hv => ?_) (fun v hv => transfer_push (hJ.trans hp) ?_ he))
  · have ht : TRun.transfer r a σ = .error err := by
      simp only [TRun.transfer, hv]; rfl
    cases he with
    | det hf => exact absurd ((hJ.trans hp).symm.trans hf) (by decide)
    | transferHalt _ ht' => rw [ht] at ht'; cases ht'; rfl
    | transferViolated _ ht' => rw [ht] at ht'; cases ht'
    | transferResume _ ht' => rw [ht] at ht'; cases ht'
  · simp only [TRun.transfer, Val.evalT_up, hv]
    cases Val.evalT σ a <;> rfl

/-- **`send_unfold_rightSndArgument` with callbacks.** -/
theorem Stmt.CapturesAs.sendAmt {m : Modality} {pv : Idx Γ (.val .bool)} {full : Bool}
    {sadr : Simple C Γ .uint} {a : Val C Γ .uint} {x : Var} (hp : (pay || full) = true) :
    (Stmt.send pv (.simple sadr) a full).CapturesAs pay m
      (.cons (.declLocal .uint x (some a))
        (.cons (.send pv.there (.simple sadr.up) (.simple (.local .here)) full) .nil))
      (.push .refl) := by
  intro J hJ σ o he
  have hp' : (J.pay || full) = true := by rw [hJ]; exact hp
  refine .inr (capture_of (fun err hv => ?_) (fun v hv => send_push hp' ?_ he))
  · have ht : TRun.transfer (.simple sadr) a σ = .error err := by
      simp only [TRun.transfer, Val.evalT, hv]; rfl
    cases he with
    | det hf => exact absurd (hp'.symm.trans hf) (by decide)
    | sendHalt _ ht' => rw [ht] at ht'; cases ht'; rfl
    | sendFailed _ ht' => rw [ht] at ht'; cases ht'
    | sendViolated _ ht' => rw [ht] at ht'; cases ht'
    | sendResume _ ht' => rw [ht] at ht'; cases ht'
  · simp only [TRun.transfer, Val.evalT, Simple.evalT_up, hv]; rfl

/-- **`send_unfold_leftFstReceiver` with callbacks.** -/
theorem Stmt.CapturesAs.sendRecv {m : Modality} {pv : Idx Γ (.val .bool)} {full : Bool}
    {r a : Val C Γ .uint} {x : Var} (hp : (pay || full) = true) :
    (Stmt.send pv r a full).CapturesAs pay m
      (.cons (.declLocal .uint x (some r))
        (.cons (.send pv.there (.simple (.local .here)) a.up full) .nil)) (.push .refl) := by
  intro J hJ σ o he
  have hp' : (J.pay || full) = true := by rw [hJ]; exact hp
  refine .inr (capture_of (fun err hv => ?_) (fun v hv => send_push hp' ?_ he))
  · have ht : TRun.transfer r a σ = .error err := by
      simp only [TRun.transfer, hv]; rfl
    cases he with
    | det hf => exact absurd (hp'.symm.trans hf) (by decide)
    | sendHalt _ ht' => rw [ht] at ht'; cases ht'; rfl
    | sendFailed _ ht' => rw [ht] at ht'; cases ht'
    | sendViolated _ ht' => rw [ht] at ht'; cases ht'
    | sendResume _ ht' => rw [ht] at ht'; cases ht'
  · simp only [TRun.transfer, Val.evalT_up, hv]
    cases Val.evalT σ a <;> rfl

end Solidity
