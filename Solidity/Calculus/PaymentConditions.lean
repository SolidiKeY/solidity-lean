import Solidity.Calculus.PaymentWitness
import Solidity.Semantics.RunFrame

/-!
# Exact payment conditions under the unchanged model

Missing oracle entries accept, as do explicit successful responses. Funding is
independent. Callback sends retain a failure outcome even after acceptance;
callback transfers retain their existing, different outcome relation.
-/
namespace Solidity.PaymentConditions
open Semantics PaymentWitness
variable {C : Contract} {Γ : Ctx}

/-- The actual recipient response policy; absence is acceptance, not refusal. -/
def RecipientAccepts (σ : State C Γ) (addr amt : PrimTy.uint.Denote) : Prop :=
  (match lookupBy (sendKey addr amt) σ.tx.ext with
    | none | some (.ok _) => true
    | some _ => false) = true

/-- Exact oracle alternatives. A missing entry is accepted by this model;
this fact alone certifies neither deployed code nor receive dispatch. -/
theorem recipient_iff (σ : State C Γ) (addr amt : PrimTy.uint.Denote) :
    RecipientAccepts σ addr amt ↔
      lookupBy (sendKey addr amt) σ.tx.ext = none ∨
        ∃ data, lookupBy (sendKey addr amt) σ.tx.ext = some (.ok data) := by
  unfold RecipientAccepts
  cases hlookup : lookupBy (sendKey addr amt) σ.tx.ext with
  | none => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | some reply =>
    cases reply with
    | ok data => exact ⟨fun _ => Or.inr ⟨data, rfl⟩, fun _ => rfl⟩
    | error reason =>
      constructor
      · intro bad; cases bad
      · rintro (bad | ⟨data, bad⟩) <;> cases bad
    | panic code =>
      constructor
      · intro bad; cases bad
      · rintro (bad | ⟨data, bad⟩) <;> cases bad
    | other data =>
      constructor
      · intro bad; cases bad
      · rintro (bad | ⟨data, bad⟩) <;> cases bad

/-- Necessary and sufficient, with both independent conditions explicit. -/
theorem canPay_iff (σ : State C Γ) (addr amt : PrimTy.uint.Denote) :
    σ.canPay addr amt = true ↔ amt.1 ≤ σ.selfBalance.1 ∧ RecipientAccepts σ addr amt := by
  simp only [State.canPay, Bool.and_eq_true, decide_eq_true_eq, RecipientAccepts]
  rfl

/-- The deterministic success condition exposes funding, recipient and post-state. -/
theorem transfer_success_iff (σ : State C Γ) (r a : Simple C Γ .uint)
    (post : State C Γ → Prop) :
    Modality.diamond.afterRunTR (fun o => post o.st)
      (TRun.transfer (.simple r) (.simple a) σ) ↔
      ((a.evalT σ).1 ≤ σ.selfBalance.1 ∧ RecipientAccepts σ (r.evalT σ) (a.evalT σ)) ∧
        post (σ.pay (r.evalT σ) (a.evalT σ).1) := by
  rw [transferNoCallbackDiamond, canPay_iff]

/-- Exact callback transfer conditions with funding and response separated. -/
theorem transfer_callback_conditions_iff (J : StateInv C) (hp : J.pay = true)
    (σ : State C Γ) (r a : Simple C Γ .uint) (post : State C Γ → Prop) :
    (∀ o, ExecS J σ (.transfer (.simple r) (.simple a)) o → o.after .diamond post) ↔
      ((a.evalT σ).1 ≤ σ.selfBalance.1 ∧ RecipientAccepts σ (r.evalT σ) (a.evalT σ)) ∧
      J.at (σ.pay (r.evalT σ) (a.evalT σ).1) ∧
      ∀ st nt sb, J.at ((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb) →
        post ((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb) := by
  rw [transferWithCallbackDiamond_iff J hp, canPay_iff]

/-- Refusal includes insufficient funds and every explicit unsuccessful response. -/
theorem transfer_failure_iff (σ : State C Γ) (r a : Simple C Γ .uint) :
    TRun.transfer (.simple r) (.simple a) σ = .error .revert ↔
      ¬ (a.evalT σ).1 ≤ σ.selfBalance.1 ∨ ¬ RecipientAccepts σ (r.evalT σ) (a.evalT σ) := by
  classical
  rw [transfer_run]
  cases h : σ.canPay (r.evalT σ) (a.evalT σ) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, true_iff]
    by_cases hf : (a.evalT σ).1 ≤ σ.selfBalance.1
    · exact Or.inr fun hr => by
        have bad : σ.canPay (r.evalT σ) (a.evalT σ) = true :=
          (canPay_iff σ (r.evalT σ) (a.evalT σ)).2 ⟨hf, hr⟩
        rw [h] at bad
        cases bad
    · exact Or.inl hf
  | true =>
    have good : (a.evalT σ).1 ≤ σ.selfBalance.1 ∧
        RecipientAccepts σ (r.evalT σ) (a.evalT σ) :=
      (canPay_iff σ (r.evalT σ) (a.evalT σ)).1 h
    simp only [↓reduceIte, reduceCtorEq, false_iff]
    intro bad
    exact bad.elim (fun hn => hn good.1) (fun hn => hn good.2)

/-- Refusal changes exactly the send-result local; no balance, ledger or frame effect. -/
theorem send_refused_run (σ : State C Γ) (pv : Idx Γ (.val .bool))
    (r a : Simple C Γ .uint) (h : σ.canPay (r.evalT σ) (a.evalT σ) = false) :
    TRun.send pv (.simple r) (.simple a) σ =
      .ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩ := by
  rw [send_run]
  unfold sendT
  rw [h]
  rfl

/-- Accepted sends book precisely the payment and set the result true. -/
theorem send_accepted_run (σ : State C Γ) (pv : Idx Γ (.val .bool))
    (r a : Simple C Γ .uint) (h : σ.canPay (r.evalT σ) (a.evalT σ) = true) :
    TRun.send pv (.simple r) (.simple a) σ =
      .ok ⟨(σ.pay (r.evalT σ) (a.evalT σ).1).setLocal pv (true : Bool), List.prefix_refl _⟩ := by
  rw [send_run]
  unfold sendT
  rw [h]
  rfl

/-- The deterministic returned Boolean is true exactly under the two success
conditions. This is not a theorem that every callback outcome succeeds. -/
theorem send_flag_iff (σ : State C Γ) (pv : Idx Γ (.val .bool))
    (addr amt : PrimTy.uint.Denote) :
    TEnv.get pv (sendT σ pv addr amt).st.env = true ↔
      amt.1 ≤ σ.selfBalance.1 ∧ RecipientAccepts σ addr amt := by
  change TEnv.get pv (TEnv.set pv (σ.canPay addr amt) σ.env) = true ↔ _
  rw [TEnv.get_set]
  exact canPay_iff σ addr amt

/-- Every callback-enabled simple send admits failure, even when accepted. -/
theorem send_failure_outcome (J : StateInv C) (full : Bool)
    (hp : (J.pay || full) = true) (σ : State C Γ)
    (pv : Idx Γ (.val .bool)) (r a : Simple C Γ .uint) :
    ExecS J σ (.send pv (.simple r) (.simple a) full)
      (.ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩) := by
  cases h : σ.canPay (r.evalT σ) (a.evalT σ) with
  | false => exact .sendRefused hp (send_refused_run σ pv r a h)
  | true =>
    apply ExecS.sendFailed hp
    rw [transfer_run, h]
    rfl

/-- A refused simple callback send has precisely one outcome, not a havoc. -/
theorem send_refused_outcome_iff (J : StateInv C) (full : Bool)
    (hp : (J.pay || full) = true) (σ : State C Γ)
    (pv : Idx Γ (.val .bool)) (r a : Simple C Γ .uint)
    (refused : σ.canPay (r.evalT σ) (a.evalT σ) = false) (o : COut C σ.H Γ) :
    ExecS J σ (.send pv (.simple r) (.simple a) full) o ↔
      o = .ok ⟨σ.setLocal pv (false : Bool), List.prefix_refl _⟩ := by
  constructor
  · intro he
    cases he with
    | det hn => simp only [Stmt.forksIn, hp, Bool.true_eq_false] at hn
    | sendHalt _ run => rw [send_run] at run; cases run
    | sendFailed _ run => rw [transfer_run, refused] at run <;> cases run
    | sendRefused _ _ => rfl
    | sendViolated _ run _ => rw [transfer_run, refused] at run <;> cases run
    | sendResume _ run _ _ => rw [transfer_run, refused] at run <;> cases run
  · intro eq
    rw [eq]
    exact .sendRefused hp (send_refused_run σ pv r a refused)

/-- Exact nonforking send reading. In particular full-gas calls cannot satisfy
this premise, even under the noCallback stipend option. -/
theorem send_deterministic_iff (J : StateInv C) (full : Bool)
    (hp : (J.pay || full) = false) (σ : State C Γ)
    (pv : Idx Γ (.val .bool)) (r a : Simple C Γ .uint) (post : State C Γ → Prop) :
    (∀ o, ExecS J σ (.send pv (.simple r) (.simple a) full) o → o.after .diamond post) ↔
      post (sendT σ pv (r.evalT σ) (a.evalT σ)).st := by
  constructor
  · intro h
    exact h _ (.det hp)
  · intro h o he
    cases he with
    | det _ => exact h
    | sendHalt hf _ => rw [hp] at hf <;> cases hf
    | sendFailed hf _ => rw [hp] at hf <;> cases hf
    | sendRefused hf _ => rw [hp] at hf <;> cases hf
    | sendViolated hf _ _ => rw [hp] at hf <;> cases hf
    | sendResume hf _ _ _ => rw [hp] at hf <;> cases hf

/-- Exact callback send diamond: failure is mandatory for all oracle responses.
Acceptance additionally requires exit and every successful callback resumption. -/
theorem send_callback_iff (J : StateInv C) (full : Bool)
    (hp : (J.pay || full) = true) (σ : State C Γ)
    (pv : Idx Γ (.val .bool)) (r a : Simple C Γ .uint) (post : State C Γ → Prop) :
    (∀ o, ExecS J σ (.send pv (.simple r) (.simple a) full) o → o.after .diamond post) ↔
    post (σ.setLocal pv (false : Bool)) ∧
      (σ.canPay (r.evalT σ) (a.evalT σ) = true →
        J.at (σ.pay (r.evalT σ) (a.evalT σ).1) ∧
        ∀ st nt sb, J.at ((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb) →
          post (((σ.pay (r.evalT σ) (a.evalT σ).1).havoc st nt sb).setLocal pv (true : Bool))) := by
  constructor
  · intro h
    refine ⟨h _ (send_failure_outcome J full hp σ pv r a), ?_⟩
    intro accepted
    have run : TRun.transfer (.simple r) (.simple a) σ =
        .ok ⟨σ.pay (r.evalT σ) (a.evalT σ).1, List.prefix_refl _⟩ := by
      rw [transfer_run, accepted]
      rfl
    have exit : J.at (σ.pay (r.evalT σ) (a.evalT σ).1) := by
      classical
      apply Classical.byContradiction
      intro hn
      exact h _ (.sendViolated hp run hn)
    exact ⟨exit, fun _ _ _ hj => h _ (.sendResume hp run exit hj)⟩
  · rintro ⟨failed, success⟩
    apply sendWithCallbackDiamond J full hp σ pv r a post
    · intro paid run
      cases ha : σ.canPay (r.evalT σ) (a.evalT σ) with
      | false => rw [transfer_run, ha] at run; cases run
      | true => rw [transfer_run, ha] at run; cases run; exact (success ha).1
    · intro paid st nt sb run hj
      cases ha : σ.canPay (r.evalT σ) (a.evalT σ) with
      | false => rw [transfer_run, ha] at run; cases run
      | true => rw [transfer_run, ha] at run; cases run; exact (success ha).2 _ _ _ hj
    · exact failed

/-- Payload-bearing failure cannot be reconstructed from this transfer result.
This preserves the original refusal rather than inventing recipient error bytes. -/
theorem transfer_does_not_bubble (σ : State C Γ) (r a : Simple C Γ .uint)
    (bytes : List UInt8) :
    TRun.transfer (.simple r) (.simple a) σ ≠ .error (.revertWith bytes) := by
  rw [transfer_run]
  cases σ.canPay (r.evalT σ) (a.evalT σ) <;> intro bad <;> cases bad

/-- Every simple-transfer halt exposes empty bytes in the unchanged runtime. -/
theorem transfer_failure_bytes (σ : State C Γ) (r a : Simple C Γ .uint)
    (e : THalt) (run : TRun.transfer (.simple r) (.simple a) σ = .error e) :
    e.data = [] := by
  rw [transfer_run] at run
  cases h : σ.canPay (r.evalT σ) (a.evalT σ) <;> rw [h] at run
  · cases run
    rfl
  · cases run

#print axioms recipient_iff
#print axioms canPay_iff
#print axioms transfer_callback_conditions_iff
#print axioms transfer_success_iff
#print axioms transfer_failure_iff
#print axioms transfer_failure_bytes
#print axioms send_accepted_run
#print axioms send_refused_run
#print axioms send_failure_outcome
#print axioms send_flag_iff
#print axioms send_deterministic_iff
#print axioms send_refused_outcome_iff
#print axioms send_callback_iff
#print axioms transfer_does_not_bubble
end Solidity.PaymentConditions
