import Solidity.Calculus.Logic
import Solidity.Semantics.Callback

/-!
# The calculus with callbacks

The callback taclet (`Rules.lean`'s `CallbackTaclet`, solkey's
`transferWithCallbackBox`) is sound for the callback reading of the
modalities (`Semantics/Callback.lean`), and this module proves it
(`CallbackTaclet.sound`).  Its premise is the booking `U` of the transfer
(`{net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se)}`),
read as solkey's goals:

```
  Γ ⟹ {U} I                                ("invariant on exit")
  Γ ⟹ {U} {havoc} (I → [ ω ] φ)             ("resume after callback")
  ─────────────────────────────────────────
  Γ ⟹ [ sadr.transfer(se); ω ] φ
```

`{havoc}` is KeY's anonymising update (`Fml.havoc`, `Hyp.havoc`): what
follows it holds for any storage and ledger the callee may leave, as
KeY's fresh skolem symbols make it hold for any interpretation of them.  Both
goals are sequents, derived like any other; `CbResume` is what the last
means (`CbResume.of_holdsC`).  Where the amount is not a word the transfer
halts, and so does the booking: nothing to show under the box, the one
modality a payment has a rule for.

A send, `pv = sadr.send(se);` (`sendWithCallbackBox`), has solkey's three
goals (`ProvesC.send`, `CallbackTaclet.sound_send`): the same invariant on
exit, the rest after the booking, `pv := true` and `{havoc}` with `I`
assumed ("send succeeded"), and the rest after `pv := false`, nothing booked
("send failed").  The last is owed whatever the transaction's oracle says:
the callee may revert, and with it whatever it did (`ExecS.sendFailed`).

`ProvesC I Γ φ` is the calculus under the callback semantics: the ordinary
taclets on a statement that pays nothing and runs no other (`update`,
`unfold`: `Taclet.sound` lifts, the statement having no other run), the
callback taclets on a transfer, and the plain calculus (`Proves`) on a goal
with no `transfer` left, where the two readings agree.  `ProvesC.sound` says a
derivation is a proof of validity with callbacks.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## The premise -/

/-- "Resume after callback", from `σ`: after the booking `U`, the rest `ω` of
the program, from every state the callee may leave in which the invariant
holds, ends in `φ`. -/
def CbResume (I : Fml C) (m : Modality) (U : Upd C) (ω : Prog C) (φ : Fml C) (σ : State) : Prop :=
  m.after (fun τ => ∀ st nt, holds (τ.havoc st nt) I →
    holdsC I (τ.havoc st nt) (.modal m ω φ)) (U.apply σ)

/-- A callback taclet's booking is the transfer's own debit, exactly: both
halt where the amount is not a word. -/
theorem CallbackTaclet.booking {m : Modality} {s : Stmt C} {U : Upd C}
    (d : CallbackTaclet C m s (.update U)) (σ : State) : U.apply σ = s.run σ := by
  cases d; exact upd_transferNoCallbackBox_eq ..

/-- The runs of a transfer with callbacks: it halts, or leaves the invariant
broken, or resumes from a state the callee may leave. -/
theorem ExecS.transfer_inv {I : Fml C} {σ : State} {r a : Val C .uint} {o : COut}
    (h : ExecS I σ (.transfer r a) o) :
    (∃ e, (Stmt.transfer r a).run σ = .error e ∧ o = .halt e) ∨
    (∃ σ₁, (Stmt.transfer r a).run σ = .ok σ₁ ∧ ¬ holds σ₁ I ∧ o = .violated) ∨
    (∃ σ₁ st nt, (Stmt.transfer r a).run σ = .ok σ₁ ∧
      holds (σ₁.havoc st nt) I ∧ o = .ok (σ₁.havoc st nt)) := by
  cases h with
  | det hf => simp [Stmt.forks] at hf
  | transferHalt h => exact .inl ⟨_, h, rfl⟩
  | transferViolated h hn => exact .inr (.inl ⟨_, h, hn, rfl⟩)
  | transferResume h _ h₂ => exact .inr (.inr ⟨_, _, _, h, h₂, rfl⟩)

/-- **The callback taclet is sound**: the invariant after the booking and
the rest resumed from every state the callee may leave give the transfer and
the rest under the callback reading.

Example: `to.transfer(amt);` with `balance + paidOut == deposited` kept at
the exit, and `[ ]` of it after any callback that keeps it, proves
`[ to.transfer(amt); ] balance + paidOut == deposited`. -/
theorem CallbackTaclet.sound {I : Fml C} {m : Modality} {s : Stmt C} {U : Upd C}
    (d : CallbackTaclet C m s (.update U)) {ω : Prog C} {φ : Fml C} {σ : State}
    (hexit : holds σ (.upd m U I)) (hres : CbResume I m U ω φ σ) :
    holdsC I σ (.modal m (s :: ω) φ) := by
  have hrun := d.booking σ
  simp only [holdsC]
  intro o he
  simp only [holds] at hexit
  simp only [CbResume] at hres
  rw [hrun] at hexit hres
  clear hrun
  cases d with
  | transferWithCallbackBox =>
    cases he with
    | cons hs hω =>
      rcases ExecS.transfer_inv hs with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨σ₁, st, nt, h, h₂, ho⟩
      · cases h
      · cases h
      · cases ho
        rw [h] at hres
        exact hres _ _ h₂ _ hω
    | stop hs ho =>
      rcases ExecS.transfer_inv hs with ⟨_, h, rfl⟩ | ⟨_, h, hn, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
      · have hp : _ ≠ Halt.panic := fun hp =>
          Stmt.run_transfer_noPanic _ _ _ (h.trans (congrArg Except.error hp))
        rw [h] at hexit
        simp_all [Modality.after, COut.after]
      · rw [h] at hexit
        exact (hn hexit).elim
      · simp [COut.isOk] at ho

/-! ## `send` -/

/-- The runs of a send with callbacks: it halts where its transfer does,
leaves the invariant broken after the booking, resumes after the booking from
a state the callee may leave, `pv` then `true`, or fails with nothing booked
and `pv` `false`. -/
theorem ExecS.send_inv {I : Fml C} {σ : State} {pv : Var} {r a : Val C .uint} {o : COut}
    (h : ExecS I σ (.send pv r a) o) :
    (∃ e, (Stmt.transfer r a).run σ = .error e ∧ o = .halt e) ∨
    (∃ σ₁, (Stmt.transfer r a).run σ = .ok σ₁ ∧ ¬ holds σ₁ I ∧ o = .violated) ∨
    (∃ σ₁ st nt, (Stmt.transfer r a).run σ = .ok σ₁ ∧ holds (σ₁.havoc st nt) I ∧
      o = .ok ((σ₁.havoc st nt).setEnv pv (.val (.bool true)))) ∨
    o = .ok (σ.setEnv pv (.val (.bool false))) := by
  cases h with
  | det hf => simp only [Stmt.forks, Bool.true_eq_false] at hf
  | sendHalt h => exact .inl ⟨_, h, rfl⟩
  | sendViolated h hn => exact .inr (.inl ⟨_, h, hn, rfl⟩)
  | sendResume h _ h₂ => exact .inr (.inr (.inl ⟨_, _, _, h, h₂, rfl⟩))
  | sendFailed _ => exact .inr (.inr (.inr rfl))

/-- `sendWithCallbackBox`'s "send succeeded" update: the transfer's booking,
then `pv` true. -/
theorem upd_sendSucceeded_eq (pv : Var) (sadr se : Simple C .uint) (σ : State) :
    Upd.apply [.pay sadr.lower se.lower, .val pv (.lit (.bool true))] σ =
      (do let σ₁ ← (Stmt.transfer (.simple sadr) (.simple se)).run σ
          pure (σ₁.setEnv pv (.val (.bool true)))) := by
  rw [← upd_transferNoCallbackBox_eq]
  simp only [Upd.apply, List.foldlM_cons, List.foldlM_nil, bind, Except.bind]
  cases (UpdElem.pay sadr.lower se.lower).write σ σ <;> rfl

/-- `sendWithCallbackBox`'s "send failed" update: `pv` false, nothing else. -/
theorem upd_sendFailed_eq (pv : Var) (σ : State) :
    Upd.apply (C := C) [.val pv (.lit (.bool false))] σ =
      .ok (σ.setEnv pv (.val (.bool false))) := rfl

/-- **`sendWithCallbackBox` is sound**: the invariant after the booking, the
rest after the booking with `pv` true resumed from every state the callee
may leave in which the invariant holds, and the rest with `pv` false and
nothing booked, give the send and the rest under the callback reading.

Example: `ok = to.send(5);` before `sent = ok;`, with an invariant of the
storage alone, proves `[ ok = to.send(5); sent = ok; ] I`
(`Examples/Tactics/Callback.lean`). -/
theorem CallbackTaclet.sound_send {I : Fml C} (hI : I.vars = []) {pv : Var} {sadr se : Simple C .uint}
    {Uok Ufail : Upd C}
    (d : CallbackTaclet C .box (.send pv (.simple sadr) (.simple se)) (.cases [] [Uok, Ufail]))
    {ω : Prog C} {φ : Fml C} {σ : State}
    (hexit : holds σ (.upd .box [.pay sadr.lower se.lower] I))
    (hok : CbResume I .box Uok ω φ σ)
    (hfail : Modality.box.after (holdsC I · (.modal .box ω φ)) (Ufail.apply σ)) :
    holdsC I σ (.modal .box (.send pv (.simple sadr) (.simple se) :: ω) φ) := by
  cases d
  simp only [holdsC]
  intro o he
  simp only [holds] at hexit
  simp only [CbResume] at hok
  rw [upd_transferNoCallbackBox_eq] at hexit
  rw [upd_sendSucceeded_eq] at hok
  rw [upd_sendFailed_eq] at hfail
  cases he with
  | cons hs hω =>
    rcases ExecS.send_inv hs with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨σ₁, st, nt, h, h₂, ho⟩ | ho
    · cases h
    · cases h
    · cases ho
      rw [h] at hok
      have h' : holds ((σ₁.setEnv pv (.val (.bool true))).havoc st nt) I := by
        rw [State.havoc_setEnv]
        exact (holds_I_frame hI ((EnvAgreeExcept.refl [pv] _).setEnv_right
          (List.mem_singleton_self pv) _)).1 h₂
      exact hok st nt h' _ hω
    · cases ho
      exact hfail _ hω
  | stop hs ho =>
    rcases ExecS.send_inv hs with ⟨_, h, rfl⟩ | ⟨_, h, hn, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | rfl
    · have hp : _ ≠ Halt.panic := fun hp =>
        Stmt.run_transfer_noPanic _ _ _ (h.trans (congrArg Except.error hp))
      exact ⟨trivial, hp⟩
    · rw [h] at hexit
      exact (hn hexit).elim
    · simp only [COut.isOk, Bool.true_eq_false] at ho
    · simp only [COut.isOk, Bool.true_eq_false] at ho

/-! ## Contexts, read with callbacks -/

/-- A context read with callbacks, around a proposition about the state it
leaves: `a → …` assumes `a`, `{U} …` runs `U` under its modality. -/
def Hyp.withC (I : Fml C) : List (Hyp C) → State → (State → Prop) → Prop
  | [], σ, P => P σ
  | .pre a :: Γ, σ, P => holdsC I σ a → Hyp.withC I Γ σ P
  | .upd m U :: Γ, σ, P => m.after (fun τ => Hyp.withC I Γ τ P) (U.apply σ)
  | .havoc :: Γ, σ, P => ∀ st nt, Hyp.withC I Γ (σ.havoc st nt) P
  | .all x p :: Γ, σ, P => ∀ v, p.admits v → Hyp.withC I Γ (σ.setEnv x (.val v)) P

theorem Hyp.holdsC_wrap {I : Fml C} {φ : Fml C} :
    (Γ : List (Hyp C)) → ∀ σ, holdsC I σ (Hyp.wrap Γ φ) ↔ Hyp.withC I Γ σ (holdsC I · φ)
  | [], _ => Iff.rfl
  | .pre a :: Γ, σ => by simp only [Hyp.wrap, holdsC, Hyp.withC, Hyp.holdsC_wrap Γ]
  | .upd m U :: Γ, σ => by
    simp only [Hyp.wrap, holdsC, Hyp.withC]
    cases U.apply σ with
    | error _ => exact Iff.rfl
    | ok τ => exact Hyp.holdsC_wrap Γ τ
  | .havoc :: Γ, σ => by
    simp only [Hyp.wrap, holdsC, Hyp.withC]
    exact forall_congr' fun _ => forall_congr' fun _ => Hyp.holdsC_wrap Γ _
  | .all x p :: Γ, σ => by
    simp only [Hyp.wrap, holdsC, Hyp.withC]
    exact forall_congr' fun _ => imp_congr_right fun _ => Hyp.holdsC_wrap Γ _

theorem Hyp.withC_mono {I : Fml C} {P Q : State → Prop} (h : ∀ τ, P τ → Q τ) :
    (Γ : List (Hyp C)) → ∀ σ, Hyp.withC I Γ σ P → Hyp.withC I Γ σ Q
  | [] => h
  | .pre _ :: Γ => fun σ hP ha => Hyp.withC_mono h Γ σ (hP ha)
  | .upd m U :: Γ => fun σ => by
    simp only [Hyp.withC]
    cases U.apply σ with
    | error _ => exact id
    | ok τ => exact Hyp.withC_mono h Γ τ
  | .havoc :: Γ => fun σ hP st nt => Hyp.withC_mono h Γ _ (hP st nt)
  | .all _ _ :: Γ => fun σ hP v hv => Hyp.withC_mono h Γ _ (hP v hv)

theorem Hyp.withC_mono₂ {I : Fml C} {P Q R : State → Prop} (h : ∀ τ, P τ → Q τ → R τ) :
    (Γ : List (Hyp C)) → ∀ σ, Hyp.withC I Γ σ P → Hyp.withC I Γ σ Q → Hyp.withC I Γ σ R
  | [] => h
  | .pre _ :: Γ => fun σ hP hQ ha => Hyp.withC_mono₂ h Γ σ (hP ha) (hQ ha)
  | .upd m U :: Γ => fun σ => by
    simp only [Hyp.withC]
    cases U.apply σ with
    | error _ => exact fun h _ => h
    | ok τ => exact Hyp.withC_mono₂ h Γ τ
  | .havoc :: Γ => fun σ hP hQ st nt => Hyp.withC_mono₂ h Γ _ (hP st nt) (hQ st nt)
  | .all _ _ :: Γ => fun σ hP hQ v hv => Hyp.withC_mono₂ h Γ _ (hP v hv) (hQ v hv)

/-- `Hyp.withC_mono₂` for a list of premises besides one. -/
theorem Hyp.withC_forall {I : Fml C} {α : Type} {Q : State → Prop} {R : α → State → Prop}
    (Γ : List (Hyp C)) (σ : State) :
    (l : List α) → Hyp.withC I Γ σ Q → (∀ a ∈ l, Hyp.withC I Γ σ (R a)) →
      Hyp.withC I Γ σ (fun τ => Q τ ∧ ∀ a ∈ l, R a τ)
  | [], hQ, _ => Hyp.withC_mono (fun _ h => ⟨h, by simp⟩) Γ σ hQ
  | a :: l, hQ, hR =>
    Hyp.withC_mono₂ (fun _ ⟨hq, hl⟩ ha => ⟨hq, List.forall_mem_cons.2 ⟨ha, hl⟩⟩) Γ σ
      (Hyp.withC_forall Γ σ l hQ (fun b hb => hR b (List.mem_cons_of_mem _ hb)))
      (hR a List.mem_cons_self)

/-- `holds_alls`, read with callbacks. -/
theorem holdsC_alls {I φ : Fml C} : {xs : List (PrimTy × Var)} → {σ : State} →
    (holdsC I σ (Fml.alls xs φ) ↔ ∀ σ', Binds xs σ σ' → holdsC I σ' φ)
  | [], σ => by
    simp only [Fml.alls, Binds, bindData]
    exact ⟨fun h σ' ⟨_, he⟩ => by cases he; exact h, fun h => h σ ⟨[], rfl⟩⟩
  | (p, x) :: xs, σ => by
    simp only [Fml.alls, holdsC, holdsC_alls (xs := xs), Binds, PrimTy.admits_iff_fits]
    constructor
    · rintro h σ' ⟨_ | ⟨v, vs⟩, he⟩
      · simp [bindData] at he
      · simp only [bindData] at he
        split at he
        · exact h v (by assumption) σ' ⟨vs, he⟩
        · cases he
    · intro h v hv σ' ⟨vs, he⟩
      exact h σ' ⟨v :: vs, by simp only [bindData, hv, if_true]; exact he⟩

/-- "Resume after callback" as a formula: `{U} {havoc} (I → ⟨[ ω ]⟩ φ)`, read
with callbacks, is `CbResume`. -/
theorem CbResume.of_holdsC {I : Fml C} (hI : I.hasTransfer = false) {m : Modality} {U : Upd C}
    {ω : Prog C} {φ : Fml C} {σ : State}
    (h : holdsC I σ (.upd m U (.havoc (.imp I (.modal m ω φ))))) : CbResume I m U ω φ σ := by
  simp only [holdsC] at h
  simp only [CbResume]
  cases hu : U.apply σ with
  | error _ => rw [hu] at h; exact h
  | ok τ => rw [hu] at h; exact fun st nt hi => h st nt ((holdsC_iff_holds I hI).2 hi)

/-- Under a context of box updates, the last precondition holds: `…, a ⟹ a`. -/
theorem Hyp.wrap_assumption {a : Fml C} (Γ : List (Hyp C)) (hb : Hyp.boxOnly Γ = true) :
    Valid (Hyp.wrap (Γ ++ [.pre a]) a) := by
  rw [Hyp.wrap_append]
  exact fun σ => Hyp.wrap_of_reaches (φ := .imp a a) Γ hb σ fun _ _ h => h

/-! ## Taclets on a statement that runs as `Stmt.run` -/

theorem ExecP.append_ok {I : Fml C} {Q : Prog C} {o : COut} :
    {P : Prog C} → {σ τ : State} → ExecP I σ P (.ok τ) → ExecP I τ Q o → ExecP I σ (P ++ Q) o
  | [], _, _, .nil, hQ => hQ
  | _ :: _, _, _, .cons hs hP, hQ => .cons hs (ExecP.append_ok hP hQ)
  | _ :: _, _, _, .stop _ ho, _ => by simp [COut.isOk] at ho

theorem ExecP.append_stop {I : Fml C} {Q : Prog C} :
    {P : Prog C} → {σ : State} → {o : COut} → ExecP I σ P o → o.isOk = false →
      ExecP I σ (P ++ Q) o
  | [], _, _, .nil, ho => by simp [COut.isOk] at ho
  | _ :: _, _, _, .cons hs hP, ho => .cons hs (ExecP.append_stop hP ho)
  | _ :: _, _, _, .stop hs ho', _ => .stop hs ho'

/-- A statement that runs no other and pays nothing has one run with
callbacks, `Stmt.run`'s. -/
theorem ExecS.det_inv {I : Fml C} {σ : State} {s : Stmt C} {o : COut} (h : ExecS I σ s o)
    (hs : s.forks = false) : o = .ofRes (s.run σ) := by
  cases h <;> first | rfl | simp [Stmt.forks] at hs

/-- A transfer-free block's run with callbacks from a state is its run. -/
theorem ExecP.of_run {I : Fml C} {σ τ : State} {P : Prog C} (hP : Prog.hasTransfer P = false)
    (h : Prog.run σ P = .ok τ) : ExecP I σ P (.ok τ) := by
  rcases Prog.exec_run I P σ with he | he
  · rw [h] at he; exact he
  · have := ExecP.eq_run he hP
    rw [h] at this; cases this

theorem ExecP.of_run_error {I : Fml C} {σ : State} {P : Prog C} {e : Halt}
    (hP : Prog.hasTransfer P = false) (h : Prog.run σ P = .error e) : ExecP I σ P (.halt e) := by
  rcases Prog.exec_run I P σ with he | he
  · rw [h] at he; exact he
  · have := ExecP.eq_run he hP
    rw [h] at this; cases this

/-- An update premise under the callback reading: the statement runs no
other and pays nothing, so its one run is the update's, off no name. -/
theorem Premise.soundC_update {I : Fml C} (hI : I.vars = []) {k : Nat} {m : Modality}
    {s : Stmt C} {U : Upd C} (h : (Premise.update U).Correct k m s) (hs : s.forks = false)
    (ω : Prog C) (φ : Fml C) (σ : State) :
    holdsC I σ (.upd m U (.modal m ω φ)) → holdsC I σ (.modal m (s :: ω) φ) := by
  have hc := h σ
  simp only [holdsC]
  intro H o he
  cases he with
  | cons h₁ hω =>
    have e := ExecS.det_inv h₁ hs
    cases hr : s.run σ with
    | error _ => rw [hr] at e; cases e
    | ok τ₁ =>
      rw [hr] at e hc
      cases e
      cases hu : U.apply σ with
      | error _ => rw [hu] at hc; exact hc.elim
      | ok a =>
        rw [hu] at hc H
        obtain ⟨o₂, he₂, hag⟩ := ExecP.frame hI hω (fun _ _ h => by simp at h) hc
        exact (hag.after m fun _ _ h' => holdsC_frame hI φ (fun _ _ h => by simp at h) h').1
          (H o₂ he₂)
  | stop h₁ ho =>
    have e := ExecS.det_inv h₁ hs
    subst e
    cases hr : s.run σ with
    | ok _ => rw [hr] at ho; simp [COut.ofRes, COut.isOk] at ho
    | error _ =>
      rw [hr] at hc
      cases hu : U.apply σ with
      | ok _ => rw [hu] at hc; exact hc.elim
      | error e =>
        rw [hu] at H hc
        exact ⟨H, fun hp => Upd.apply_ne_panic U σ (by rw [hu, hc.2 hp])⟩

/-- An unfold premise under the callback reading: the statement and its
premise pay nothing, so each has its one run, and they agree off the fresh
names. -/
theorem Premise.soundC_unfold {I : Fml C} (hI : I.vars = []) {k : Nat} {m : Modality}
    {s : Stmt C} {P : Prog C} (h : (Premise.unfold P).Correct k m s) (hs : s.forks = false)
    (hP : Prog.hasTransfer P = false) (ω : Prog C) (φ : Fml C)
    (hω : Avoids (Prog.vars ω ++ φ.vars) (freshVars k)) (σ : State) :
    holdsC I σ (.modal m (P ++ ω) φ) → holdsC I σ (.modal m (s :: ω) φ) := by
  have hc := h σ
  simp only [holdsC]
  intro H o he
  cases he with
  | cons h₁ hω' =>
    have e := ExecS.det_inv h₁ hs
    cases hr : s.run σ with
    | error _ => rw [hr] at e; cases e
    | ok τ₁ =>
      rw [hr] at e hc
      cases e
      cases hp : Prog.run σ P with
      | error _ => rw [hp] at hc; exact hc.elim
      | ok a =>
        rw [hp] at hc
        obtain ⟨o₂, he₂, hag⟩ := ExecP.frame hI hω' hω.left hc
        exact (hag.after m fun _ _ h' => holdsC_frame hI φ hω.right h').1
          (H o₂ (ExecP.append_ok (ExecP.of_run hP hp) he₂))
  | stop h₁ ho =>
    have e := ExecS.det_inv h₁ hs
    subst e
    cases hr : s.run σ with
    | ok _ => rw [hr] at ho; simp [COut.ofRes, COut.isOk] at ho
    | error _ =>
      rw [hr] at hc
      cases hp : Prog.run σ P with
      | ok _ => rw [hp] at hc; exact hc.elim
      | error e =>
        have := H _ (ExecP.append_stop (Q := ω) (ExecP.of_run_error hP hp) rfl)
        rw [hp] at hc
        simp only [COut.ofRes, COut.after] at this ⊢
        exact ⟨this.1, fun h' => this.2 (hc.2 h')⟩

/-- The runs of a `try` with callbacks: it halts, leaves the invariant
broken, returns to a state the callee may leave and runs its success block,
or runs a clause's block from where it was made. -/
theorem ExecS.tryCall_inv {I : Fml C} {σ : State} {c : ExtCall C} {rets : List (PrimTy × Var)}
    {ok err : List (Stmt C)} {code : Option Var} {pnc other : List (Stmt C)} {o : COut}
    (h : ExecS I σ (.tryCall c rets ok err code pnc other) o) :
    (∃ e, o = .halt e ∧ e ≠ .panic) ∨ (¬ holds σ I ∧ o = .violated) ∨
    (∃ st nt σ₁, holds (σ.havoc st nt) I ∧ Binds rets (σ.havoc st nt) σ₁ ∧
      ExecP I σ₁ ok o) ∨
    ExecP I σ err o ∨ (∃ σ₁, Binds (codeBinders code) σ σ₁ ∧ ExecP I σ₁ pnc o) ∨
    ExecP I σ other o := by
  cases h with
  | det hf => simp [Stmt.forks] at hf
  | tryHalt h =>
    exact .inl ⟨_, rfl, NoPanic.ne_of_eq (ExtCall.key_noPanic σ c) h⟩
  | tryRevert _ => exact .inl ⟨_, rfl, nofun⟩
  | tryViolated _ hn => exact .inr (.inl ⟨hn, rfl⟩)
  | tryOk _ _ h₂ hb hp => exact .inr (.inr (.inl ⟨_, _, _, h₂, hb, hp⟩))
  | tryError _ hp => exact .inr (.inr (.inr (.inl hp)))
  | tryPanic _ hb hp => exact .inr (.inr (.inr (.inr (.inl ⟨_, hb, hp⟩))))
  | tryOther _ hp => exact .inr (.inr (.inr (.inr (.inr hp))))

/-- **`tryCallWithCallbackBox` is sound**: with the invariant where control
leaves, the call's success from every state the callee may leave in which the
invariant holds, and each clause's block from where the call was made, the
`try` and the rest hold under the callback reading.  A call that reverts in
the caller satisfies the box. -/
theorem CallbackTaclet.sound_branches {I : Fml C} {s : Stmt C} {xs : List (PrimTy × Var)}
    {P : Prog C} {bs : List (List (PrimTy × Var) × Prog C)}
    (d : CallbackTaclet C .box s (.branches ((xs, P) :: bs))) {ω : Prog C} {φ : Fml C}
    {σ : State} (hexit : holds σ I)
    (hok : ∀ st nt, holds (σ.havoc st nt) I → ∀ σ₁, Binds xs (σ.havoc st nt) σ₁ →
      holdsC I σ₁ (.modal .box (P ++ ω) φ))
    (hcaught : ∀ b ∈ bs, ∀ σ₁, Binds b.1 σ σ₁ → holdsC I σ₁ (.modal .box (b.2 ++ ω) φ)) :
    holdsC I σ (.modal .box (s :: ω) φ) := by
  cases d
  rename_i err code pnc other
  simp only [holdsC] at hok hcaught ⊢
  have hE := hcaught ([], err) (by simp) σ ⟨[], rfl⟩
  have hP := fun σ₁ hb => hcaught (codeBinders code, pnc) (by simp) σ₁ hb
  have hO := hcaught ([], other) (by simp) σ ⟨[], rfl⟩
  intro o he
  cases he with
  | cons hs hω =>
    rcases ExecS.tryCall_inv hs with ⟨_, h, _⟩ | ⟨_, h⟩ | ⟨_, _, _, h₂, hb, hp⟩ | hp |
      ⟨_, hb, hp⟩ | hp
    · cases h
    · cases h
    · exact hok _ _ h₂ _ hb o (ExecP.append_ok hp hω)
    · exact hE o (ExecP.append_ok hp hω)
    · exact hP _ hb o (ExecP.append_ok hp hω)
    · exact hO o (ExecP.append_ok hp hω)
  | stop hs ho =>
    rcases ExecS.tryCall_inv hs with ⟨_, rfl, hne⟩ | ⟨hn, _⟩ | ⟨_, _, _, h₂, hb, hp⟩ | hp |
      ⟨_, hb, hp⟩ | hp
    · exact ⟨trivial, hne⟩
    · exact absurd hexit hn
    · exact hok _ _ h₂ _ hb o (ExecP.append_stop hp ho)
    · exact hE o (ExecP.append_stop hp ho)
    · exact hP _ hb o (ExecP.append_stop hp ho)
    · exact hO o (ExecP.append_stop hp ho)

/-! ## The judgement -/

/-- `ProvesC I Γ φ`: the calculus proves `φ` in the context `Γ` when every
`transfer` may call back into a contract with invariant `I`. -/
inductive ProvesC (I : Invariant C) : List (Hyp C) → Fml C → Prop
  /-- A goal with no `transfer` left is a goal of the calculus: there the
  two readings agree. -/
  | plain {Γ : List (Hyp C)} {φ : Fml C} (h : dl{ ..Γ ⟹ φ })
      (hφ : (Hyp.wrap Γ φ).hasTransfer = false) : dl{ ..Γ ⟹ᶜ[I] φ }
  /-- `impRight`. -/
  | intro {Γ : List (Hyp C)} {a φ : Fml C} (h : dl{ ..Γ, a ⟹ᶜ[I] φ }) :
      dl{ ..Γ ⟹ᶜ[I] a → φ }
  /-- A taclet that produces an update, on a statement that runs no other
  and pays nothing. -/
  | update {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {U : Upd C}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ‹I.fml› ∧ ⟨[ s; ..ω ]⟩ φ }) m s (.update U))
      (hs : s.forks = false)
      (h : dl{ ..Γ, {U} ⟹ᶜ[I] ⟨[ ..ω ]⟩ φ }) : dl{ ..Γ ⟹ᶜ[I] ⟨[ s; ..ω ]⟩ φ }
  /-- A taclet that produces statements, on a statement that runs no other
  and pays nothing, when they pay nothing either. -/
  | unfold {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {P : Prog C}
      (d : Taclet C (Hyp.fresh Γ dl_schema{ ‹I.fml› ∧ ⟨[ s; ..ω ]⟩ φ }) m s (.unfold P))
      (hs : s.forks = false) (hP : Prog.hasTransfer P = false)
      (h : dl{ ..Γ ⟹ᶜ[I] ⟨[ P; ..ω ]⟩ φ }) : dl{ ..Γ ⟹ᶜ[I] ⟨[ s; ..ω ]⟩ φ }
  /-- `unfold`, by a rule solkey does not have. -/
  | unfoldLean {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {P : Prog C} (d : LeanTaclet C (Hyp.fresh Γ dl_schema{ ‹I.fml› ∧ ⟨[ s; ..ω ]⟩ φ }) m s (.unfold P))
      (hs : s.forks = false) (hP : Prog.hasTransfer P = false)
      (h : dl{ ..Γ ⟹ᶜ[I] ⟨[ P; ..ω ]⟩ φ }) : dl{ ..Γ ⟹ᶜ[I] ⟨[ s; ..ω ]⟩ φ }
  /-- **A callback taclet**: the invariant on exit (`{U} I`) and the rest
  resumed after the callback, from any state the callee may leave in which
  the invariant holds (`{U} {havoc} (I → [ ω ] φ)`). -/
  | callback {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {U : Upd C}
      (d : CallbackTaclet C m s (.update U))
      (exit : dl{ ..Γ ⟹ᶜ[I] {U} ‹I.fml› })
      (resume : ProvesC I (Γ ++ [.upd m U, .havoc, .pre I.fml]) (.modal m ω φ)) :
      dl{ ..Γ ⟹ᶜ[I] ⟨[ s; ..ω ]⟩ φ }
  /-- **`sendWithCallbackBox`**: the invariant after the booking, solkey's
  `{net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se)} CInv`
  under the box ("invariant on exit"); the rest after the booking and `pv := true`, from any state the
  callee may leave in which the invariant holds ("send succeeded"); and the
  rest after `pv := false`, nothing booked ("send failed"): the callee may
  revert, and what it did with it. -/
  | send {Γ : List (Hyp C)} {pv : Var} {sadr se : Simple C .uint} {ω : Prog C} {φ : Fml C}
      {Uok Ufail : Upd C}
      (d : CallbackTaclet C .box (.send pv (.simple sadr) (.simple se)) (.cases [] [Uok, Ufail]))
      (exit : dl{ ..Γ ⟹ᶜ[I] ‹.upd .box [.pay sadr.lower se.lower] I.fml› })
      (ok : ProvesC I (Γ ++ [.upd .box Uok, .havoc, .pre I.fml]) (.modal .box ω φ))
      (failed : ProvesC I (Γ ++ [.upd .box Ufail]) (.modal .box ω φ)) :
      dl{ ..Γ ⟹ᶜ[I] [ pv = sadr.send(se); ..ω ] φ }
  /-- **`tryCallWithCallbackBox`**: the invariant where control leaves
  ("invariant on exit"); the call's success, from any state the callee may
  leave in which the invariant holds, for every value of its return data
  ("call succeeded"); and each clause's block where the call reverted, which
  undid whatever the callee did. -/
  | tryCall {Γ : List (Hyp C)} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {xs : List (PrimTy × Var)} {P : Prog C} {bs : List (List (PrimTy × Var) × Prog C)}
      (d : CallbackTaclet C .box s (.branches ((xs, P) :: bs)))
      (exit : dl{ ..Γ ⟹ᶜ[I] ‹I.fml› })
      (ok : ProvesC I (Γ ++ [.havoc, .pre I.fml]) (.alls xs (.modal .box (P ++ ω) φ)))
      (caught : ∀ b ∈ bs, dl{ ..Γ ⟹ᶜ[I] ‹.alls b.1 (.modal .box (b.2 ++ ω) φ)› }) :
      dl{ ..Γ ⟹ᶜ[I] [ s; ..ω ] φ }
  /-- `allRight`. -/
  | allIntro {Γ : List (Hyp C)} {x : Var} {p : PrimTy} {φ : Fml C}
      (h : dl{ ..Γ, ∀ p x ⟹ᶜ[I] φ }) : dl{ ..Γ ⟹ᶜ[I] ‹.all x p φ› }
  /-- Leave the calculus: with no modality left anywhere in the sequent, what
  is left is proved about the callback reading. -/
  | close {Γ : List (Hyp C)} {φ : Fml C} (h : ValidC I (Hyp.wrap Γ φ))
      (hφ : (Hyp.wrap Γ φ).modalFree = true := by first | rfl | decide) : dl{ ..Γ ⟹ᶜ[I] φ }

/-- A taclet in a context, its fresh names avoiding the invariant too. -/
theorem Taclet.avoids_in {I : Fml C} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C}
    {φ : Fml C} :
    let k := Hyp.fresh Γ (.and I (.modal m (s :: ω) φ))
    Avoids s.vars (freshVars k) ∧ Avoids (Prog.vars ω ++ φ.vars) (freshVars k) := by
  intro _
  exact freshVars_avoid_modal (m := m) (Nat.lt_succ_self _) fun _ hy =>
    Hyp.vars_wrap Γ (List.mem_append_right I.vars hy)

/-- **Soundness of the calculus with callbacks**: a derivation of `Γ ⊢ φ`
proves `φ` wrapped in `Γ`, valid when every `transfer` may call back. -/
theorem ProvesC.sound {I : Invariant C} {Γ : List (Hyp C)} {φ : Fml C} (h : ProvesC I Γ φ) :
    ValidC I (Hyp.wrap Γ φ) := by
  induction h with
  | plain h hφ =>
    intro σ
    exact (holdsC_iff_holds _ hφ).2 (h.sound σ)
  | intro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | @update Γ m s ω φ U d hs _ ih =>
    intro σ
    have ih := ih σ
    rw [Hyp.wrap_append] at ih
    simp only [Hyp.wrap] at ih
    rw [Hyp.holdsC_wrap] at ih ⊢
    exact Hyp.withC_mono (fun τ => Premise.soundC_update I.closed
      (d.sound Taclet.avoids_in.1) hs ω φ τ) Γ σ ih
  | @unfold Γ m s ω φ P d hs hP _ ih =>
    intro σ
    have ih := ih σ
    rw [Hyp.holdsC_wrap] at ih ⊢
    exact Hyp.withC_mono (fun τ => Premise.soundC_unfold I.closed
      (d.sound Taclet.avoids_in.1) hs hP ω φ Taclet.avoids_in.2 τ) Γ σ ih
  | @unfoldLean Γ m s ω φ P d hs hP _ ih =>
    intro σ
    have ih := ih σ
    rw [Hyp.holdsC_wrap] at ih ⊢
    exact Hyp.withC_mono (fun τ => Premise.soundC_unfold I.closed
      (d.sound Taclet.avoids_in.1) hs hP ω φ Taclet.avoids_in.2 τ) Γ σ ih
  | @callback Γ m s ω φ U d _ _ ih ihr =>
    intro σ
    have ih := ih σ
    have ihr := ihr σ
    rw [Hyp.wrap_append] at ihr
    simp only [Hyp.wrap] at ihr
    rw [Hyp.holdsC_wrap] at ih ihr ⊢
    exact Hyp.withC_mono₂ (fun τ hx hr => d.sound
      (by
        simp only [holdsC] at hx; simp only [holds]
        cases hu : U.apply τ with
        | error _ => rw [hu] at hx; exact hx
        | ok a => rw [hu] at hx; exact (holdsC_iff_holds I.fml I.noTransfer).1 hx)
      (CbResume.of_holdsC I.noTransfer hr)) Γ σ ih ihr
  | @send Γ pv sadr se ω φ Uok Ufail d _ _ _ ihx iho ihf =>
    intro σ
    have hx := ihx σ
    have ho := iho σ
    have hf := ihf σ
    rw [Hyp.wrap_append] at ho hf
    simp only [Hyp.wrap] at ho hf
    rw [Hyp.holdsC_wrap] at hx ho hf ⊢
    refine Hyp.withC_mono₂ (fun τ ⟨hx, hr⟩ hf => d.sound_send I.closed ?_
      (CbResume.of_holdsC I.noTransfer hr) hf) Γ σ
      (Hyp.withC_mono₂ (fun _ h₁ h₂ => And.intro h₁ h₂) Γ σ hx ho) hf
    simp only [holdsC] at hx; simp only [holds]
    cases hu : Upd.apply [.pay sadr.lower se.lower] τ with
    | error _ => rw [hu] at hx; exact hx
    | ok a => rw [hu] at hx; exact (holdsC_iff_holds I.fml I.noTransfer).1 hx
  | allIntro _ ih => simpa [Hyp.wrap_append, Hyp.wrap] using ih
  | @tryCall Γ s ω φ xs P bs d _ _ _ ihx iho ihc =>
    intro σ
    have hx := ihx σ
    have ho := iho σ
    rw [Hyp.wrap_append] at ho
    simp only [Hyp.wrap] at ho
    rw [Hyp.holdsC_wrap] at hx ho ⊢
    have hc := Hyp.withC_forall (R := fun b τ => holdsC I.fml τ (.alls b.1 (.modal .box (b.2 ++ ω) φ)))
      Γ σ bs (Hyp.withC_mono₂ (fun _ h₁ h₂ => And.intro h₁ h₂) Γ σ hx ho)
      (fun b hb => by have := ihc b hb σ; rwa [Hyp.holdsC_wrap] at this)
    refine Hyp.withC_mono (fun τ ⟨⟨hx, ho⟩, hc⟩ => d.sound_branches
      ((holdsC_iff_holds I.fml I.noTransfer).1 hx) (fun st nt hI σ₁ hb => ?_)
      (fun b hb σ₁ hb' => holdsC_alls.1 (hc b hb) σ₁ hb')) Γ σ hc
    simp only [holdsC] at ho
    exact holdsC_alls.1 (ho st nt ((holdsC_iff_holds I.fml I.noTransfer).2 hI)) σ₁ hb
  | close h _ => exact h

/-- A derivation from the empty context proves validity with callbacks. -/
theorem ProvesC.valid {I : Invariant C} {φ : Fml C} (h : ProvesC I [] φ) : ValidC I φ := h.sound

/-! ## Printing sequents with callbacks -/

section Print
open Lean Meta PrettyPrinter Delaborator SubExpr
set_option hygiene false

/-- `ProvesC I Γ φ`: `dl{ Γ ⟹ᶜ[I] φ }`, the context printed as `Proves`'s. -/
@[delab app.Solidity.ProvesC]
def delabProvesC : Delab := do
  unless ← ppOn do failure
  let e ← getExpr
  guard (e.getAppNumArgs == 4)
  let some (rest, hs) ← hypSpine? (e.getArg! 2) | failure
  let mut out := #[]
  if let some Γ := rest then out := out.push (← `(dl_hyp| ..$Γ:ident))
  for h in hs do
    let some h ← ppHyp? h | failure
    out := out.push h
  let φ ← ppFml (e.getArg! 3)
  guard !(isEscape φ)
  let I ← withNaryArg 1 delab
  `(dl{ $[$out],* ⟹ᶜ[$I] $φ:dl_fml })

end Print

end Solidity
