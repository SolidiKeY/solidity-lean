import Solidity.Calculus.Logic
import Solidity.Semantics.Callback

/-!
# The calculus with callbacks

The callback taclets (`Rules.lean`'s `CallbackTaclet`, solkey's
`transferWithCallbackBox`/`transferWithCallbackDiamond`) are sound for the
callback reading of the modalities (`Semantics/Callback.lean`), and this
module proves it (`CallbackTaclet.sound`).  Their premise is the booking `U`
of the transfer, read two ways, as solkey's two goals:

```
  Γ ⟹ {U} I                                   ("invariant on exit")
  Γ ⟹ {U} {havoc} (I → ⟨[ ω ]⟩ φ)              ("resume after callback")
  ─────────────────────────────────────────
  Γ ⟹ ⟨[ sadr.transfer(se); ω ]⟩ φ
```

`{havoc}` is KeY's anonymising update (`Fml.havoc`, `Hyp.havoc`): what
follows it holds for any storage, ledger and funds the callee may leave, as
KeY's fresh skolem symbols make it hold for any interpretation of them.  Both
goals are sequents, derived like any other; `CbResume` is what the second
means (`CbResume.of_holdsC`).  Under the diamond the booking must succeed,
which is KeY's "sufficient funds" goal.

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
  m.after (fun τ => ∀ st nt bal, holds (τ.havoc st nt bal) I →
    holdsC I (τ.havoc st nt bal) (.modal m ω φ)) (U.apply σ)

/-- A callback taclet's booking is the transfer's own debit. -/
theorem CallbackTaclet.booking {m : Modality} {s : Stmt C} {U : Upd C}
    (d : CallbackTaclet C m s U) (σ : State) : U.apply σ = s.run σ := by
  cases d <;> simp only [Upd.apply_single, UpdElem.write, Stmt.run, Val.eval, Simple.lower_eval]

/-- The runs of a transfer with callbacks: it halts, or leaves the invariant
broken, or resumes from a state the callee may leave. -/
theorem ExecS.transfer_inv {I : Fml C} {σ : State} {r a : Val C .uint} {o : COut}
    (h : ExecS I σ (.transfer r a) o) :
    (∃ e, (Stmt.transfer r a).run σ = .error e ∧ o = .halt e) ∨
    (∃ σ₁, (Stmt.transfer r a).run σ = .ok σ₁ ∧ ¬ holds σ₁ I ∧ o = .violated) ∨
    (∃ σ₁ st nt bal, (Stmt.transfer r a).run σ = .ok σ₁ ∧
      holds (σ₁.havoc st nt bal) I ∧ o = .ok (σ₁.havoc st nt bal)) := by
  cases h with
  | det hf => simp [Stmt.forks] at hf
  | transferHalt h => exact .inl ⟨_, h, rfl⟩
  | transferViolated h hn => exact .inr (.inl ⟨_, h, hn, rfl⟩)
  | transferResume h _ h₂ => exact .inr (.inr ⟨_, _, _, _, h, h₂, rfl⟩)

/-- **The callback taclets are sound**: the invariant after the booking, and
the rest resumed from every state the callee may leave, give the transfer
and the rest under the callback reading.

Example: `to.transfer(amt);` with `balance + paidOut == deposited` kept at
the exit, and `[ ]` of it after any callback that keeps it, proves
`[ to.transfer(amt); ] balance + paidOut == deposited`. -/
theorem CallbackTaclet.sound {I : Fml C} {m : Modality} {s : Stmt C} {U : Upd C}
    (d : CallbackTaclet C m s U) {ω : Prog C} {φ : Fml C} {σ : State}
    (hexit : holds σ (.upd m U I)) (hres : CbResume I m U ω φ σ) :
    holdsC I σ (.modal m (s :: ω) φ) := by
  simp only [holds] at hexit
  simp only [CbResume] at hres
  rw [d.booking] at hexit hres
  simp only [holdsC]
  intro o he
  cases d with
  | transferWithCallbackBox | transferWithCallbackDiamond =>
    cases he with
    | cons hs hω =>
      rcases ExecS.transfer_inv hs with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨σ₁, st, nt, bal, h, h₂, ho⟩
      · cases h
      · cases h
      · cases ho
        rw [h] at hres
        exact hres _ _ _ h₂ _ hω
    | stop hs ho =>
      rcases ExecS.transfer_inv hs with ⟨_, h, rfl⟩ | ⟨_, h, hn, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩
      · rw [h] at hexit
        simp_all [Modality.after, COut.after]
      · rw [h] at hexit
        exact (hn hexit).elim
      · simp [COut.isOk] at ho

/-! ## Contexts, read with callbacks -/

/-- A context read with callbacks, around a proposition about the state it
leaves: `a → …` assumes `a`, `{U} …` runs `U` under its modality. -/
def Hyp.withC (I : Fml C) : List (Hyp C) → State → (State → Prop) → Prop
  | [], σ, P => P σ
  | .pre a :: Γ, σ, P => holdsC I σ a → Hyp.withC I Γ σ P
  | .upd m U :: Γ, σ, P => m.after (fun τ => Hyp.withC I Γ τ P) (U.apply σ)
  | .havoc :: Γ, σ, P => ∀ st nt bal, Hyp.withC I Γ (σ.havoc st nt bal) P

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
    exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => Hyp.holdsC_wrap Γ _

theorem Hyp.withC_mono {I : Fml C} {P Q : State → Prop} (h : ∀ τ, P τ → Q τ) :
    (Γ : List (Hyp C)) → ∀ σ, Hyp.withC I Γ σ P → Hyp.withC I Γ σ Q
  | [] => h
  | .pre _ :: Γ => fun σ hP ha => Hyp.withC_mono h Γ σ (hP ha)
  | .upd m U :: Γ => fun σ => by
    simp only [Hyp.withC]
    cases U.apply σ with
    | error _ => exact id
    | ok τ => exact Hyp.withC_mono h Γ τ
  | .havoc :: Γ => fun σ hP st nt bal => Hyp.withC_mono h Γ _ (hP st nt bal)

theorem Hyp.withC_mono₂ {I : Fml C} {P Q R : State → Prop} (h : ∀ τ, P τ → Q τ → R τ) :
    (Γ : List (Hyp C)) → ∀ σ, Hyp.withC I Γ σ P → Hyp.withC I Γ σ Q → Hyp.withC I Γ σ R
  | [] => h
  | .pre _ :: Γ => fun σ hP hQ ha => Hyp.withC_mono₂ h Γ σ (hP ha) (hQ ha)
  | .upd m U :: Γ => fun σ => by
    simp only [Hyp.withC]
    cases U.apply σ with
    | error _ => exact fun h _ => h
    | ok τ => exact Hyp.withC_mono₂ h Γ τ
  | .havoc :: Γ => fun σ hP hQ st nt bal => Hyp.withC_mono₂ h Γ _ (hP st nt bal) (hQ st nt bal)

/-- "Resume after callback" as a formula: `{U} {havoc} (I → ⟨[ ω ]⟩ φ)`, read
with callbacks, is `CbResume`. -/
theorem CbResume.of_holdsC {I : Fml C} (hI : I.hasTransfer = false) {m : Modality} {U : Upd C}
    {ω : Prog C} {φ : Fml C} {σ : State}
    (h : holdsC I σ (.upd m U (.havoc (.imp I (.modal m ω φ))))) : CbResume I m U ω φ σ := by
  simp only [holdsC] at h
  simp only [CbResume]
  cases hu : U.apply σ with
  | error _ => rw [hu] at h; exact h
  | ok τ => rw [hu] at h; exact fun st nt bal hi => h st nt bal ((holdsC_iff_holds I hI).2 hi)

/-- A context whose updates are all under the box holds around anything true
everywhere: a box update that halts proves what is in front of it. -/
theorem Hyp.wrap_of_forall {ψ : Fml C} (h : ∀ τ, holds τ ψ) :
    (Γ : List (Hyp C)) → (Γ.all fun
      | .upd m _ => m == .box
      | _ => true) = true → ∀ σ, holds σ (Hyp.wrap Γ ψ)
  | [], _ => h
  | .pre _ :: Γ, hb => fun σ _ => Hyp.wrap_of_forall h Γ (by simpa using hb) σ
  | .havoc :: Γ, hb => fun σ _ _ _ => Hyp.wrap_of_forall h Γ (by simpa using hb) _
  | .upd m U :: Γ, hb => fun σ => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨rfl, hb⟩ := hb
    simp only [Hyp.wrap, holds]
    cases U.apply σ with
    | error _ => trivial
    | ok τ => exact Hyp.wrap_of_forall h Γ hb τ

/-- Under a context of box updates, the last precondition holds: `…, a ⟹ a`. -/
theorem Hyp.wrap_assumption {a : Fml C} (Γ : List (Hyp C)) (hb : (Γ.all fun
      | .upd m _ => m == .box
      | _ => true) = true) : Valid (Hyp.wrap (Γ ++ [.pre a]) a) := by
  rw [Hyp.wrap_append]
  exact Hyp.wrap_of_forall (ψ := .imp a a) (fun _ h => h) Γ hb

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
      | error _ => rw [hu] at H; exact H

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
        exact this

/-! ## The judgement -/

/-- `ProvesC I Γ φ`: the calculus proves `φ` in the context `Γ` when every
`transfer` may call back into a contract with invariant `I`. -/
inductive ProvesC (I : Invariant C) : List (Hyp C) → Fml C → Prop
  /-- A goal with no `transfer` left is a goal of the calculus: there the
  two readings agree. -/
  | plain {Γ : List (Hyp C)} {φ : Fml C} (h : Proves .all Γ φ)
      (hφ : (Hyp.wrap Γ φ).hasTransfer = false) : ProvesC I Γ φ
  /-- `impRight`. -/
  | intro {Γ : List (Hyp C)} {a φ : Fml C} (h : ProvesC I (Γ ++ [.pre a]) φ) :
      ProvesC I Γ (.imp a φ)
  /-- A taclet that produces an update, on a statement that runs no other
  and pays nothing. -/
  | update {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {U : Upd C}
      (d : Taclet C (Hyp.fresh Γ (.and I.fml (.modal m (s :: ω) φ))) m s (.update U))
      (hs : s.forks = false)
      (h : ProvesC I (Γ ++ [.upd m U]) (.modal m ω φ)) : ProvesC I Γ (.modal m (s :: ω) φ)
  /-- A taclet that produces statements, on a statement that runs no other
  and pays nothing, when they pay nothing either. -/
  | unfold {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {P : Prog C}
      (d : Taclet C (Hyp.fresh Γ (.and I.fml (.modal m (s :: ω) φ))) m s (.unfold P))
      (hs : s.forks = false) (hP : Prog.hasTransfer P = false)
      (h : ProvesC I Γ (.modal m (P ++ ω) φ)) : ProvesC I Γ (.modal m (s :: ω) φ)
  /-- `unfold`, by a rule solkey does not have. -/
  | unfoldLean {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C}
      {P : Prog C} (d : LeanTaclet C (Hyp.fresh Γ (.and I.fml (.modal m (s :: ω) φ))) m s (.unfold P))
      (hs : s.forks = false) (hP : Prog.hasTransfer P = false)
      (h : ProvesC I Γ (.modal m (P ++ ω) φ)) : ProvesC I Γ (.modal m (s :: ω) φ)
  /-- **A callback taclet**: the invariant on exit, and the rest resumed after
  the callback, from any state the callee may leave in which the invariant
  holds (`{U} {havoc} (I → ⟨[ ω ]⟩ φ)`). -/
  | callback {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C} {φ : Fml C} {U : Upd C}
      (d : CallbackTaclet C m s U)
      (exit : ProvesC I Γ (.upd m U I.fml))
      (resume : ProvesC I (Γ ++ [.upd m U, .havoc, .pre I.fml]) (.modal m ω φ)) :
      ProvesC I Γ (.modal m (s :: ω) φ)
  /-- Leave the calculus: with no modality left anywhere in the sequent, what
  is left is proved about the callback reading. -/
  | close {Γ : List (Hyp C)} {φ : Fml C} (h : ValidC I (Hyp.wrap Γ φ))
      (hφ : (Hyp.wrap Γ φ).modalFree = true := by first | rfl | decide) : ProvesC I Γ φ

/-- A taclet in a context, its fresh names avoiding the invariant too. -/
theorem Taclet.avoids_in {I : Fml C} {Γ : List (Hyp C)} {m : Modality} {s : Stmt C} {ω : Prog C}
    {φ : Fml C} :
    let k := Hyp.fresh Γ (.and I (.modal m (s :: ω) φ))
    Avoids s.vars (freshVars k) ∧ Avoids (Prog.vars ω ++ φ.vars) (freshVars k) := by
  intro k
  have hv := freshVars_avoid (Nat.lt_succ_self (maxIdx (Hyp.wrap Γ (.and I (.modal m (s :: ω) φ))).vars))
  constructor <;> intro y hy <;>
    exact hv y (Hyp.vars_wrap Γ (by simp [Fml.vars, Prog.vars, hy]))

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
      (by simp only [holdsC] at hx; simp only [holds]
          cases hu : U.apply τ with
          | error _ => rw [hu] at hx; exact hx
          | ok a => rw [hu] at hx; exact (holdsC_iff_holds I.fml I.noTransfer).1 hx)
      (CbResume.of_holdsC I.noTransfer hr))
      Γ σ ih ihr
  | close h _ => exact h

/-- A derivation from the empty context proves validity with callbacks. -/
theorem ProvesC.valid {I : Invariant C} {φ : Fml C} (h : ProvesC I [] φ) : ValidC I φ := h.sound

end Solidity
