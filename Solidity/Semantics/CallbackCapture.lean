import Solidity.Semantics.CallbackUnwk

/-!
# A capture runs as its statement, with callbacks

KeY captures a non-simple operand into a fresh local before the statement
that reads it (`ifElseUnfold`: `if (nse) …` becomes `bool se = nse; if (se)
…`).  The capture is a declaration of a value: it calls no function and
hands control to nobody, whatever the statement around it does.  So a
capture keeps every run with callbacks of its statement, even where the
statement's own branches call back (`Stmt.CapturesAs`, read by
`ProvesC.capture`, `Calculus/Callback.lean`): the statement's run is the
captured program's, its fresh local popped.  This is what the rule needs,
not that nothing in the captured program calls back (`ProvesC.unfold`'s
side conditions).

One lemma per capture shape whose rest may call back: an `if`'s condition
(`ifElseUnfold`), a `transfer`'s and a `send`'s operands
(`transfer_unfold_…`, `send_unfold_…`).  A `require`'s, an `assert`'s and a
ternary's conditions leave a statement that calls nobody, so
`ProvesC.unfold` takes them already.
-/

namespace Solidity

variable {C : Contract}

/-- **`s` runs, with callbacks, as the program `P` that captures its
operands**, `P`'s fresh locals popped (`e`): every run of `s` is one of
`P`'s, or a halt the modality `m` accepts that is no panic (a loop's
divergence, under the box). -/
def Stmt.CapturesAs (pay : Bool) (m : Modality) {Γ Γ' Γ'' : Ctx} (s : Stmt C Γ Γ')
    (P : Prog C Γ Γ'') (e : Ext Γ' Γ'') : Prop :=
  ∀ (J : StateInv C), J.pay = pay → ∀ (σ : State C Γ) (o : COut C σ.H Γ'), ExecS J σ s o →
    (∃ err, o = .halt err ∧ m.onTHalt err ∧ err ≠ .panic) ∨
      ∃ o', ExecP J σ P o' ∧ o'.map (Out.drop e) = o

namespace CallbackCapture

variable {J : StateInv C}

/-- A one-statement program runs as its statement. -/
theorem execP_single {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} {o : COut C σ.H Γ'}
    (h : ExecS J σ s o) : ExecP J σ (.cons s .nil) o := by
  cases o with
  | ok a => exact .cons h .nil
  | halt err => exact .halt h
  | violated => exact .violated h

/-- A fresh value local on top keeps every callback run of a program, and
its scope's end. -/
theorem prog_afterPush {Γ Γ' : Ctx} {p : PrimTy} (P : Prog C Γ Γ')
    (σ : State C Γ) (v : p.Denote) {o : COut C σ.H Γ'} (he : ExecP J σ P o) :
    ∃ o', ExecP J (σ.push (t := .val p) v) (P.wk (.drop .refl)).2.2 o' ∧
      o'.map (Out.drop (P.wk (.drop .refl)).2.2.ext) =
        (o.map (Out.drop P.ext)).map (fun x => ⟨x.st.push (t := .val p) v, x.ext⟩) := by
  obtain ⟨u, hu, hr⟩ := CallbackWk.prog_wk J P (.drop (t := .val p) .refl) σ (v, σ.env) he
  refine ⟨u, hu, ?_⟩
  simpa only [Out.lift, State.lift, State.push, TEnv.put, TEnv.wk, LTy.TDenote.wk] using
    (CallbackWk.CWkRel.drop (Prog.wk_over P (.drop .refl)) hr).eq_lifted

end CallbackCapture

open CallbackCapture in
/-- **`ifElseUnfold` with callbacks**: `if (nse) S₁ else S₂` runs as
`bool se = nse; if (se) S₁ else S₂`, whatever its branches call. -/
theorem Stmt.CapturesAs.ite {pay : Bool} {m : Modality} {Γ Γ₁ Γ₂ : Ctx} {c : Val C Γ .bool} {x : Var}
    {thn : Prog C Γ Γ₁} {els : Prog C Γ Γ₂} :
    (Stmt.ite c thn els).CapturesAs pay m
      (.cons (.declLocal .bool x (some c))
        (.cons (.ite (.simple (.local .here)) (thn.wk (.drop .refl)).2.2
          (els.wk (.drop .refl)).2.2) .nil)) (.push .refl) := by
  intro J _ σ o he
  cases he with
  | det hf => exact nomatch hf
  | iteHalt hc =>
    rename_i e
    have hr : (Stmt.declLocal .bool x (some c)).run σ = .error e := by
      show TRun.declLocal .bool (some c) σ = _; simp only [TRun.declLocal, hc]; rfl
    have hd := ExecS.det (J := J) (σ := σ) (s := Stmt.declLocal .bool x (some c)) rfl
    rw [hr] at hd
    exact .inr ⟨.halt e, .halt hd, rfl⟩
  | iteThen hc hp =>
    rename_i o₀
    have hr : (Stmt.declLocal .bool x (some c)).run σ =
        .ok ⟨σ.push (t := .val .bool) true, List.prefix_refl _⟩ := by
      show TRun.declLocal .bool (some c) σ = _; simp only [TRun.declLocal, hc]; rfl
    have hd := ExecS.det (J := J) (σ := σ) (s := Stmt.declLocal .bool x (some c)) rfl
    rw [hr] at hd
    obtain ⟨u, hu, hue⟩ := prog_afterPush (p := .bool) thn σ true hp
    have hi : ExecS J (σ.push (t := .val .bool) true)
        (.ite (.simple (.local .here)) (thn.wk (.drop .refl)).2.2 (els.wk (.drop .refl)).2.2)
        (u.map (Out.drop (thn.wk (.drop .refl)).2.2.ext)) := .iteThen rfl hu
    refine .inr ⟨_, .cons hd (execP_single hi), ?_⟩
    rw [hue]
    cases o₀ <;> rfl
  | iteElse hc hp =>
    rename_i o₀
    have hr : (Stmt.declLocal .bool x (some c)).run σ =
        .ok ⟨σ.push (t := .val .bool) false, List.prefix_refl _⟩ := by
      show TRun.declLocal .bool (some c) σ = _; simp only [TRun.declLocal, hc]; rfl
    have hd := ExecS.det (J := J) (σ := σ) (s := Stmt.declLocal .bool x (some c)) rfl
    rw [hr] at hd
    obtain ⟨u, hu, hue⟩ := prog_afterPush (p := .bool) els σ false hp
    have hi : ExecS J (σ.push (t := .val .bool) false)
        (.ite (.simple (.local .here)) (thn.wk (.drop .refl)).2.2 (els.wk (.drop .refl)).2.2)
        (u.map (Out.drop (els.wk (.drop .refl)).2.2.ext)) := .iteElse rfl hu
    refine .inr ⟨_, .cons hd (execP_single hi), ?_⟩
    rw [hue]
    cases o₀ <;> rfl

namespace CallbackCapture

/-- A loop's annotation (its unwinding bound, its invariant) does not
change its runs with callbacks. -/
theorem loop_ann {J : StateInv C} {Γ Γ₁ : Ctx} {a a' : LoopAnn C Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Γ₁} (hb : body.callsBack J.pay = true) {σ : State C Γ}
    {o : COut C σ.H Γ} (h : CallbackUnwk.LoopExec J a c body σ o) :
    ExecS J σ (.loop a' c body) o := by
  induction h with
  | det hf => rw [hb] at hf; cases hf
  | halt ht hc => exact .loopHalt ht hc
  | exit ht hc => exact .loopExit ht hc
  | iter ht hc hp _ ih => exact .loopIter ht hc hp ih
  | stop ht hc hp hn => exact .loopStop ht hc hp hn
  | diverge ht => exact .loopDiverge ht

end CallbackCapture

open CallbackCapture in
/-- **`whileUnwind` with callbacks**, a body that calls back: `while (c) S`
runs as `if (c) { S; while (c) S; }`, or diverges, which the box accepts. -/
theorem Stmt.CapturesAs.loop {pay : Bool} {Γ Γ₁ : Ctx} {a a' : LoopAnn C Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Γ₁} (hb : body.callsBack pay = true) :
    (Stmt.loop a c body).CapturesAs pay .box
      (.cons (.ite c (.cons (.block body) (.cons (.loop a' c body) .nil)) .nil) .nil) .refl := by
  intro J hJ σ o he
  subst hJ
  have hl : CallbackUnwk.LoopExec J a c body σ o := CallbackUnwk.asLoop he
  cases hl with
  | det hf => rw [hb] at hf; cases hf
  | halt _ hc => exact .inr ⟨_, .halt (.iteHalt hc), rfl⟩
  | exit _ hc => exact .inr ⟨_, execP_single (.iteElse hc .nil), rfl⟩
  | iter _ hc hp hl =>
    rename_i v o₀
    have hi := ExecS.iteThen (J := J) (els := (.nil : Prog C Γ Γ)) hc
      (.cons (.block hb hp) (execP_single (loop_ann (a' := a') hb hl)))
    refine .inr ⟨_, execP_single hi, ?_⟩
    cases o₀ <;> rfl
  | stop _ hc hp hn =>
    rename_i o₀
    cases o₀ with
    | ok => cases hn
    | halt err =>
      exact .inr ⟨_, execP_single (.iteThen (els := (.nil : Prog C Γ Γ)) hc
        (.halt (.block hb hp))), rfl⟩
    | violated =>
      exact .inr ⟨_, execP_single (.iteThen (els := (.nil : Prog C Γ Γ)) hc
        (.violated (.block hb hp))), rfl⟩
  | diverge _ => exact .inl ⟨_, rfl, trivial, nofun⟩

end Solidity
