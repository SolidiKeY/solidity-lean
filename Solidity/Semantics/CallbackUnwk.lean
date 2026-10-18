import Solidity.Semantics.CallbackWk

/-!
# Callback execution reflects local weakening

Every callback execution of a weakened statement or program projects to an
execution of the original syntax. Together with `Semantics/CallbackWk.lean`,
the public `Stmt.exec_wk_iff` and `Prog.exec_wk_iff` give exact correspondence
through any typed local thinning. `Prog.exec_withoutAlias` recovers the original
execution after a fresh storage alias and the program's scope are removed.

The proofs cover the full current syntax, including paying loops, closed call
frames and all try branches. A proof-only loop view fixes the loop's indices
for induction; both directions relate it to the existing callback judgement.
No execution clause, interpreter representation or source syntax changes.
`Semantics/DeferredCorrespondence.lean` applies these laws to direct/captured
deferred operands. `Semantics/NativeDeferredCallback.lean` connects that result
to native receiver syntax and the callback calculus.
-/

namespace Solidity.CallbackUnwk

open Solidity.CallbackWk

variable {C : Contract}

def UWkS (J : StateInv C) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ {Δ : Ctx} (h : Thin Γ Δ) (τ : State C Δ) {o' : COut C τ.H (s.wk h).1},
    ExecS J τ (s.wk h).2.2 o' →
      ∃ o, ExecS J (τ.thin h) s o ∧ CWkRel (s.wk h).2.1 (TEnv.off h τ.env) o o'

def UWkP (J : StateInv C) {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prop :=
  ∀ {Δ : Ctx} (h : Thin Γ Δ) (τ : State C Δ) {o' : COut C τ.H (P.wk h).1},
    ExecP J τ (P.wk h).2.2 o' →
      ∃ o, ExecP J (τ.thin h) P o ∧ CWkRel (P.wk h).2.1 (TEnv.off h τ.env) o o'

theorem at_thin {Γ Δ : Ctx} (J : StateInv C) (h : Thin Γ Δ) (τ : State C Δ) :
    J.at (τ.thin h) ↔ J.at τ := Iff.rfl

theorem val_thin {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : State C Δ) {p : PrimTy} (v : Val C Γ p) :
    (v.wk h).evalT τ = v.evalT (τ.thin h) := by
  simpa only [State.lift_thin] using Val.evalT_wk h (τ.thin h) τ.env v

theorem det_unwk {Γ Γ' Δ : Ctx} (J : StateInv C) (s : Stmt C Γ Γ')
    (h : Thin Γ Δ) (τ : State C Δ) (hf : (s.wk h).2.2.forks = false) :
    ∃ o, ExecS J (τ.thin h) s o ∧
      CWkRel (s.wk h).2.1 (TEnv.off h τ.env) o (.ofRes ((s.wk h).2.2.run τ)) := by
  refine ⟨_, ExecS.det ((forks_stmt s h).symm.trans hf), ?_⟩
  have hr := CWkRel.of_res (Stmt.run_wk s h (τ.thin h) τ.env)
  dsimp only [State.lift, State.thin, State.withEnv] at hr
  rw [TEnv.put_thin h τ.env] at hr
  exact hr

/-- A proof-only view of the callback loop clauses, with the loop fixed as a parameter. -/
inductive LoopExec (J : StateInv C) {Γ Γ₁ : Ctx} (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) : (σ : State C Γ) → COut C σ.H Γ → Prop where
  | det {σ : State C Γ} : body.hasTransfer = false →
      LoopExec J a c body σ (.ofRes ((Stmt.loop a c body).run σ))
  | halt {σ : State C Γ} {e : THalt} : body.hasTransfer = true → c.evalT σ = .error e →
      LoopExec J a c body σ (.halt e)
  | exit {σ : State C Γ} : body.hasTransfer = true → c.evalT σ = .ok false →
      LoopExec J a c body σ (.ok ⟨σ, List.prefix_refl _⟩)
  | iter {σ : State C Γ} {v : Out C σ.H Γ₁} {o : COut C (v.st.drop body.ext).H Γ} :
      body.hasTransfer = true → c.evalT σ = .ok true → ExecP J σ body (.ok v) →
      LoopExec J a c body (v.st.drop body.ext) o →
        LoopExec J a c body σ (o.map (Out.cat (Out.drop body.ext v)))
  | stop {σ : State C Γ} {o : COut C σ.H Γ₁} :
      body.hasTransfer = true → c.evalT σ = .ok true → ExecP J σ body o → o.isOk = false →
        LoopExec J a c body σ (o.map (Out.drop body.ext))
  | diverge {σ : State C Γ} : body.hasTransfer = true → LoopExec J a c body σ (.halt .diverge)

def AsLoop (J : StateInv C) {Γ Γ' : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ')
    (o : COut C σ.H Γ') : Prop :=
  match s with
  | .loop a c body => LoopExec J a c body σ o
  | _ => True

theorem asLoop {J : StateInv C} {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'}
    {o : COut C σ.H Γ'} (he : ExecS J σ s o) : AsLoop J σ s o := by
  induction he using ExecS.rec (motive_2 := fun _ _ _ _ => True) with
  | @det Γ₀ Γ₁ τ s₀ hf =>
    cases s₀ <;> try trivial
    case loop a c body => exact .det hf
  | loopHalt ht hc => exact .halt ht hc
  | loopExit ht hc => exact .exit ht hc
  | loopIter ht hc hp hl _ ih => exact .iter ht hc hp ih
  | loopStop ht hc hp hn _ => exact .stop ht hc hp hn
  | loopDiverge ht => exact .diverge ht
  | _ => trivial

theorem loop_unwk {Γ Γ₁ : Ctx} (J : StateInv C) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (hb : UWkP J body) : UWkS J (.loop a c body) := by
  intro Δ h τ o' he
  have hl : LoopExec J (a.wk h) (c.wk h) (body.wk h).2.2 τ o' := asLoop he
  clear he
  induction hl with
  | @det τ ht => exact det_unwk J _ h τ ht
  | @halt τ err ht hc =>
    exact ⟨_, .loopHalt ((hasTransfer_prog body h).symm.trans ht)
      ((val_thin h τ c).symm.trans hc), rfl⟩
  | @exit τ ht hc =>
    refine ⟨_, ExecS.loopExit ((hasTransfer_prog body h).symm.trans ht)
      ((val_thin h τ c).symm.trans hc), ?_⟩
    have hr := CWkRel.lift_ok h τ.env (⟨τ.thin h, List.prefix_refl _⟩ : Out C τ.H Γ)
    simp only [Out.lift, TEnv.wk_self] at hr
    dsimp only [State.lift, State.thin, State.withEnv] at hr
    rw [TEnv.put_thin h τ.env] at hr
    exact hr
  | @iter τ v o ht hc hp hl ih =>
    obtain ⟨u, hu, hr⟩ := hb h τ hp
    cases u with
    | halt _ => cases hr
    | violated => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      have ho := Prog.wk_over body h
      obtain ⟨u', hu', hr'⟩ := ih
      dsimp only [State.thin, State.drop, State.lift, State.withEnv] at hu' hr'
      rw [(ho.tenv b.st.env d').1,
        TEnv.thin_put h (TEnv.drop body.ext b.st.env) (TEnv.drop (body.wk h).2.2.ext d')] at hu'
      rw [(ho.tenv b.st.env d').1,
        TEnv.off_put h (TEnv.drop body.ext b.st.env) (TEnv.drop (body.wk h).2.2.ext d')] at hr'
      exact ⟨_, ExecS.loopIter ((hasTransfer_prog body h).symm.trans ht)
        ((val_thin h τ c).symm.trans hc) hu hu',
        CWkRel.cat (Out.drop body.ext b) (TEnv.drop (body.wk h).2.2.ext d')
          ((ho.tenv b.st.env d').2.trans hd) hr'⟩
  | @stop τ o ht hc hp hn =>
    obtain ⟨u, hu, hr⟩ := hb h τ hp
    exact ⟨_, ExecS.loopStop ((hasTransfer_prog body h).symm.trans ht)
      ((val_thin h τ c).symm.trans hc) hu ((CWkRel.isOk hr).symm.trans hn),
      CWkRel.drop (Prog.wk_over body h) hr⟩
  | @diverge τ ht => exact ⟨_, .loopDiverge ((hasTransfer_prog body h).symm.trans ht), rfl⟩

theorem args_thin {Γ Δ ps : Ctx} (h : Thin Γ Δ) (τ : State C Δ) (args : Args C Γ ps) :
    (args.wk h).evalT τ = args.evalT (τ.thin h) := by
  have hr := Args.evalT_wk h (τ.thin h) τ.env args
  dsimp only [State.lift, State.thin, State.withEnv] at hr
  rw [TEnv.put_thin h τ.env] at hr
  exact hr

theorem call_cases {Γ Γ' ps rs Γf : Ctx} (J : StateInv C) (σ : State C Γ)
    (f : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf)
    {o : COut C σ.H Γ'} (he : ExecS J σ (.call f args ret body) o) :
    (∃ err, args.evalT σ = .error err ∧ o = .halt err) ∨
    (∃ a u, args.evalT σ = .ok a ∧ ExecP J (ret.enterT (σ.withEnv a)).st body u ∧
      o = u.map (TRun.callLeave ret body.ext σ (ret.enterT (σ.withEnv a)))) := by
  cases he with
  | det hf => cases hf
  | callArgs ha => exact .inl ⟨_, ha, rfl⟩
  | callBody ha hp => exact .inr ⟨_, _, ha, hp, rfl⟩

theorem call_unwk {Γ Γ' ps rs Γf : Ctx} (J : StateInv C) (f : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) : UWkS J (.call f args ret body) := by
  intro Δ h τ o' he
  change ExecS J τ (.call f (args.wk h) (ret.wk h).2.2 body) o' at he
  rcases call_cases J τ f (args.wk h) (ret.wk h).2.2 body he with
    ⟨err, ha, rfl⟩ | ⟨a, u, ha, hp, rfl⟩
  · exact ⟨_, ExecS.callArgs (f := f) (ret := ret) (body := body)
      ((args_thin h τ args).symm.trans ha), rfl⟩
  · let ret₀ := ret
    cases ret <;> have hs : ExecP J (ret₀.enterT ((τ.thin h).withEnv a)).st body u := hp
    all_goals
      have hr := callLeave_wk h (τ.thin h) τ.env ret₀ body.ext (ret₀.enterT ((τ.thin h).withEnv a)) u
      dsimp only [State.lift, State.thin, State.withEnv] at hr
      rw [TEnv.put_thin h τ.env] at hr
      exact ⟨_, ExecS.callBody (J := J) (σ := τ.thin h) (f := f) (args := args)
        (ret := ret₀) (body := body) ((args_thin h τ args).symm.trans ha) hs, hr⟩

theorem thin_self {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : State C Δ) :
    CWkRel h (TEnv.off h τ.env) (.ok ⟨τ.thin h, List.prefix_refl _⟩) (.ok ⟨τ, List.prefix_refl _⟩) := by
  refine ⟨τ.env, (offWk_self _ _).symm, ?_⟩
  dsimp only [State.thin, State.lift, State.withEnv]
  rw [TEnv.put_thin h τ.env]

theorem havoc_rel {Γ Δ : Ctx} {H : HTy} {h : Thin Γ Δ}
    {off : List ((t : LTy) × t.TDenote C H)} {a : Out C H Γ} {b : Out C H Δ}
    (hr : CWkRel h off (.ok a) (.ok b)) (st : Storage C) (nt : Ledger) :
    CWkRel h off (.ok ⟨a.st.havoc st nt, a.ext⟩) (.ok ⟨b.st.havoc st nt, b.ext⟩) := by
  obtain ⟨d', hd, rfl⟩ := hr
  exact ⟨d', hd, rfl⟩

theorem local_rel {Γ Δ : Ctx} {H : HTy} {h : Thin Γ Δ}
    {off : List ((t : LTy) × t.TDenote C H)} {a : Out C H Γ} {b : Out C H Δ}
    (hr : CWkRel h off (.ok a) (.ok b)) (i : Idx Γ (.val .bool)) (v : Bool) :
    CWkRel h off (.ok ⟨a.st.setLocal i v, a.ext⟩) (.ok ⟨b.st.setLocal (i.wk h) v, b.ext⟩) := by
  obtain ⟨d', hd, rfl⟩ := hr
  refine ⟨d', hd, ?_⟩
  dsimp only [State.setLocal, State.lift, State.withEnv]
  rw [TEnv.set_put h i v a.st.env d']

theorem inv_rel {Γ Δ : Ctx} {H : HTy} {h : Thin Γ Δ}
    {off : List ((t : LTy) × t.TDenote C H)} {a : Out C H Γ} {b : Out C H Δ}
    (hr : CWkRel h off (.ok a) (.ok b)) (J : StateInv C) : J.at a.st ↔ J.at b.st := by
  obtain ⟨d', hd, rfl⟩ := hr
  exact Iff.rfl

theorem transfer_run {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : State C Δ) (r amt : Val C Γ .uint) :
    TWkRel h (TEnv.off h τ.env) (TRun.transfer r amt (τ.thin h))
      (TRun.transfer (r.wk h) (amt.wk h) τ) := by
  have hr := TWkRel.of_eq (TRun.transfer_wk h (τ.thin h) τ.env r amt)
  dsimp only [State.lift, State.thin, State.withEnv] at hr
  rw [TEnv.put_thin h τ.env] at hr
  exact hr

theorem transfer_error {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : State C Δ) (r amt : Val C Γ .uint)
    {err : THalt} (hp : TRun.transfer (r.wk h) (amt.wk h) τ = .error err) :
    TRun.transfer r amt (τ.thin h) = .error err := by
  have hr := transfer_run h τ r amt
  rw [hp] at hr
  cases ha : TRun.transfer r amt (τ.thin h) with
  | error e => rw [ha] at hr; cases hr; rfl
  | ok a => rw [ha] at hr; cases hr

theorem transfer_ok {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : State C Δ) (r amt : Val C Γ .uint)
    {b : Out C τ.H Δ} (hp : TRun.transfer (r.wk h) (amt.wk h) τ = .ok b) :
    ∃ a, TRun.transfer r amt (τ.thin h) = .ok a ∧
      CWkRel h (TEnv.off h τ.env) (.ok a) (.ok b) := by
  have hr := transfer_run h τ r amt
  rw [hp] at hr
  cases ha : TRun.transfer r amt (τ.thin h) with
  | error e => rw [ha] at hr; cases hr
  | ok a => rw [ha] at hr; exact ⟨a, rfl, hr⟩

theorem transfer_unwk {Γ : Ctx} (J : StateInv C) (r amt : Val C Γ .uint) :
    UWkS J (.transfer r amt) := by
  intro Δ h τ o' he
  cases he with
  | det hf => exact det_unwk J _ h τ hf
  | transferHalt hp => exact ⟨_, .transferHalt (transfer_error h τ r amt hp), rfl⟩
  | @transferViolated _ _ _ _ b hp hj =>
    obtain ⟨a, ha, hr⟩ := transfer_ok h τ r amt hp
    exact ⟨_, .transferViolated ha (fun hk => hj ((inv_rel hr J).mp hk)), trivial⟩
  | @transferResume _ _ _ _ b st nt hp hj hk =>
    obtain ⟨a, ha, hr⟩ := transfer_ok h τ r amt hp
    have hr' := havoc_rel hr st nt
    exact ⟨_, ExecS.transferResume ha ((inv_rel hr J).mpr hj) ((inv_rel hr' J).mpr hk), hr'⟩

theorem send_unwk {Γ : Ctx} (J : StateInv C) (pv : Idx Γ (.val .bool))
    (r amt : Val C Γ .uint) : UWkS J (.send pv r amt) := by
  intro Δ h τ o' he
  cases he with
  | det hf => exact det_unwk J _ h τ hf
  | sendHalt hp => exact ⟨_, .sendHalt (transfer_error h τ r amt hp), rfl⟩
  | sendFailed hp =>
    obtain ⟨a, ha, hr⟩ := transfer_ok h τ r amt hp
    exact ⟨_, ExecS.sendFailed ha, local_rel (thin_self h τ) pv false⟩
  | sendViolated hp hj =>
    obtain ⟨a, ha, hr⟩ := transfer_ok h τ r amt hp
    exact ⟨_, .sendViolated ha (fun hk => hj ((inv_rel hr J).mp hk)), trivial⟩
  | @sendResume _ _ _ _ _ b st nt hp hj hk =>
    obtain ⟨a, ha, hr⟩ := transfer_ok h τ r amt hp
    have hr' := havoc_rel hr st nt
    exact ⟨_, ExecS.sendResume ha ((inv_rel hr J).mpr hj) ((inv_rel hr' J).mpr hk),
      local_rel hr' pv true⟩

theorem ite_unwk {Γ Γ₁ Γ₂ : Ctx} (J : StateInv C) (c : Val C Γ .bool)
    (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) (ht : UWkP J thn) (hels : UWkP J els) :
    UWkS J (.ite c thn els) := by
  intro Δ h τ o' he
  cases he with
  | det hf => exact det_unwk J _ h τ hf
  | iteHalt hc => exact ⟨_, .iteHalt ((val_thin h τ c).symm.trans hc), rfl⟩
  | iteThen hc hp =>
    obtain ⟨u, hu, hr⟩ := ht h τ hp
    exact ⟨_, ExecS.iteThen ((val_thin h τ c).symm.trans hc) hu,
      CWkRel.drop (Prog.wk_over thn h) hr⟩
  | iteElse hc hp =>
    obtain ⟨u, hu, hr⟩ := hels h τ hp
    exact ⟨_, ExecS.iteElse ((val_thin h τ c).symm.trans hc) hu,
      CWkRel.drop (Prog.wk_over els h) hr⟩

theorem block_unwk {Γ Γ₁ : Ctx} (J : StateInv C) (body : Prog C Γ Γ₁) (hb : UWkP J body) :
    UWkS J (.block body) := by
  intro Δ h τ o' he
  cases he with
  | det hf => exact det_unwk J _ h τ hf
  | block ht hp =>
    obtain ⟨u, hu, hr⟩ := hb h τ hp
    exact ⟨_, ExecS.block ((hasTransfer_prog body h).symm.trans ht) hu,
      CWkRel.drop (Prog.wk_over body h) hr⟩

theorem callReceiver_unwk {Γ ps Γf : Ctx} {E : Ty} (J : StateInv C) (f : Name)
    (args : Args C Γ ps) (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (op : ReceiverOp C Γ E) : UWkS J (.callReceiver f args r body op) := by
  intro Δ h τ o' he
  cases he with
  | det hf => exact det_unwk J _ h τ hf
  | callReceiver hc =>
    obtain ⟨u, hu, hr⟩ := call_unwk J f args (.storage _ r) body h τ hc
    exact ⟨_, ExecS.callReceiver hu, receiverOp_wk h op hr⟩

/-- Every weakened callback run of `f().push(i++)` projects to the original caller. -/
theorem callReceiverPush_unwk {Γ ps Γf Γv : Ctx} {E : Ty} (J : StateInv C) (f : Name)
    (args : Args C Γ ps) (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (code : Prog C Γ Γv) (value : Src C Γv E) (hb : UWkP J code) :
    UWkS J (.callReceiverPush f args r body code value) := by
  intro Δ h τ o' he
  cases he with
  | det hf => exact det_unwk J _ h τ hf
  | @callReceiverPush _ _ _ _ _ _ _ _ _ _ _ _ a ref u hc hp hu =>
    obtain ⟨v, hv, hr⟩ := call_unwk J f args (.storage _ r) body h τ hc
    cases v with
    | halt _ => cases hr
    | violated => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      obtain ⟨u', hu', hr'⟩ := hb h _ hu
      dsimp only [State.drop, State.thin, State.lift, State.withEnv, Stmt.wk, CallRet.wk,
        TEnv.drop, TEnv.put] at hu' hr'
      rw [TEnv.thin_put h b.st.env.2 d'.2] at hu'
      rw [TEnv.off_put h b.st.env.2 d'.2] at hr'
      exact ⟨_, ExecS.callReceiverPush hv hp hu',
        CWkRel.cat b d' hd (pushPrefix_wk code value ref h hr')⟩
  | callReceiverPushUnset hc hp =>
    obtain ⟨v, hv, hr⟩ := call_unwk J f args (.storage _ r) body h τ hc
    cases v with
    | halt _ => cases hr
    | violated => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      exact ⟨_, ExecS.callReceiverPushUnset hv hp, rfl⟩
  | callReceiverPushHalt hc =>
    obtain ⟨v, hv, hr⟩ := call_unwk J f args (.storage _ r) body h τ hc
    cases v <;> cases hr
    exact ⟨_, ExecS.callReceiverPushHalt hv, rfl⟩
  | callReceiverPushViolated hc =>
    obtain ⟨v, hv, hr⟩ := call_unwk J f args (.storage _ r) body h τ hc
    cases v <;> try cases hr
    exact ⟨_, ExecS.callReceiverPushViolated hv, trivial⟩

theorem thin_keepAll {Γ Δ : Ctx} {H : HTy} (h : Thin Γ Δ) :
    (ρ : Ctx) → (r : TEnv C H ρ) → (d : TEnv C H Δ) →
      TEnv.thin (Thin.keepAll ρ h) (TEnv.append ρ r d) = TEnv.append ρ r (TEnv.thin h d)
  | [], r, d => rfl
  | t :: ρ, r, d => by
    change (r.1, TEnv.thin (Thin.keepAll ρ h) (TEnv.append ρ r.2 d)) =
      (r.1, TEnv.append ρ r.2 (TEnv.thin h d))
    rw [thin_keepAll h ρ r.2 d]

theorem tryCall_unwk {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (J : StateInv C) (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄)
    (hok : UWkP J ok) (herr : UWkP J err) (hpnc : UWkP J pnc) (hoth : UWkP J other) :
    UWkS J (.tryCall call rets ok err code pnc other) := by
  intro Δ h τ o' he
  cases he with
  | det hf => exact det_unwk J _ h τ hf
  | tryRevert => exact ⟨_, .tryRevert, rfl⟩
  | tryDecode hd => exact ⟨_, .tryDecode hd, rfl⟩
  | tryViolated hj => exact ⟨_, .tryViolated (fun hk => hj ((at_thin J h τ).mp hk)), trivial⟩
  | tryOk hj hk hd hp =>
    rename_i st nt vs rest r u'
    obtain ⟨u, hu, hr⟩ := hok (Thin.keepAll ρ h)
      ((τ.havoc st nt).withEnv (TEnv.append ρ r τ.env)) hp
    dsimp only [State.thin, State.withEnv, State.havoc] at hu
    rw [thin_keepAll h ρ r τ.env] at hu
    refine ⟨_, ExecS.tryOk (J := J) (st := st) (nt := nt) (vs := vs) (rest := rest)
      ((at_thin J h τ).mpr hj) ((at_thin J h (τ.havoc st nt)).mpr hk) hd hu, ?_⟩
    simpa only [State.withEnv, TEnv.off_keepAll] using
      (CWkRel.drop ((Thin.Over.append h ρ).trans (Prog.wk_over ok (Thin.keepAll ρ h))) hr)
  | tryError hp =>
    obtain ⟨u, hu, hr⟩ := herr h τ hp
    exact ⟨_, ExecS.tryError hu, CWkRel.drop (Prog.wk_over err h) hr⟩
  | tryPanic hp =>
    rename_i v u'
    obtain ⟨u, hu, hr⟩ := hpnc (Thin.keepAll κ h)
      (τ.withEnv (TEnv.append κ (code.decodeT v) τ.env)) hp
    dsimp only [State.thin, State.withEnv] at hu
    rw [thin_keepAll h κ (code.decodeT v) τ.env] at hu
    refine ⟨_, ExecS.tryPanic (v := v) hu, ?_⟩
    simpa only [State.withEnv, TEnv.off_keepAll] using
      (CWkRel.drop ((Thin.Over.append h κ).trans (Prog.wk_over pnc (Thin.keepAll κ h))) hr)
  | tryOther hp =>
    obtain ⟨u, hu, hr⟩ := hoth h τ hp
    exact ⟨_, ExecS.tryOther hu, CWkRel.drop (Prog.wk_over other h) hr⟩

theorem cons_cases {Γ Γ₁ Γ₂ : Ctx} (J : StateInv C) (σ : State C Γ)
    (s : Stmt C Γ Γ₁) (P : Prog C Γ₁ Γ₂) {o : COut C σ.H Γ₂}
    (he : ExecP J σ (.cons s P) o) :
    (∃ a b, ExecS J σ s (.ok a) ∧ ExecP J a.st P b ∧ o = b.map (Out.cat a)) ∨
      (∃ err, ExecS J σ s (.halt err) ∧ o = .halt err) ∨
        (ExecS J σ s .violated ∧ o = .violated) := by
  cases he with
  | cons hs hp => exact .inl ⟨_, _, hs, hp, rfl⟩
  | halt hs => exact .inr (.inl ⟨_, hs, rfl⟩)
  | violated hs => exact .inr (.inr ⟨hs, rfl⟩)

mutual

theorem stmt_unwk (J : StateInv C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → UWkS J s
  | _, _, .ite c thn els => ite_unwk J c thn els (prog_unwk J thn) (prog_unwk J els)
  | _, _, .block body => block_unwk J body (prog_unwk J body)
  | _, _, .loop a c body => loop_unwk J a c body (prog_unwk J body)
  | _, _, .transfer r a => transfer_unwk J r a
  | _, _, .send pv r a => send_unwk J pv r a
  | _, _, .call f args ret body => call_unwk J f args ret body
  | _, _, .callReceiver f args r body op => callReceiver_unwk J f args r body op
  | _, _, .callReceiverPush f args r body code value =>
    callReceiverPush_unwk J f args r body code value (prog_unwk J code)
  | _, _, .tryCall call rets ok err code pnc other =>
    tryCall_unwk J call rets ok err code pnc other
      (prog_unwk J ok) (prog_unwk J err) (prog_unwk J pnc) (prog_unwk J other)
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal ..
  | _, _, .declLocal .. | _, _, .declStorage ..
  | _, _, .opAssign .. | _, _, .incDec ..
  | _, _, .assignIncDec .. | _, _, .assignLocalPush ..
  | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .push .. | _, _, .pop ..
  | _, _, .declMem .. | _, _, .rebindMem ..
  | _, _, .assignFromMem .. | _, _, .assignMem ..
  | _, _, .delete .. | _, _, .deleteMem .. | _, _, .assignNew ..
  | _, _, .require .. | _, _, .assert .. | _, _, .revert => by
    intro h τ o' he
    rw [he.eq_run rfl]
    exact det_unwk J _ h τ rfl

theorem prog_unwk (J : StateInv C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → UWkP J P
  | _, _, .nil => by
    intro h τ o' he
    cases he
    exact ⟨_, .nil, thin_self h τ⟩
  | _, _, .cons s P => by
    intro h τ o' he
    change ExecP J τ (.cons (s.wk h).2.2 (P.wk (s.wk h).2.1).2.2) o' at he
    rcases cons_cases J τ _ _ he with ⟨a', b', hs, hp, rfl⟩ | ⟨err, hs, rfl⟩ | ⟨hs, rfl⟩
    · obtain ⟨a, ha, hra⟩ := stmt_unwk J s h τ hs
      cases a with
      | halt _ => cases hra
      | violated => cases hra
      | ok a =>
        obtain ⟨d', hd, rfl⟩ := hra
        obtain ⟨u, hu, hr⟩ := prog_unwk J P (s.wk h).2.1 (a.st.lift (s.wk h).2.1 d') hp
        dsimp only [State.thin, State.lift, State.withEnv] at hu hr
        rw [TEnv.thin_put (s.wk h).2.1 a.st.env d'] at hu
        rw [TEnv.off_put (s.wk h).2.1 a.st.env d'] at hr
        exact ⟨_, ExecP.cons ha hu, CWkRel.cat a d' hd hr⟩
    · obtain ⟨u, hu, hr⟩ := stmt_unwk J s h τ hs
      cases u with
      | ok _ => cases hr
      | violated => cases hr
      | halt e => cases hr; exact ⟨_, .halt hu, rfl⟩
    · obtain ⟨u, hu, hr⟩ := stmt_unwk J s h τ hs
      cases u with
      | ok _ => cases hr
      | halt _ => cases hr
      | violated => exact ⟨_, .violated hu, trivial⟩

end

theorem _root_.Solidity.CallbackWk.CWkRel.right_unique {Γ Δ : Ctx} {H : HTy}
    {h : Thin Γ Δ} {off : List ((t : LTy) × t.TDenote C H)}
    {o : COut C H Γ} {u v : COut C H Δ}
    (hu : CWkRel h off o u) (hv : CWkRel h off o v) : u = v := by
  cases o <;> cases u <;> cases v
  all_goals first | exact False.elim hu | exact False.elim hv | skip
  case halt.halt.halt => exact congrArg COut.halt (hu.symm.trans hv)
  case violated.violated.violated => rfl
  case ok.ok.ok a b c =>
    obtain ⟨d, hd, rfl⟩ := hu
    obtain ⟨d', hd', rfl⟩ := hv
    congr 2
    exact State.lift_congr h a.st (hd.trans hd'.symm)

theorem _root_.Solidity.Stmt.exec_unwk {Γ Γ' Δ : Ctx} (J : StateInv C) (s : Stmt C Γ Γ')
    (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {o' : COut C σ.H (s.wk h).1} (he : ExecS J (σ.lift h d) (s.wk h).2.2 o') :
    ∃ o, ExecS J σ s o ∧ CWkRel (s.wk h).2.1 (TEnv.off h d) o o' := by
  obtain ⟨o, ho, hr⟩ := stmt_unwk J s h (σ.lift h d) he
  dsimp only [State.thin, State.lift, State.withEnv] at ho hr
  rw [TEnv.thin_put h σ.env d] at ho
  exact ⟨o, ho, (TEnv.off_put h σ.env d) ▸ hr⟩

theorem _root_.Solidity.Prog.exec_unwk {Γ Γ' Δ : Ctx} (J : StateInv C) (P : Prog C Γ Γ')
    (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {o' : COut C σ.H (P.wk h).1} (he : ExecP J (σ.lift h d) (P.wk h).2.2 o') :
    ∃ o, ExecP J σ P o ∧ CWkRel (P.wk h).2.1 (TEnv.off h d) o o' := by
  obtain ⟨o, ho, hr⟩ := prog_unwk J P h (σ.lift h d) he
  dsimp only [State.thin, State.lift, State.withEnv] at ho hr
  rw [TEnv.thin_put h σ.env d] at ho
  exact ⟨o, ho, (TEnv.off_put h σ.env d) ▸ hr⟩

theorem _root_.Solidity.Stmt.exec_wk_iff {Γ Γ' Δ : Ctx} (J : StateInv C) (s : Stmt C Γ Γ')
    (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {o' : COut C σ.H (s.wk h).1} :
    ExecS J (σ.lift h d) (s.wk h).2.2 o' ↔
      ∃ o, ExecS J σ s o ∧ CWkRel (s.wk h).2.1 (TEnv.off h d) o o' :=
  ⟨Stmt.exec_unwk J s h σ d, fun ⟨_, ho, hr⟩ =>
    let ⟨_, hu, hru⟩ := Stmt.exec_wk J s h σ d ho
    (hr.right_unique hru).symm ▸ hu⟩

theorem _root_.Solidity.Prog.exec_wk_iff {Γ Γ' Δ : Ctx} (J : StateInv C) (P : Prog C Γ Γ')
    (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {o' : COut C σ.H (P.wk h).1} :
    ExecP J (σ.lift h d) (P.wk h).2.2 o' ↔
      ∃ o, ExecP J σ P o ∧ CWkRel (P.wk h).2.1 (TEnv.off h d) o o' :=
  ⟨Prog.exec_unwk J P h σ d, fun ⟨_, ho, hr⟩ =>
    let ⟨_, hu, hru⟩ := Prog.exec_wk J P h σ d ho
    (hr.right_unique hru).symm ▸ hu⟩

/-- Recover a callback execution after removing a fresh storage alias. -/
theorem _root_.Solidity.Prog.exec_withoutAlias {Γ Γ' : Ctx} {R : RefTy} (J : StateInv C)
    (P : Prog C Γ Γ') (σ : State C Γ) (p : Option (SRef C (.ref R)))
    {o' : COut C σ.H (P.wk (.drop (t := .alias R) .refl)).1}
    (he : ExecP J (σ.push (t := .alias R) p) (P.wk (.drop .refl)).2.2 o') :
    ∃ o, ExecP J σ P o ∧
      o'.map (Out.drop (P.wk (.drop .refl)).2.2.ext) =
        (o.map (Out.drop P.ext)).map (fun x => ⟨x.st.push (t := .alias R) p, x.ext⟩) := by
  obtain ⟨o, ho, hr⟩ := Prog.exec_unwk J P (.drop (t := .alias R) .refl) σ (p, σ.env) he
  refine ⟨o, ho, ?_⟩
  simpa only [Out.lift, State.lift, State.push, TEnv.put, TEnv.wk, LTy.TDenote.wk] using
    (CWkRel.drop (Prog.wk_over P (.drop .refl)) hr).eq_lifted

end Solidity.CallbackUnwk
