import Solidity.Semantics.Callback

/-!
# Callback execution preserves extra typed locals

Every callback execution can be lifted through a local thinning. The outcome
relation preserves halts and invariant violations, and successful states keep
the added locals weakened along the heap extension. The proof covers the full
statement and program syntax, including paying loops and all call/try/send
branches; no fragment or payment-free hypothesis is used.

This is forward simulation. `Semantics/CallbackUnwk.lean` proves its converse
and the exact callback correspondence through local thinning.
`Semantics/DeferredCorrespondence.lean` applies these laws to direct/captured
deferred operands. Native syntax and source support are unchanged.
The proofs reuse ordinary interpreter weakening for
non-forking steps, and keep programs interpreted.
-/

namespace Solidity.CallbackWk

variable {C : Contract}

mutual

theorem callsBack_stmt {pay : Bool} : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    {Δ : Ctx} → (h : Thin Γ Δ) → (s.wk h).2.2.callsBack pay = s.callsBack pay
  | _, _, .ite c thn els, _, h => by
    change ((thn.wk h).2.2.callsBack pay || (els.wk h).2.2.callsBack pay) =
      (thn.callsBack pay || els.callsBack pay)
    rw [callsBack_prog thn h, callsBack_prog els h]
  | _, _, .loop a c body, _, h => callsBack_prog body h
  | _, _, .block body, _, h => callsBack_prog body h
  | _, _, .call f args ret body, _, h => by cases ret <;> rfl
  | _, _, .callReceiverPush _ _ _ body code _, _, h => by
    change (body.callsBack pay || (code.wk h).2.2.callsBack pay) =
      (body.callsBack pay || code.callsBack pay)
    rw [callsBack_prog code h]
  | _, _, .assign .., _, _ | _, _, .rebind .., _, _ | _, _, .assignLocal .., _, _
  | _, _, .declLocal .., _, _ | _, _, .declStorage .., _, _
  | _, _, .opAssign .., _, _ | _, _, .incDec .., _, _
  | _, _, .assignIncDec .., _, _ | _, _, .assignLocalPush .., _, _
  | _, _, .pushOpAssign .., _, _ | _, _, .pushIncDec .., _, _
  | _, _, .push .., _, _ | _, _, .pop .., _, _
  | _, _, .transfer .., _, _ | _, _, .send .., _, _
  | _, _, .declMem .., _, _ | _, _, .rebindMem .., _, _
  | _, _, .assignFromMem .., _, _ | _, _, .assignMem .., _, _
  | _, _, .delete .., _, _ | _, _, .deleteMem .., _, _ | _, _, .assignNew .., _, _
  | _, _, .require .., _, _ | _, _, .assert .., _, _ | _, _, .revert, _, _
  | _, _, .callReceiver .., _, _ | _, _, .tryCall .., _, _ => rfl

theorem callsBack_prog {pay : Bool} : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    {Δ : Ctx} → (h : Thin Γ Δ) → (P.wk h).2.2.callsBack pay = P.callsBack pay
  | _, _, .nil, _, _ => rfl
  | _, _, .cons s P, _, h => by
    change ((s.wk h).2.2.callsBack pay || (P.wk (s.wk h).2.1).2.2.callsBack pay) =
      (s.callsBack pay || P.callsBack pay)
    rw [callsBack_stmt s h, callsBack_prog P (s.wk h).2.1]

end

theorem hasTransfer_stmt {Γ Γ' Δ : Ctx} (s : Stmt C Γ Γ') (h : Thin Γ Δ) :
    (s.wk h).2.2.hasTransfer = s.hasTransfer := by
  rw [← Stmt.callsBack_true, ← Stmt.callsBack_true, callsBack_stmt s h]

theorem hasTransfer_prog {Γ Γ' Δ : Ctx} (P : Prog C Γ Γ') (h : Thin Γ Δ) :
    (P.wk h).2.2.hasTransfer = P.hasTransfer := by
  rw [← Prog.callsBack_true, ← Prog.callsBack_true, callsBack_prog P h]

theorem forksIn_stmt {pay : Bool} {Γ Γ' Δ : Ctx} (s : Stmt C Γ Γ') (h : Thin Γ Δ) :
    (s.wk h).2.2.forksIn pay = s.forksIn pay := by
  cases s <;> try rfl
  case loop a c body => exact callsBack_prog body h
  case block body => exact callsBack_prog body h

theorem forks_stmt {Γ Γ' Δ : Ctx} (s : Stmt C Γ Γ') (h : Thin Γ Δ) :
    (s.wk h).2.2.forks = s.forks := by
  rw [← Stmt.forksIn_true, ← Stmt.forksIn_true, forksIn_stmt s h]

/-- Callback outcomes related by local weakening, with the same halted/violated status. -/
def CWkRel {Γ Δ : Ctx} {H : HTy} (h : Thin Γ Δ)
    (off : List ((t : LTy) × t.TDenote C H)) : COut C H Γ → COut C H Δ → Prop
  | .ok a, .ok b => TWkRel h off (.ok a) (.ok b)
  | .halt e, .halt e' => e = e'
  | .violated, .violated => True
  | _, _ => False

theorem CWkRel.of_res {Γ Δ : Ctx} {H : HTy} {h : Thin Γ Δ}
    {off : List ((t : LTy) × t.TDenote C H)} {r : TRes (Out C H Γ)} {r' : TRes (Out C H Δ)}
    (hr : TWkRel h off r r') : CWkRel h off (.ofRes r) (.ofRes r') := by
  cases r <;> cases r' <;> exact hr

theorem CWkRel.eq_lifted {Γ Δ : Ctx} {H : HTy} {h : Thin Γ Δ} {d : TEnv C H Δ}
    {o : COut C H Γ} {o' : COut C H Δ} (hr : CWkRel h (TEnv.off h d) o o') :
    o' = o.map (Out.lift h d) := by
  cases o with
  | ok a =>
    cases o' with
    | ok b => exact congrArg COut.ok (Except.ok.inj
        (TWkRel.eq_lifted (h := h) (d := d) (r₀ := .ok a) (r := .ok b) hr))
    | halt _ => cases hr
    | violated => cases hr
  | halt e =>
    cases o' with
    | ok _ => cases hr
    | halt e' => cases hr; rfl
    | violated => cases hr
  | violated =>
    cases o' with
    | ok _ => cases hr
    | halt _ => cases hr
    | violated => rfl

theorem CWkRel.drop {Γ Γ' Δ Δ' : Ctx} {H : HTy}
    {e : Ext Γ Γ'} {h : Thin Γ Δ} {e' : Ext Δ Δ'} {h' : Thin Γ' Δ'}
    (ho : Thin.Over e h e' h') {off : List ((t : LTy) × t.TDenote C H)}
    {o : COut C H Γ'} {o' : COut C H Δ'} (hr : CWkRel h' off o o') :
    CWkRel h off (o.map (Out.drop e)) (o'.map (Out.drop e')) := by
  cases o with
  | ok a =>
    cases o' with
    | ok b => exact TWkRel.drop ho (r₀ := .ok a) (r := .ok b) hr
    | halt _ => cases hr
    | violated => cases hr
  | halt e =>
    cases o' with
    | ok _ => cases hr
    | halt e' => exact hr
    | violated => cases hr
  | violated =>
    cases o' with
    | ok _ => cases hr
    | halt _ => cases hr
    | violated => trivial

theorem CWkRel.cat {Γ₁ Δ₁ Γ₂ Δ₂ : Ctx} {H : HTy}
    {h₁ : Thin Γ₁ Δ₁} {h₂ : Thin Γ₂ Δ₂} (a : Out C H Γ₁) (d : TEnv C a.st.H Δ₁)
    {off : List ((t : LTy) × t.TDenote C H)} (hd : TEnv.off h₁ d = offWk a.ext off)
    {o : COut C a.st.H Γ₂} {o' : COut C a.st.H Δ₂}
    (hr : CWkRel h₂ (TEnv.off h₁ d) o o') :
    CWkRel h₂ off (o.map (Out.cat a))
      (o'.map (Out.cat (⟨a.st.lift h₁ d, a.ext⟩ : Out C H Δ₁))) := by
  cases o with
  | ok b =>
    cases o' with
    | ok b' =>
      obtain ⟨d', hd', rfl⟩ := hr
      refine ⟨d', ?_, rfl⟩
      rw [hd', hd, offWk_trans]
    | halt _ => cases hr
    | violated => cases hr
  | halt e =>
    cases o' with
    | ok _ => cases hr
    | halt e' => exact hr
    | violated => cases hr
  | violated =>
    cases o' with
    | ok _ => cases hr
    | halt _ => cases hr
    | violated => trivial

theorem at_lift {Γ Δ : Ctx} (J : StateInv C) (h : Thin Γ Δ) (σ : State C Γ)
    (d : TEnv C σ.H Δ) : J.at (σ.lift h d) ↔ J.at σ := Iff.rfl

theorem lift_havoc {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Γ)
    (d : TEnv C σ.H Δ) (st : Storage C) (nt : Ledger) :
    (σ.lift h d).havoc st nt = (σ.havoc st nt).lift h d := rfl

def WkS (J : StateInv C) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {o : COut C σ.H Γ'}, ExecS J σ s o →
      ∃ o', ExecS J (σ.lift h d) (s.wk h).2.2 o' ∧
        CWkRel (s.wk h).2.1 (TEnv.off h d) o o'

def WkP (J : StateInv C) {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prop :=
  ∀ {Δ : Ctx} (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ)
    {o : COut C σ.H Γ'}, ExecP J σ P o →
      ∃ o', ExecP J (σ.lift h d) (P.wk h).2.2 o' ∧
        CWkRel (P.wk h).2.1 (TEnv.off h d) o o'

theorem det_wk {Γ Γ' Δ : Ctx} (J : StateInv C) (s : Stmt C Γ Γ')
    (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ) (hf : s.forksIn J.pay = false) :
    ∃ o', ExecS J (σ.lift h d) (s.wk h).2.2 o' ∧
      CWkRel (s.wk h).2.1 (TEnv.off h d) (.ofRes (s.run σ)) o' :=
  ⟨_, .det ((forksIn_stmt s h).trans hf), CWkRel.of_res (Stmt.run_wk s h σ d)⟩

theorem callLeave_wk {Γ Δ Γ' ps rs Γf : Ctx} (h : Thin Γ Δ) (σ : State C Γ)
    (d : TEnv C σ.H Δ) (ret : CallRet Γ rs Γ') (hb : Ext (rs ++ ps) Γf)
    (a : Out C σ.H (rs ++ ps)) (o : COut C a.st.H Γf) :
    CWkRel (ret.wk h).2.1 (TEnv.off h d)
      (o.map (TRun.callLeave ret hb σ a))
      (o.map (TRun.callLeave (ret.wk h).2.2 hb (σ.lift h d) a)) := by
  cases o with
  | ok b =>
    have ee : σ.H <+: b.st.H := a.ext.trans b.ext
    obtain ⟨d', hd', he⟩ := CallRet.leaveT_wk h (TEnv.wk ee _ σ.env) (TEnv.wk ee _ d) ret
      (TEnv.take _ (TEnv.drop hb b.st.env))
    refine ⟨d', by rw [hd', TEnv.off_wk], ?_⟩
    change (⟨b.st.withEnv ((ret.wk h).2.2.leaveT (TEnv.wk ee _ (TEnv.put h σ.env d)) _), ee⟩ :
      Out C σ.H _) = _
    rw [TEnv.put_wk, he]
    rfl
  | halt e => rfl
  | violated => trivial

theorem call_wk {Γ Γ' ps rs Γf : Ctx} (J : StateInv C) (f : Name) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf) : WkS J (.call f args ret body) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | callArgs ha =>
    refine ⟨_, ExecS.callArgs (f := f) (args := args.wk h) (ret := (ret.wk h).2.2)
      (body := body) ?_, rfl⟩
    simpa only [Args.evalT_wk] using ha
  | @callBody _ _ _ _ _ _ _ _ _ _ a o ha hp =>
    have hr := callLeave_wk h σ d ret body.ext (ret.enterT (σ.withEnv a)) o
    cases ret <;> refine ⟨_, ExecS.callBody (J := J) (σ := σ.lift h d) (f := f)
      (args := args.wk h) (body := body) ?_ hp, hr⟩
    all_goals simpa only [Args.evalT_wk] using ha

theorem CWkRel.lift_ok {Γ Δ : Ctx} {H : HTy} (h : Thin Γ Δ) (d : TEnv C H Δ)
    (a : Out C H Γ) : CWkRel h (TEnv.off h d) (.ok a) (.ok (Out.lift h d a)) :=
  ⟨TEnv.wk a.ext Δ d, TEnv.off_wk a.ext h d, rfl⟩

theorem transfer_wk {Γ : Ctx} (J : StateInv C) (r amt : Val C Γ .uint) :
    WkS J (.transfer r amt) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | transferHalt hpay hp =>
    refine ⟨_, ExecS.transferHalt (J := J) hpay ?_, rfl⟩
    rw [TRun.transfer_wk, hp]
    rfl
  | @transferViolated _ _ _ _ a hpay hp hj =>
    have hl : TRun.transfer (r.wk h) (amt.wk h) (σ.lift h d) = .ok (Out.lift h d a) := by
      rw [TRun.transfer_wk, hp]
      rfl
    exact ⟨_, .transferViolated hpay hl (fun hk => hj ((at_lift J h a.st _).mp hk)), trivial⟩
  | @transferResume _ _ _ _ a st nt hpay hp hj hk =>
    have hl : TRun.transfer (r.wk h) (amt.wk h) (σ.lift h d) = .ok (Out.lift h d a) := by
      rw [TRun.transfer_wk, hp]
      rfl
    refine ⟨_, ExecS.transferResume (J := J) (st := st) (nt := nt) hpay hl ?_ ?_, ?_⟩
    · exact (at_lift J h a.st _).mpr hj
    · exact (at_lift J h (a.st.havoc st nt) _).mpr hk
    · exact CWkRel.lift_ok h d ⟨a.st.havoc st nt, a.ext⟩

theorem send_wk {Γ : Ctx} (J : StateInv C) (pv : Idx Γ (.val .bool))
    (r amt : Val C Γ .uint) : WkS J (.send pv r amt) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | sendHalt hpay hp =>
    refine ⟨_, ExecS.sendHalt (J := J) hpay ?_, rfl⟩
    rw [TRun.transfer_wk, hp]
    rfl
  | @sendFailed _ _ _ _ _ a hpay hp =>
    have hl : TRun.transfer (r.wk h) (amt.wk h) (σ.lift h d) = .ok (Out.lift h d a) := by
      rw [TRun.transfer_wk, hp]
      rfl
    refine ⟨_, ExecS.sendFailed (J := J) (pv := pv.wk h) hpay hl, ?_⟩
    simpa only [Out.lift, TEnv.wk_self, State.lift_setLocal] using
      CWkRel.lift_ok h d (⟨σ.setLocal pv false, List.prefix_refl _⟩ : Out C σ.H Γ)
  | @sendViolated _ _ _ _ _ a hpay hp hj =>
    have hl : TRun.transfer (r.wk h) (amt.wk h) (σ.lift h d) = .ok (Out.lift h d a) := by
      rw [TRun.transfer_wk, hp]
      rfl
    exact ⟨_, .sendViolated hpay hl (fun hk => hj ((at_lift J h a.st _).mp hk)), trivial⟩
  | @sendResume _ _ _ _ _ a st nt hpay hp hj hk =>
    have hl : TRun.transfer (r.wk h) (amt.wk h) (σ.lift h d) = .ok (Out.lift h d a) := by
      rw [TRun.transfer_wk, hp]
      rfl
    refine ⟨_, ExecS.sendResume (J := J) (pv := pv.wk h) (st := st) (nt := nt) hpay hl ?_ ?_, ?_⟩
    · exact (at_lift J h a.st _).mpr hj
    · exact (at_lift J h (a.st.havoc st nt) _).mpr hk
    · simpa only [Out.lift, State.lift_setLocal, lift_havoc] using
        CWkRel.lift_ok h d (⟨(a.st.havoc st nt).setLocal pv true, a.ext⟩ : Out C σ.H Γ)

theorem ite_wk {Γ Γ₁ Γ₂ : Ctx} (J : StateInv C) (c : Val C Γ .bool)
    (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) (ht : WkP J thn) (hels : WkP J els) :
    WkS J (.ite c thn els) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | iteHalt hc =>
    refine ⟨_, ExecS.iteHalt (J := J) ?_, rfl⟩
    simpa only [Val.evalT_wk] using hc
  | iteThen hc hp =>
    obtain ⟨u, hu, hr⟩ := ht h σ d hp
    refine ⟨_, ExecS.iteThen (J := J) ?_ hu, CWkRel.drop (Prog.wk_over thn h) hr⟩
    simpa only [Val.evalT_wk] using hc
  | iteElse hc hp =>
    obtain ⟨u, hu, hr⟩ := hels h σ d hp
    refine ⟨_, ExecS.iteElse (J := J) ?_ hu, CWkRel.drop (Prog.wk_over els h) hr⟩
    simpa only [Val.evalT_wk] using hc

theorem block_wk {Γ Γ₁ : Ctx} (J : StateInv C) (body : Prog C Γ Γ₁) (hb : WkP J body) :
    WkS J (.block body) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | block ht hp =>
    obtain ⟨u, hu, hr⟩ := hb h σ d hp
    exact ⟨_, ExecS.block ((callsBack_prog body h).trans ht) hu,
      CWkRel.drop (Prog.wk_over body h) hr⟩

theorem res_map_map {α β γ : Type} (r : TRes α) (f : α → β) (g : β → γ) :
    (r.map f).map g = r.map (fun x => g (f x)) := by
  cases r <;> rfl

theorem receiverOp_wk {Γ Δ : Ctx} {H : HTy} {E : Ty} (h : Thin Γ Δ) (op : ReceiverOp C Γ E)
    {off : List ((t : LTy) × t.TDenote C H)}
    {o : COut C H (.alias (.array E) :: Γ)} {o' : COut C H (.alias (.array E) :: Δ)}
    (hr : CWkRel (.keep h) off o o') :
    CWkRel h off (o.receiverOp op) (o'.receiverOp (op.wk h)) := by
  cases o with
  | ok a =>
    cases o' with
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      have hrun := CWkRel.of_res (TWkRel.of_eq (TRun.receiverOp_afterAlias_wk h op a.st d'))
      have hdrop := CWkRel.drop (.push (.refl h)) hrun
      have hcat := CWkRel.cat a d' hd hdrop
      simpa only [COut.receiverOp, COut.map_ofRes, res_map_map] using hcat
    | halt _ => cases hr
    | violated => cases hr
  | halt e =>
    cases o' with
    | ok _ => cases hr
    | halt e' => exact hr
    | violated => cases hr
  | violated =>
    cases o' with
    | ok _ => cases hr
    | halt _ => cases hr
    | violated => trivial

theorem callReceiver_wk {Γ ps Γf : Ctx} {E : Ty} (J : StateInv C) (f : Name)
    (args : Args C Γ ps) (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (op : ReceiverOp C Γ E) : WkS J (.callReceiver f args r body op) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | callReceiver hc =>
    obtain ⟨u, hu, hr⟩ := call_wk J f args (.storage _ r) body h σ d hc
    exact ⟨_, ExecS.callReceiver hu, receiverOp_wk h op hr⟩

/-- Finishing `f().push(e)` preserves the operand prefix's weakening relation. -/
theorem pushPrefix_wk {Γ Γv Δ : Ctx} {H : HTy} {E : Ty}
    (code : Prog C Γ Γv) (value : Src C Γv E) (ref : SRef C (.array E)) (h : Thin Γ Δ)
    {off : List ((t : LTy) × t.TDenote C H)}
    {u : COut C H Γv} {u' : COut C H (code.wk h).1}
    (hr : CWkRel (code.wk h).2.1 off u u') :
    CWkRel h off (u.pushPrefix code.ext value ref)
      (u'.pushPrefix (code.wk h).2.2.ext (value.wk (code.wk h).2.1) ref) := by
  cases u <;> cases u'
  all_goals first | exact False.elim hr | skip
  all_goals try exact hr
  case ok.ok a b =>
    obtain ⟨d, hd, rfl⟩ := hr
    simp only [COut.pushPrefix, Src.valueT_wk]
    cases hv : value.valueT a.st with
    | error err => rfl
    | ok v =>
      dsimp only [bind, Except.bind, State.lift, State.withEnv]
      cases hf : a.st.storage.full ref with
      | true => rfl
      | false =>
        cases hs : a.st.storage.push ref (fun _ => some v.strip) with
        | none => rfl
        | some st =>
          exact CWkRel.drop (Prog.wk_over code h)
            (o := .ok ⟨a.st.withStorage st, a.ext⟩)
            (o' := .ok ⟨(a.st.withStorage st).lift (code.wk h).2.1 d, a.ext⟩)
            ⟨d, hd, rfl⟩

/-- A caller local added around `f().push(i++)` survives getter and operand callbacks. -/
theorem callReceiverPush_wk {Γ ps Γf Γv : Ctx} {E : Ty} (J : StateInv C) (f : Name)
    (args : Args C Γ ps) (r : Var) (body : Prog C ([.alias (.array E)] ++ ps) Γf)
    (code : Prog C Γ Γv) (value : Src C Γv E) (hb : WkP J code) :
    WkS J (.callReceiverPush f args r body code value) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | @callReceiverPush _ _ _ _ _ _ _ _ _ _ _ _ a ref u hc hp hu =>
    obtain ⟨v, hv, hr⟩ := call_wk J f args (.storage _ r) body h σ d hc
    cases v with
    | halt _ => cases hr
    | violated => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      obtain ⟨u', hu', hr'⟩ := hb h (a.st.drop (.push .refl)) d'.2 hu
      exact ⟨_, ExecS.callReceiverPush hv hp hu',
        CWkRel.cat a d' hd (pushPrefix_wk code value ref h hr')⟩
  | callReceiverPushUnset hc hp =>
    obtain ⟨v, hv, hr⟩ := call_wk J f args (.storage _ r) body h σ d hc
    cases v with
    | halt _ => cases hr
    | violated => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      exact ⟨_, ExecS.callReceiverPushUnset hv hp, rfl⟩
  | callReceiverPushHalt hc =>
    obtain ⟨v, hv, hr⟩ := call_wk J f args (.storage _ r) body h σ d hc
    cases v <;> cases hr
    exact ⟨_, ExecS.callReceiverPushHalt hv, rfl⟩
  | callReceiverPushViolated hc =>
    obtain ⟨v, hv, hr⟩ := call_wk J f args (.storage _ r) body h σ d hc
    cases v <;> try cases hr
    exact ⟨_, ExecS.callReceiverPushViolated hv, trivial⟩

theorem tryCall_wk {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (J : StateInv C) (call : ExtCall C Γ)
    (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γ₁) (err : Prog C Γ Γ₂) (code : CodeBinder κ)
    (pnc : Prog C (κ ++ Γ) Γ₃) (other : Prog C Γ Γ₄)
    (hok : WkP J ok) (herr : WkP J err) (hpnc : WkP J pnc) (hoth : WkP J other) :
    WkS J (.tryCall call rets ok err code pnc other) := by
  intro Δ h σ d o he
  cases he with
  | det hf => exact det_wk J _ h σ d hf
  | tryRevert => exact ⟨_, .tryRevert, rfl⟩
  | tryDecode hd => exact ⟨_, .tryDecode hd, rfl⟩
  | tryViolated hj => exact ⟨_, .tryViolated (fun hk => hj ((at_lift J h σ d).mp hk)), trivial⟩
  | tryOk hj hk hd hp =>
    rename_i st nt vs rest r u
    obtain ⟨u', hu, hr⟩ := hok (Thin.keepAll ρ h)
      ((σ.havoc st nt).withEnv (TEnv.append ρ r σ.env)) (TEnv.append ρ r d) hp
    simp only [State.lift, State.withEnv, State.havoc] at hu
    rw [TEnv.put_keepAll h ρ r r σ.env d] at hu
    refine ⟨_, ExecS.tryOk (J := J) (st := st) (nt := nt) (vs := vs) (rest := rest)
      ((at_lift J h σ d).mpr hj) ((at_lift J h (σ.havoc st nt) d).mpr hk) hd hu, ?_⟩
    simpa only [TEnv.off_keepAll] using
      (CWkRel.drop ((Thin.Over.append h ρ).trans (Prog.wk_over ok (Thin.keepAll ρ h))) hr)
  | tryError hp =>
    obtain ⟨u, hu, hr⟩ := herr h σ d hp
    exact ⟨_, ExecS.tryError hu, CWkRel.drop (Prog.wk_over err h) hr⟩
  | tryPanic hp =>
    rename_i v u
    obtain ⟨u', hu, hr⟩ := hpnc (Thin.keepAll κ h)
      (σ.withEnv (TEnv.append κ (code.decodeT v) σ.env)) (TEnv.append κ (code.decodeT v) d) hp
    simp only [State.lift, State.withEnv] at hu
    rw [TEnv.put_keepAll h κ (code.decodeT v) (code.decodeT v) σ.env d] at hu
    refine ⟨_, ExecS.tryPanic (v := v) hu, ?_⟩
    simpa only [TEnv.off_keepAll] using
      (CWkRel.drop ((Thin.Over.append h κ).trans (Prog.wk_over pnc (Thin.keepAll κ h))) hr)
  | tryOther hp =>
    obtain ⟨u, hu, hr⟩ := hoth h σ d hp
    exact ⟨_, ExecS.tryOther hu, CWkRel.drop (Prog.wk_over other h) hr⟩

theorem CWkRel.isOk {Γ Δ : Ctx} {H : HTy} {h : Thin Γ Δ}
    {off : List ((t : LTy) × t.TDenote C H)} {o : COut C H Γ} {o' : COut C H Δ}
    (hr : CWkRel h off o o') : o'.isOk = o.isOk := by
  cases o <;> cases o' <;> first | rfl | cases hr

theorem execS_drop_lift {Γ Γ' Δ Δ' Ε : Ctx} {e : Ext Γ Γ'} {h : Thin Γ Δ}
    {e' : Ext Δ Δ'} {h' : Thin Γ' Δ'} (ho : Thin.Over e h e' h')
    (J : StateInv C) (σ : State C Γ') (d : TEnv C σ.H Δ') (s : Stmt C Δ Ε)
    {o : COut C σ.H Ε} (he : ExecS J ((σ.drop e).lift h (TEnv.drop e' d)) s o) :
    ExecS J ((σ.lift h' d).drop e') s o := by
  dsimp only [State.drop, State.lift, State.withEnv] at he ⊢
  rw [(ho.tenv σ.env d).1]
  exact he

def LoopWeak (J : StateInv C) {Γ Γ' : Ctx} (σ : State C Γ)
    (s : Stmt C Γ Γ') (o : COut C σ.H Γ') : Prop :=
  match s with
  | .loop a c body => WkP J body → ∀ {Δ : Ctx} (h : Thin Γ Δ) (d : TEnv C σ.H Δ),
      ∃ o', ExecS J (σ.lift h d) (.loop (a.wk h) (c.wk h) (body.wk h).2.2) o' ∧
        CWkRel h (TEnv.off h d) o o'
  | _ => True

theorem loop_exec_wk {J : StateInv C} {Γ Γ' : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Γ'} {o : COut C σ.H Γ'} (he : ExecS J σ s o) : LoopWeak J σ s o := by
  induction he using ExecS.rec (motive_2 := fun _ _ _ _ => True) with
  | @det Γ₀ Γ₁ τ s₀ hf =>
    cases s₀ <;> try trivial
    case loop a c body =>
      intro hb Δ h d
      exact det_wk J _ h τ d hf
  | @loopHalt Γ Γ₁ σ a c body err ht hc =>
    intro hb Δ h d
    refine ⟨_, ExecS.loopHalt ((callsBack_prog body h).trans ht) ?_, rfl⟩
    simpa only [Val.evalT_wk] using hc
  | @loopExit Γ Γ₁ σ a c body ht hc =>
    intro hb Δ h d
    refine ⟨_, ExecS.loopExit ((callsBack_prog body h).trans ht) ?_, ?_⟩
    · simpa only [Val.evalT_wk] using hc
    · simpa only [Out.lift, TEnv.wk_self] using
        CWkRel.lift_ok h d (⟨σ, List.prefix_refl _⟩ : Out C σ.H Γ)
  | @loopIter Γ Γ₁ σ a c body v o ht hc hp hl _ ih =>
    intro hb Δ h d
    obtain ⟨u, hu, hr⟩ := hb h σ d hp
    cases u with
    | halt _ => cases hr
    | violated => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      have ho := Prog.wk_over body h
      obtain ⟨u', hu', hr'⟩ := ih hb h (TEnv.drop (body.wk h).2.2.ext d')
      have hn := execS_drop_lift ho J v.st d'
        (.loop (a.wk h) (c.wk h) (body.wk h).2.2) hu'
      refine ⟨_, ExecS.loopIter ((callsBack_prog body h).trans ht) ?_ hu hn,
        CWkRel.cat (Out.drop body.ext v) (TEnv.drop (body.wk h).2.2.ext d')
          ((ho.tenv v.st.env d').2.trans hd) hr'⟩
      simpa only [Val.evalT_wk] using hc
  | @loopStop Γ Γ₁ σ a c body o ht hc hp hn _ =>
    intro hb Δ h d
    obtain ⟨u, hu, hr⟩ := hb h σ d hp
    refine ⟨_, ExecS.loopStop ((callsBack_prog body h).trans ht) ?_ hu
      ((CWkRel.isOk hr).trans hn), CWkRel.drop (Prog.wk_over body h) hr⟩
    simpa only [Val.evalT_wk] using hc
  | @loopDiverge Γ Γ₁ σ a c body ht =>
    intro hb Δ h d
    exact ⟨_, ExecS.loopDiverge ((callsBack_prog body h).trans ht), rfl⟩
  | _ => trivial

theorem loop_wk {Γ Γ₁ : Ctx} (J : StateInv C) (a : LoopAnn C Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Γ₁) (hb : WkP J body) : WkS J (.loop a c body) := by
  intro Δ h σ d o he
  exact loop_exec_wk he hb h d

mutual

theorem stmt_wk (J : StateInv C) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → WkS J s
  | _, _, .ite c thn els => ite_wk J c thn els (prog_wk J thn) (prog_wk J els)
  | _, _, .block body => block_wk J body (prog_wk J body)
  | _, _, .loop a c body => loop_wk J a c body (prog_wk J body)
  | _, _, .transfer r a => transfer_wk J r a
  | _, _, .send pv r a => send_wk J pv r a
  | _, _, .call f args ret body => call_wk J f args ret body
  | _, _, .callReceiver f args r body op => callReceiver_wk J f args r body op
  | _, _, .callReceiverPush f args r body code value =>
    callReceiverPush_wk J f args r body code value (prog_wk J code)
  | _, _, .tryCall call rets ok err code pnc other =>
    tryCall_wk J call rets ok err code pnc other
      (prog_wk J ok) (prog_wk J err) (prog_wk J pnc) (prog_wk J other)
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
    intro h σ d o he
    cases he with
    | det hf => exact det_wk J _ h σ d hf

theorem prog_wk (J : StateInv C) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → WkP J P
  | _, _, .nil => by
    intro h σ d o he
    cases he
    exact ⟨_, .nil, d, (offWk_self _ _).symm, rfl⟩
  | _, _, .cons s P => by
    intro h σ d o he
    cases he with
    | cons hs hp =>
      rename_i a b
      obtain ⟨u, hu, hr⟩ := stmt_wk J s h σ d hs
      cases u with
      | halt _ => cases hr
      | violated => cases hr
      | ok a' =>
        obtain ⟨d', hd, rfl⟩ := hr
        obtain ⟨v, hv, hrel⟩ := prog_wk J P (s.wk h).2.1 a.st d' hp
        exact ⟨_, ExecP.cons hu hv, CWkRel.cat a d' hd hrel⟩
    | halt hs =>
      obtain ⟨u, hu, hr⟩ := stmt_wk J s h σ d hs
      cases u with
      | ok _ => cases hr
      | violated => cases hr
      | halt e => cases hr; exact ⟨_, ExecP.halt hu, rfl⟩
    | violated hs =>
      obtain ⟨u, hu, hr⟩ := stmt_wk J s h σ d hs
      cases u with
      | ok _ => cases hr
      | halt _ => cases hr
      | violated => exact ⟨_, ExecP.violated hu, trivial⟩

end

/-- Add a fresh storage alias without losing any callback run; preserve it across scope exit. -/
theorem prog_afterAlias {Γ Γ' : Ctx} {R : RefTy} (J : StateInv C) (P : Prog C Γ Γ')
    (σ : State C Γ) (p : Option (SRef C (.ref R))) {o : COut C σ.H Γ'}
    (he : ExecP J σ P o) :
    ∃ o', ExecP J (σ.push (t := .alias R) p) (P.wk (.drop .refl)).2.2 o' ∧
      o'.map (Out.drop (P.wk (.drop .refl)).2.2.ext) =
        (o.map (Out.drop P.ext)).map (fun x => ⟨x.st.push (t := .alias R) p, x.ext⟩) := by
  obtain ⟨u, hu, hr⟩ := prog_wk J P (.drop (t := .alias R) .refl) σ (p, σ.env) he
  refine ⟨u, hu, ?_⟩
  simpa only [Out.lift, State.lift, State.push, TEnv.put, TEnv.wk, LTy.TDenote.wk] using
    (CWkRel.drop (Prog.wk_over P (.drop .refl)) hr).eq_lifted

theorem _root_.Solidity.Stmt.exec_wk {Γ Γ' Δ : Ctx} (J : StateInv C) (s : Stmt C Γ Γ')
    (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ) {o : COut C σ.H Γ'}
    (he : ExecS J σ s o) :
    ∃ o', ExecS J (σ.lift h d) (s.wk h).2.2 o' ∧
      CWkRel (s.wk h).2.1 (TEnv.off h d) o o' := stmt_wk J s h σ d he

theorem _root_.Solidity.Prog.exec_wk {Γ Γ' Δ : Ctx} (J : StateInv C) (P : Prog C Γ Γ')
    (h : Thin Γ Δ) (σ : State C Γ) (d : TEnv C σ.H Δ) {o : COut C σ.H Γ'}
    (he : ExecP J σ P o) :
    ∃ o', ExecP J (σ.lift h d) (P.wk h).2.2 o' ∧
      CWkRel (P.wk h).2.1 (TEnv.off h d) o o' := prog_wk J P h σ d he

/-- A fresh storage alias survives arbitrary callback execution and the program's scope end. -/
theorem _root_.Solidity.Prog.exec_afterAlias {Γ Γ' : Ctx} {R : RefTy} (J : StateInv C)
    (P : Prog C Γ Γ') (σ : State C Γ) (p : Option (SRef C (.ref R))) {o : COut C σ.H Γ'}
    (he : ExecP J σ P o) :
    ∃ o', ExecP J (σ.push (t := .alias R) p) (P.wk (.drop .refl)).2.2 o' ∧
      o'.map (Out.drop (P.wk (.drop .refl)).2.2.ext) =
        (o.map (Out.drop P.ext)).map (fun x => ⟨x.st.push (t := .alias R) p, x.ext⟩) :=
  prog_afterAlias J P σ p he

end Solidity.CallbackWk
