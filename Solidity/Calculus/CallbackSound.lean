import Solidity.Calculus.Callback
import Solidity.Calculus.CallbackHolds
import Solidity.Calculus.Sound
import Solidity.Calculus.UpdateRules
import Solidity.Semantics.NativeDeferredCallback

/-!
# The calculus with callbacks is sound

`ProvesC I pay H φ` (`Calculus/Callback.lean`) proves `φ` with callbacks:
what it derives holds, its context in front, when every `try` and value call,
and with `pay` every payment, may call back into the contract and the callee
leaves the invariant as it found it
(`holdsC`, `ValidC`, `Calculus/CallbackHolds.lean`).  `ProvesC.sound_of`
and `ProvesC.valid` take the invariant first-order (`Fml.FO`, a contract
invariant of the storage and the ledger; `Invariant.fo` carries it): "the invariant holds" is then a
fact of what the state's terms read (`State.ReadsAs`: its global part and
its locals erased), which the callee's run and the updates preserve.

* A rule of the calculus fires on a statement that runs no other by a
  choice and pays nothing (`ProvesC.update`, `unfold`, `bind`): such a
  statement has one callback run, its typed run, and what its premise asks
  of that run (`Premise.Runs`, the arms' statement, `Stmt.runs`) carries
  the premise over every callback run of the rest.
* A split (`ifElseSplit`, `requireSimple`) runs with callbacks as the branch
  its condition picks (`Premise.Runs`' split clause, which the `if` arm
  proves of `ExecS`'s `ite` runs).
* The callback taclets read `ExecS`'s runs of a payment and a `try`: halted
  (a payment of simple operands never halts), the invariant broken on exit
  (refuted by "invariant on exit"), or resumed from a state the callee may
  leave, the invariant holding (the premise "resume after callback", "send
  succeeded", "call succeeded"); a send that fails and a `try` whose call
  reverts run their clause from where they were made.

`Frames.popsOnly`, `Fml.reclose?` and the `openInv`s use
`match` on the indexed families, against Gate G0's first condition: an
exemption, timed (`docs/intrinsic.md`, W3c `tactics`), since they run once
a rule.
-/

namespace Solidity

open Solidity (Modality RuleSet)

variable {C : Contract} {pay : Bool}

/-! ## First-order formulas read alike (`State.ReadsAs`) -/

/-- **A first-order formula holds alike in two typed states a term reads
alike.** -/
theorem holds_FO_reads {Γ : Ctx} (φ : Fml C Γ) (_ : φ.FO = true) {σ σ' : State C Γ}
    (e : σ.ReadsAs σ') : holds σ φ ↔ holds σ' φ := by
  rw [State.eq_of_readsAs e]

/-- The invariant at a state: of its global part (`StateInv.at`), read as a
closed formula after a frame end (`Fml.closedAt`). -/
theorem holdsC_closedAt_iff {I : Fml C []} (hI : I.FO = true) (hT : I.hasTransfer = false)
    {Γ : Ctx} (τ : State C Γ) : holdsC I pay τ (Fml.closedAt I) ↔ (I.stateInv pay).at τ := by
  constructor
  · intro h
    have h' := Upd.afterT.of_lands h (Upd.lands_drop_nil (Thin.nilTo Γ) τ)
    exact (holdsC_iff_holds I (Fml.callsBack_of_FO I hI) _).1 h'
  · intro h
    refine Upd.afterT_intro (fun _ => trivial) fun g σ'' hL => ?_
    refine (holdsC_iff_holds I (Fml.callsBack_of_FO I hI) σ'').2 ((holds_FO_reads I hI ?_).1 h)
    have hg : g = τ.globG := (Option.some.inj hL.1).symm
    exact ⟨(hL.2.1.trans (congrArg Subtype.val hg)).symm, fun i => nomatch i⟩

/-! ## Outcomes, through the frames -/

section Outcomes

variable {J : StateInv C} {m : Modality}

theorem COut.after_map_cat {H : HTy} {Γ₁ Γ₂ : Ctx} (o₁ : Out C H Γ₁) (o : COut C o₁.st.H Γ₂)
    (p : State C Γ₂ → Prop) : (o.map (Out.cat o₁)).after m p ↔ o.after m p := by
  cases o <;> exact Iff.rfl

theorem COut.thenF_map_cat {H : HTy} {Γ₁ Γ₂ Γ₀ : Ctx} (o₁ : Out C H Γ₁) (o : COut C o₁.st.H Γ₂)
    (κ : Frames C Γ₂ Γ₀) (p : State C Γ₀ → Prop) :
    (o.map (Out.cat o₁)).thenF J κ m p ↔ o.thenF J κ m p := by
  cases o <;> exact Iff.rfl

/-- The rest `ω` and then the frames `κ`, from what `ω` with callbacks
gives the frames. -/
theorem COut.after_seq {Γ Γ₁ Γ₀ : Ctx} {τ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀}
    {p : State C Γ₀ → Prop} (h : ∀ o, ExecP J τ ω o → o.thenF J κ m p) :
    ∀ o', ExecF J τ (.seq ω κ) o' → o'.after m p := by
  intro o' he
  cases he with
  | seq hω hκ => exact (COut.after_map_cat _ _ p).2 (h _ hω _ hκ)
  | seqHalt hω => exact h _ hω
  | seqViolated hω => exact (h _ hω).elim

/-- A block's outcome, its locals popped by a frame end. -/
theorem COut.thenF_drop {H : HTy} {Γ Γ' Γ₀ : Ctx} {b : BlockKind} {e : Ext Γ Γ'}
    {κ : Frames C Γ Γ₀} {p : State C Γ₀ → Prop} (o : COut C H Γ')
    (h : o.thenF J (.pop b e κ) m p) : (o.map (Out.drop e)).thenF J κ m p := by
  cases o with
  | ok o => exact fun o' he => h o' (.pop he)
  | halt _ => exact h
  | violated => exact h

/-- **A finished program's frames, with callbacks**, from the formula
`emptyModality` leaves (`Frames.exit`). -/
theorem holdsC_exit_after {I : Fml C []} {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ (φ : Fml C Γ₀) (σ : State C Γ), holdsC I pay σ (κ.exit m φ) →
      ∀ o', ExecF (I.stateInv pay) σ κ o' → o'.after m (holdsC I pay · φ)
  | _, .nil, φ, σ, h, o', he => by cases he; exact h
  | _, .seq .nil κ, φ, σ, h, o', he => by
    cases he with
    | seq hω hκ =>
      cases hω
      exact (COut.after_map_cat _ _ _).2 (holdsC_exit_after κ φ σ h _ hκ)
    | seqHalt hω => cases hω
    | seqViolated hω => cases hω
  | _, .seq (.cons s ω) κ, φ, σ, h, o', he => COut.after_seq h o' he
  | _, .pop _ e κ, φ, σ, h, o', he => by
    cases he with
    | pop hκ =>
      exact holdsC_exit_after κ φ (σ.drop e)
        (Upd.afterT.of_lands h (Upd.lands_pop_nil e σ)) _ hκ
  | _, .drop e κ, φ, σ, h, o', he => by
    cases he with
    | drop hκ =>
      exact holdsC_exit_after κ φ (σ.thin e)
        (Upd.afterT.of_lands h (Upd.lands_drop_nil e σ)) _ hκ

/-- The rest of the program, gone into the frames when it is empty, gives
the modality over it, with callbacks. -/
theorem holdsC_modalK {I : Fml C []} {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) (h : holdsC I pay σ (Fml.modalK m ω κ φ)) :
    holdsC I pay σ (.modal m ω κ φ) := by
  cases ω with
  | nil =>
    intro o ho
    cases ho
    exact holdsC_exit_after κ φ σ h
  | cons s ω => exact h

/-- **A statement and the rest, with callbacks**: what each callback run of
the statement leaves gives the rest and the frames. -/
theorem holdsC_cons {I : Fml C []} {Γ Γ' Γ₁ Γ₀ : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'}
    {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : ∀ o₁, ExecS (I.stateInv pay) σ s o₁ →
      o₁.thenF (I.stateInv pay) (.seq ω κ) m (holdsC I pay · φ)) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  intro o ho
  cases ho with
  | cons hs hω =>
    refine (COut.thenF_map_cat _ _ κ _).2 ?_
    rename_i o₁ o'
    cases o' with
    | ok o₂ => exact fun o₃ h₃ => (COut.after_map_cat _ _ _).1 (h _ hs _ (.seq hω h₃))
    | halt e => exact h _ hs _ (.seqHalt hω)
    | violated => exact h _ hs _ (.seqViolated hω)
  | halt hs => exact h _ hs
  | violated hs => exact (h _ hs).elim

end Outcomes

/-! ## A rule of the calculus, with callbacks -/

section Rules

variable {I : Fml C []} {m : Modality} {Γ Γ' Γ₁ Γ₀ : Ctx} {σ : State C Γ}
  {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}

/-- A sequence that pays nothing runs with callbacks as it runs. -/
theorem ExecP.of_run {J : StateInv C} {Δ : Ctx} {τ : State C Δ} {P : Prog C Δ Γ'}
    (hP : Prog.callsBack J.pay P = false) : ExecP J τ P (.ofRes (Prog.run τ P)) := by
  rcases Prog.exec_run J P τ with h | h
  · exact h
  · have := ExecP.eq_run h hP
    revert this
    cases Prog.run τ P <;> exact fun h => nomatch h

/-- Two outcomes that end alike, up to the halt, are read alike after the
frames. -/
theorem COut.thenF_of_sim {J : StateInv C} {H : HTy} {Δ : Ctx} {κ' : Frames C Δ Γ₀}
    {p : State C Γ₀ → Prop} {r r' : TRes (Out C H Δ)}
    (hs : TRes.Sim (r.map (·.st)) (r'.map (·.st))) (h : (COut.ofRes r).thenF J κ' m p) :
    (COut.ofRes r').thenF J κ' m p := by
  cases r with
  | ok a =>
    cases r' with
    | ok b =>
      obtain ⟨sa, ea⟩ := a
      obtain ⟨sb, eb⟩ := b
      have e : sa = sb := hs
      subst e
      exact h
    | error => exact hs.elim
  | error e =>
    cases r' with
    | ok => exact hs.elim
    | error e' =>
      obtain ⟨hp, hx⟩ := hs
      obtain ⟨h₁, h₂⟩ := h
      refine ⟨?_, fun he => h₂ (hp.2 he)⟩
      cases m with
      | box => trivial
      | diamond => exact hx h₁

/-- **A statement that does not fork, with callbacks**, by its typed run:
where it ends the rest holds, where it halts the halt is no panic, and an
exhaustion under the diamond. -/
theorem holdsC_cons_det {s : Stmt C Γ Γ'} (hs : s.forksIn pay = false)
    (hok : ∀ τ, Stmt.runSt σ s = .ok τ → holdsC I pay τ (Fml.modalK m ω κ φ))
    (herr : ∀ e, Stmt.runSt σ s = .error e → e ≠ .panic ∧ (m = .diamond → e = .exhausted)) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  rw [ExecS.detIn_inv he hs]
  cases ht : s.run σ with
  | ok o =>
    have hst : Stmt.runSt σ s = .ok o.st := by simp only [Stmt.runSt, ht]; rfl
    exact COut.after_seq (holdsC_modalK o.st ω κ φ (hok _ hst))
  | error e =>
    have hst : Stmt.runSt σ s = .error e := by simp only [Stmt.runSt, ht]; rfl
    obtain ⟨hp, hd⟩ := herr e hst
    refine ⟨?_, hp⟩
    cases m with
    | box => trivial
    | diamond => exact hd rfl

/-- **An update, with callbacks.** -/
theorem holdsC_update {s : Stmt C Γ Γ'} {U : Upd C Γ Γ'} (hs : s.forksIn pay = false)
    (hr : Premise.Runs m s (.update U) σ) (h : holdsC I pay σ (.upd m U (Fml.modalK m ω κ φ))) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) :=
  holdsC_cons_det hs
    (fun _ hτ => Upd.afterT.of_lands h (Upd.lands_of_applyP (hr.1 _ hτ)).choose_spec)
    fun e he => ⟨(hr.2 e he).1, fun hm => by
      subst hm
      by_cases hx : e = .exhausted
      · exact hx
      · have hd := (hr.2 e he).2 rfl hx
        exact (Upd.afterT.of_noExh h (Upd.globT_none_of_applyV hd.1) hd.2).elim⟩

/-- Two sequential updates, such as the append then save in
`a.push() += x`, preserve the callback reading of the continuation. -/
theorem holdsC_updates {Δ : Ctx} {s : Stmt C Γ Γ'} {U : Upd C Γ Δ} {V : Upd C Δ Γ'}
    (hs : s.forksIn pay = false) (hr : Premise.Runs m s (.updates U V) σ)
    (h : holdsC I pay σ (.upd m U (.upd m V (Fml.modalK m ω κ φ)))) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) :=
  holdsC_cons_det hs (fun _ hτ => Upd.afterT_pair_of_lands h (hr.1 _ hτ))
    fun e he => ⟨(hr.2 e he).1, fun hm => by
      subst hm
      by_cases hx : e = .exhausted
      · exact hx
      · exact (Upd.afterT_pair_noHalt h ((hr.2 e he).2 rfl hx)).elim⟩

/-- The outer zero-divisor test of `sp.push() /= se` reads no callbacks;
the successful branch keeps the two updates in order before its continuation. -/
theorem holdsC_guardedUpdates {Γ Δ Γ₁ Γ₀ : Ctx} {I : Fml C []} {m : Modality}
    {σ : State C Γ} {s : Stmt C Γ Γ} {c : Fml C Γ}
    {U : Upd C Γ Δ} {V : Upd C Δ Γ} {ω : Prog C Γ Γ₁}
    {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (hs : s.forksIn pay = false) (hr : Premise.Runs m s (.guardedUpdates c U V) σ)
    (h : holdsC I pay σ ((Premise.guardedUpdates c U V).fml m ω κ φ)) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  by_cases hc : holds σ c
  · exact holdsC_updates (U := U) (V := V) hs (hr.2.1 hc)
      (h.1 ((holdsC_iff_holds c (Fml.callsBack_of_hasTransfer c hr.1) σ).2 hc))
  · have hn : holdsC I pay σ (.not c) := fun hh =>
      hc ((holdsC_iff_holds c (Fml.callsBack_of_hasTransfer c hr.1) σ).1 hh)
    have he := h.2 hn
    refine holdsC_cons fun o₁ hex => ?_
    rw [ExecS.detIn_inv hex hs]
    refine COut.thenF_of_sim (r := (.error .revert : TRes (Out C σ.H Γ))) (hr.2.2 hc) ?_
    exact he (.halt .revert) (.halt (.det rfl))

/-- **A block that pays nothing, with callbacks.** -/
theorem holdsC_unfold {Γ'' : Ctx} {s : Stmt C Γ Γ'} {P : Prog C Γ Γ''} {e : Ext Γ' Γ''}
    (hs : s.forksIn pay = false) (hP : Prog.callsBack pay P = false)
    (hr : Premise.Runs m s (.unfold P e) σ)
    (h : holdsC I pay σ (.modal m P (.pop .capture e (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  rw [ExecS.detIn_inv he hs]
  have h₁ := COut.thenF_drop _ (h _ (ExecP.of_run hP))
  rw [COut.map_ofRes] at h₁
  refine COut.thenF_of_sim ?_ h₁
  have hr : TRes.Sim ((Prog.runSt σ P).map (State.drop e)) (Stmt.runSt σ s) := hr
  have e₁ : ((Prog.run σ P).map (Out.drop e)).map (·.st) = (Prog.runSt σ P).map (State.drop e) := by
    simp only [Prog.runSt]; cases Prog.run σ P <;> rfl
  rw [e₁]
  exact hr

/-- Capturing `f()` before `e` preserves `f().push(e)` even when either calls back. -/
theorem holdsC_unfoldReceiver {ps Γf Γv : Ctx} {E : Ty} {f : Name}
    {args : Args C Γ ps} {r : Var} {body : Prog C ([.alias (.array E)] ++ ps) Γf}
    {code : Prog C Γ Γv} {value : Src C Γv E} {k : Nat}
    {ω : Prog C Γ Γ₁}
    (h : holdsC I pay σ (.modal m (callReceiverPushCapture k f args r body code value)
      (.pop .capture (.push (.push .refl)) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.callReceiverPush f args r body code value) ω) κ φ) := by
  refine holdsC_cons fun o he => ?_
  obtain ⟨u, hu, rfl⟩ := (NativeDeferred.capture_iff k f args r body code value).mpr he
  exact COut.thenF_drop _ (h _ hu)

/-- **A hidden binder over a program that pays nothing, with callbacks.** -/
theorem holdsC_bind {s : Stmt C Γ Γ'} {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'}
    (hs : s.forksIn pay = false) (hP : Prog.callsBack pay P = false)
    (hr : Premise.Runs m s (.bind x t P) σ)
    (h : holdsC I pay σ (.bind m x t (.modal m P (.seq ω κ) φ))) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  rw [ExecS.detIn_inv he hs]
  obtain ⟨v, hv⟩ := hr
  have h₁ := (Modality.forallB_all h v : holdsC I pay (σ.push v) (.modal m P (.seq ω κ) φ)) _
    (ExecP.of_run hP)
  refine COut.thenF_of_sim (r := Prog.run (σ.push v) P) ?_ h₁
  exact TRes.Sim.of_eq hv

/-- **A split, with callbacks**: the branch its condition picks, whatever
the branches pay. -/
theorem holdsC_split {s : Stmt C Γ Γ} {ω : Prog C Γ Γ₁} {b : BlockKind} {c c' : Fml C Γ}
    {Δ₁ Δ₂ : Ctx} {P : Prog C Γ Δ₁} {Q : Prog C Γ Δ₂} (hr : Premise.Runs m s (.split b c c' P Q) σ)
    (h : holdsC I pay σ (.and (.imp c (Fml.modalK m P (.pop b P.ext (.seq ω κ)) φ))
      (.imp c' (Fml.modalK m Q (.pop b Q.ext (.seq ω κ)) φ)))) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  obtain ⟨hc, hc', hcov, hT, hT'⟩ := hr
  refine holdsC_cons fun o₁ he => ?_
  rcases hcov with hh | hh
  · obtain ⟨o', hP, rfl⟩ := (hc hh).2 _ o₁ he
    have hA := holdsC_modalK σ P _ φ
      (h.1 ((holdsC_iff_holds c (Fml.callsBack_of_hasTransfer c hT) σ).2 hh))
    exact COut.thenF_drop _ (hA o' hP)
  · obtain ⟨o', hQ, rfl⟩ := (hc' hh).2 _ o₁ he
    have hB := holdsC_modalK σ Q _ φ
      (h.2 ((holdsC_iff_holds c' (Fml.callsBack_of_hasTransfer c' hT') σ).2 hh))
    exact COut.thenF_drop _ (hB o' hQ)

/-- `P`'s run, through no frame. -/
theorem Prog.runFrames_nilF {Γ' : Ctx} (σ : State C Γ) (P : Prog C Γ Γ') :
    Prog.runFrames σ P .nil = Prog.runSt σ P := by
  unfold Prog.runFrames Prog.runSt
  cases Prog.run σ P <;> rfl

/-- **A closing taclet, with callbacks** (`revertBox`, a diamond's `false`):
on a statement that hands control to no callee, its premise says how its
run halts. -/
theorem holdsC_done {s : Stmt C Γ Γ'} {b : Bool} (hs : s.forksIn pay = false)
    (hr : Premise.Runs m s (.done b) σ) (h : holdsC I pay σ (if b then .tt else .ff)) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  cases b with
  | false => exact (h trivial).elim
  | true =>
    have H : holds σ (.modal m (.cons s .nil) .nil (.ff : Fml C Γ')) := hr .nil .nil .ff trivial
    change m.afterRunTR _ (Prog.runFrames σ _ .nil) at H
    rw [Prog.runFrames_nilF, Prog.runSt_single] at H
    refine holdsC_cons_det hs (fun τ hτ => ?_) (fun e he => ?_)
    · rw [hτ] at H
      exact ((afterRunTR_ok m _ τ).1 H trivial).elim
    · rw [he] at H
      obtain ⟨h₁, h₂⟩ := (afterRunTR_error m _ e).1 H
      exact ⟨h₂, fun hm => by subst hm; exact h₁⟩

/-- **`assertSimple`, with callbacks**: the condition holds, and the rest
where it does. -/
theorem holdsC_assert {v : Simple C Γ .bool} {ω : Prog C Γ Γ₁}
    (h : holdsC I pay σ (.and (.imp (Fml.isBool v.lower true) (Fml.modalK m ω κ φ))
      (Fml.isBool v.lower true))) :
    holdsC I pay σ (.modal m (.cons (.assert (.simple v)) ω) κ φ) := by
  have hc : holds σ (Fml.isBool v.lower true) := (holdsC_iff_holds _ rfl σ).1 h.2
  have hv : v.evalT σ = true := (holds_isBool σ v true).1 hc
  have hrun : Stmt.runSt σ (.assert (.simple v)) = .ok σ := by
    show (TRun.assert (.simple v) σ).map (·.st) = _
    simp only [TRun.assert, Val.evalT, ok_bind, hv]; rfl
  refine holdsC_cons_det rfl (fun τ hτ => ?_) (fun e he => ?_)
  · rw [hrun] at hτ
    cases hτ
    exact h.1 h.2
  · rw [hrun] at he; cases he

/-- **A block that calls back**: its body, its locals popped, then the rest. -/
theorem holdsC_block {Γ₁' : Ctx} {body : Prog C Γ Γ₁'} {ω : Prog C Γ Γ₁}
    (h : holdsC I pay σ (.modal m body (.pop .capture body.ext (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.block body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  cases he with
  | det hf =>
    have h₁ := COut.thenF_drop _ (h _ (ExecP.of_run (J := I.stateInv pay) hf))
    rw [COut.map_ofRes] at h₁
    exact h₁
  | block _ hp => exact COut.thenF_drop _ (h _ hp)

end Rules

/-! ## The context, read with callbacks -/

section Wrap

open scoped Solidity.Hyps

variable {I : Fml C []} {Γ₀ : Ctx}

/-- Two formulas under the context give a third that follows from both. -/
theorem Hyps.wrapC_and {Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    ∀ {φ ψ χ : Fml C Γ}, (∀ τ, holdsC I pay τ φ → holdsC I pay τ ψ → holdsC I pay τ χ) →
      ∀ σ, holdsC I pay σ (H.wrap φ) → holdsC I pay σ (H.wrap ψ) → holdsC I pay σ (H.wrap χ) := by
  hyps_wrap_and

/-- The context is monotone. -/
theorem Hyps.wrapC_mono {Γ : Ctx} (H : Hyps C Γ₀ Γ) {φ ψ : Fml C Γ}
    (h : ∀ τ, holdsC I pay τ φ → holdsC I pay τ ψ) (σ : State C Γ₀)
    (hφ : holdsC I pay σ (H.wrap φ)) :
    holdsC I pay σ (H.wrap ψ) :=
  H.wrapC_and (fun τ a _ => h τ a) σ hφ hφ

/-- `∀ xs. ψ`, with callbacks, at every typed value of the binders. -/
theorem holdsC_binders_all {Γ ρ : Ctx} (bs : Binders ρ) :
    ∀ (σ : State C Γ) (ψ : Fml C (ρ ++ Γ)) (r : TEnv C σ.H ρ), holdsC I pay σ (bs.all ψ) →
      holdsC I pay (σ.withEnv (TEnv.append ρ r σ.env)) ψ := by
  induction bs with
  | nil => intro σ ψ _ h; exact h
  | snoc bs p x ih =>
    intro σ ψ r h
    exact ih σ (.all x p ψ) r.2 h r.1

end Wrap

/-! ## The callback taclets -/

section Taclets

variable {I : Fml C []} {Γ Γ₁ Γ₀ : Ctx} {σ : State C Γ} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀}
  {φ : Fml C Γ₀}

/-- A transfer's booking, by its no-callback twin's update: where the
transfer returns, the booking ends in its state. -/
theorem transfer_booking (sadr se : Simple C Γ .uint) {o₁ : Out C σ.H Γ}
    (h : TRun.transfer (.simple sadr) (.simple se) σ = .ok o₁) :
    (Upd.nil.snoc (UpdElem.payTo sadr se)).applyP σ = some (o₁.st.glob, o₁.st.locV) :=
  (Stmt.runs 0 .box (.transfer (.simple sadr) (.simple se)) (.upd1 (.payTo sadr se)) rfl σ).1
    o₁.st (by show (TRun.transfer _ _ σ).map _ = _; rw [h]; rfl)

/-- **`transferWithCallbackBox` is sound with callbacks**: the invariant on
exit after the booking, and the rest resumed after the callback, from any
state the callee leaves in which the invariant holds. -/
theorem holdsC_transferCb (hI : I.FO = true) (hT : I.hasTransfer = false)
    (sadr se : Simple C Γ .uint)
    (hx : holdsC I pay σ (.upd .box (Upd.nil.snoc (UpdElem.payTo sadr se)) (Fml.closedAt I)))
    (hr : holdsC I pay σ (.upd .box (Upd.nil.snoc (UpdElem.payTo sadr se))
      (.havoc (.imp (Fml.closedAt I) (Fml.modalK .box ω κ φ))))) :
    holdsC I pay σ (.modal .box (.cons (.transfer (.simple sadr) (.simple se)) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  cases he with
  | det _ =>
    -- `transferSemantics:noCallback`: the callee keeps the state, a resumption
    obtain ⟨o₂, h⟩ : ∃ o₂, TRun.transfer (.simple sadr) (.simple se) σ = .ok o₂ := ⟨_, rfl⟩
    change COut.thenF _ _ _ _ (COut.ofRes (TRun.transfer _ _ σ))
    rw [h]
    have hL := (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec
    have hJ := (holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx hL)
    exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hr hL o₂.st.storage
      o₂.st.net ((holdsC_closedAt_iff hI hT _).2 hJ)))
  | transferHalt _ h => nomatch h
  | transferViolated _ h hn =>
    exact (hn ((holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx
      (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec))).elim
  | transferResume _hp h hJ hJ' =>
    rename_i st nt o₂
    exact COut.after_seq (holdsC_modalK _ ω κ φ
      (Upd.afterT.of_lands hr (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec st nt
        ((holdsC_closedAt_iff hI hT _).2 hJ')))

/-- **`sendWithCallbackBox` is sound with callbacks**: the invariant on exit
after the booking; the rest after the booking and `pv := true`, from any
state the callee leaves in which the invariant holds; the rest after
`pv := false`, nothing booked. -/
theorem holdsC_sendCb {m : Modality} (hI : I.FO = true) (hT : I.hasTransfer = false)
    (pv : Idx Γ (.val .bool))
    (sadr se : Simple C Γ .uint) (full : Bool)
    (hx : holdsC I pay σ (.upd m (Upd.nil.snoc (UpdElem.payTo sadr se)) (Fml.closedAt I)))
    (hok : holdsC I pay σ (.upd m ((Upd.nil.snoc (UpdElem.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (p := .bool) true))))
      (.havoc (.imp (Fml.closedAt I) (Fml.modalK m ω κ φ)))))
    (hf : holdsC I pay σ (.upd m (Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false))))
      (Fml.modalK m ω κ φ))) :
    holdsC I pay σ (.modal m (.cons (.send pv (.simple sadr) (.simple se) full) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  cases he with
  | det _ =>
    -- `transferSemantics:noCallback`: booked or refused, the callee keeping the state
    change COut.thenF _ _ _ _ (COut.ofRes (TRun.send pv (.simple sadr) (.simple se) σ))
    rcases TRun.send_cases pv (.simple sadr) (.simple se) σ with ⟨e, ht, _⟩ | ⟨o₂, ht, hs | hs⟩
    · exact nomatch ht
    · rw [hs]
      have hL := (Upd.lands_of_applyP (transfer_booking sadr se ht)).choose_spec
      have hJ := (holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx hL)
      exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hok
        (Upd.lands_snoc_local hL pv (v := (true : Bool)) rfl) o₂.st.storage o₂.st.net
        ((holdsC_closedAt_iff hI hT _).2 hJ)))
    · rw [hs]
      exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hf
        (Upd.lands_snoc_local (Upd.lands_nil σ) pv (v := (false : Bool)) rfl)))
  | sendHalt _ h => nomatch h
  | sendFailed _ h =>
    exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hf
      (Upd.lands_snoc_local (Upd.lands_nil σ) pv (v := (false : Bool)) rfl)))
  | sendViolated _ h hn =>
    exact (hn ((holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx
      (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec))).elim
  | sendResume _hp h hJ hJ' =>
    rename_i st nt o₂
    exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hok
      (Upd.lands_snoc_local (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec pv
        (v := (true : Bool)) rfl) st nt ((holdsC_closedAt_iff hI hT _).2 hJ')))

/-- **`tryCallWithCallbackBox` is sound with callbacks**: the invariant where
control leaves; the call's success, from any state the callee leaves in which
the invariant holds, for every value of its return data; each clause's block
where the call reverted. -/
theorem holdsC_tryCb (hI : I.FO = true) (hT : I.hasTransfer = false)
    {ρ κc Γok Γe Γ₃ Γ₄ ps Γf : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γok) (err : Prog C Γ Γe)
    (code : CodeBinder κc) (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)
    (hx : holdsC I pay σ (Fml.closedAt I))
    (hok : holdsC I pay σ (.havoc (.imp (Fml.closedAt I) (rets.all
      (Fml.modalK .box ok (.pop .block ((Ext.append Γ ρ).trans ok.ext) (.seq ω κ)) φ)))))
    (herr : holdsC I pay σ (Binders.nil.all
      (Fml.modalK .box err (.pop .block ((Ext.append Γ []).trans err.ext) (.seq ω κ)) φ)))
    (hpnc : holdsC I pay σ (code.binders.all
      (Fml.modalK .box pnc (.pop .block ((Ext.append Γ κc).trans pnc.ext) (.seq ω κ)) φ)))
    (hoth : holdsC I pay σ (Binders.nil.all
      (Fml.modalK .box other (.pop .block ((Ext.append Γ []).trans other.ext) (.seq ω κ)) φ))) :
    holdsC I pay σ (.modal .box (.cons (.tryCall call rets ok err code pnc other sargs sbody false)
      ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  cases he with
  | det hf => nomatch hf
  | tryRevert => exact ⟨trivial, nofun⟩
  | tryDecode hd => exact ⟨trivial, fun he => rets.decodeT_ne_panic _ (he ▸ hd)⟩
  | tryViolated hn => exact (hn ((holdsC_closedAt_iff hI hT σ).1 hx)).elim
  | tryOk hJ hJ' hd hP _hg =>
    rename_i st nt _ _ r o
    have h₁ := hok st nt ((holdsC_closedAt_iff hI hT _).2 hJ')
    have h₂ := holdsC_binders_all rets (σ.havoc st nt) _ r h₁
    exact COut.thenF_drop _ (holdsC_modalK _ ok _ φ h₂ o hP)
  | tryError _ hP =>
    rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at herr
    exact COut.thenF_drop _ (holdsC_modalK σ err _ φ herr _ hP)
  | tryPanic _hsf hP =>
    rename_i v o
    have h₂ := holdsC_binders_all code.binders σ _ (code.decodeT v) hpnc
    exact COut.thenF_drop _ (holdsC_modalK _ pnc _ φ h₂ o hP)
  | tryOther _ hP =>
    rw [show (Ext.append Γ []).trans other.ext = other.ext from Subsingleton.elim _ _] at hoth
    exact COut.thenF_drop _ (holdsC_modalK σ other _ φ hoth _ hP)

/-- A `require` whose condition holds, with callbacks: the rest's runs from
where it is. -/
theorem ExecP.require_true {J : StateInv C} {Δ Δ' : Ctx} {τ : State C Δ}
    {c : Val C Δ .bool} (h : c.evalT τ = .ok true) {P : Prog C Δ Δ'} {o : COut C τ.H Δ'}
    (hP : ExecP J τ P o) :
    ExecP J τ (.cons (.require c) P) (o.map (Out.cat ⟨τ, List.prefix_refl _⟩)) := by
  have hd := ExecS.det (J := J) (σ := τ) (s := .require c) rfl
  have hr : (Stmt.require c).run τ = .ok ⟨τ, List.prefix_refl _⟩ := by
    show TRun.require c τ = _
    simp only [TRun.require, h]
    rfl
  rw [hr] at hd
  exact ExecP.cons hd hP

/-- A run that reverts or panics refutes a diamond, with callbacks. -/
theorem holdsC_not_diamond {Γ₁ Γ₀ : Ctx} {σ : State C Γ} {P : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀}
    {φ : Fml C Γ₀} {e : THalt} (he : e = .revert ∨ e = .panic)
    (h : ExecP (I.stateInv pay) σ P (.halt e)) : ¬ holdsC I pay σ (.modal .diamond P κ φ) := by
  intro hX
  have h' := hX _ h
  rcases he with rfl | rfl
  · exact nomatch h'.1
  · exact h'.2 rfl

/-- Another contract's callee: the self-call's `require` reverts. -/
theorem holdsC_selfFails_notSelf {ρ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (σ : State C Γ)
    (hs : (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1) :
    holdsC I pay σ (call.selfFails rets sargs sbody) := by
  have hd := ExecS.det (J := I.stateInv pay) (σ := σ) (s := .require call.isSelf) rfl
  have hr : (Stmt.require call.isSelf).run σ = .error .revert := by
    show TRun.require call.isSelf σ = _
    simp only [TRun.require, ExtCall.isSelf_evalT, hs, decide_false]
    rfl
  rw [hr] at hd
  exact holdsC_not_diamond (.inl rfl) (ExecP.halt hd)

/-- The contract's own callee, which reverts or panics. -/
theorem holdsC_selfFails_halt {ρ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (σ : State C Γ)
    (hs : (call.addr.evalT σ).1 = σ.tx.selfAddress.1) {e : THalt} (he : e = .revert ∨ e = .panic)
    (hc : ExecS (I.stateInv pay) σ (.call call.fn sargs (.rets rets) sbody) (.halt e)) :
    holdsC I pay σ (call.selfFails rets sargs sbody) := by
  have hi : call.isSelf.evalT σ = .ok true := by
    rw [ExtCall.isSelf_evalT]; simp only [hs, decide_true]
  exact holdsC_not_diamond he (ExecP.require_true hi (ExecP.halt (P := .nil) hc))

/-- **`tryCallSelfBox` is sound with callbacks** (Lean, `docs/options.md`
O8): the invariant where control leaves; the receiver the contract, the
callee's body inlined (its runs with callbacks) then the success block; the
receiver another, the success block from any state the callee leaves in
which the invariant holds; each clause's block where the call reverted. -/
theorem holdsC_trySelfCb (hI : I.FO = true) (hT : I.hasTransfer = false)
    {ρ κc Γok Γe Γ₃ Γ₄ ps Γf : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γok) (err : Prog C Γ Γe)
    (code : CodeBinder κc) (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf)
    (hx : holdsC I pay σ (Fml.closedAt I))
    (h0 : holdsC I pay σ (Binders.nil.all (Fml.modalK .box
      (.cons (.require call.hasCode) (.cons (.require call.isSelf)
        (.cons (.call call.fn sargs (.rets rets) sbody) ok)) : Prog C ([] ++ Γ) Γok)
      (.pop .block ((Ext.append Γ []).trans
        (Prog.cons (.require call.hasCode) (.cons (.require call.isSelf)
          (.cons (.call call.fn sargs (.rets rets) sbody) ok)) : Prog C ([] ++ Γ) Γok).ext)
        (.seq ω κ)) φ)))
    (hok : holdsC I pay σ (.havoc (.imp (Fml.closedAt I) (rets.all (Fml.modalK .box
      (.cons (.require (call.wk (Thin.ofExt (Ext.append Γ ρ))).hasCode)
        (.cons (.require (call.wk (Thin.ofExt (Ext.append Γ ρ))).notSelf) ok))
      (.pop .block ((Ext.append Γ ρ).trans
        (Prog.cons (.require (call.wk (Thin.ofExt (Ext.append Γ ρ))).hasCode)
          (.cons (.require (call.wk (Thin.ofExt (Ext.append Γ ρ))).notSelf) ok)).ext)
        (.seq ω κ)) φ)))))
    (herr : holdsC I pay σ (.imp (call.selfFails rets sargs sbody) (Binders.nil.all
      (Fml.modalK .box err (.pop .block ((Ext.append Γ []).trans err.ext) (.seq ω κ)) φ))))
    (hpnc : holdsC I pay σ (.imp (call.selfFails rets sargs sbody) (code.binders.all
      (Fml.modalK .box pnc (.pop .block ((Ext.append Γ κc).trans pnc.ext) (.seq ω κ)) φ))))
    (hoth : holdsC I pay σ (.imp (call.selfFails rets sargs sbody) (Binders.nil.all
      (Fml.modalK .box other (.pop .block ((Ext.append Γ []).trans other.ext) (.seq ω κ)) φ)))) :
    holdsC I pay σ (.modal .box (.cons (.tryCall call rets ok err code pnc other sargs sbody true)
      ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  cases he with
  | det hf => nomatch hf
  | tryRevert => exact ⟨trivial, nofun⟩
  | tryDecode hd => exact ⟨trivial, fun he => rets.decodeT_ne_panic _ (he ▸ hd)⟩
  | tryViolated hn => exact (hn ((holdsC_closedAt_iff hI hT σ).1 hx)).elim
  | tryOk hJ hJ' hd hP hg =>
    rename_i st nt _ _ r o
    obtain ⟨hz, hs⟩ := hg rfl
    have h₁ := hok st nt ((holdsC_closedAt_iff hI hT _).2 hJ')
    have h₂ := holdsC_modalK _ _ _ φ (holdsC_binders_all rets (σ.havoc st nt) _ r h₁)
    have ha : (call.wk (Thin.ofExt (Ext.append Γ ρ))).addr.evalT
        ((σ.havoc st nt).withEnv (TEnv.append ρ r σ.env)) = call.addr.evalT σ :=
      ExtCall.addr_wk_append call (σ.havoc st nt) r
    have hc : (call.wk (Thin.ofExt (Ext.append Γ ρ))).hasCode.evalT
        ((σ.havoc st nt).withEnv (TEnv.append ρ r σ.env)) = .ok true := by
      rw [ExtCall.hasCode_evalT, ha]; simp only [hz, decide_false, Bool.not_false]
    have hn : (call.wk (Thin.ofExt (Ext.append Γ ρ))).notSelf.evalT
        ((σ.havoc st nt).withEnv (TEnv.append ρ r σ.env)) = .ok true := by
      rw [ExtCall.notSelf_evalT, ha]
      show Except.ok (!decide ((call.addr.evalT σ).1 = σ.tx.selfAddress.1)) = _
      simp only [hs, decide_false, Bool.not_false]
    have h₃ := h₂ _ (ExecP.require_true hc (ExecP.require_true hn hP))
    rw [COut.thenF_map_cat, COut.thenF_map_cat] at h₃
    rw [show (Ext.append Γ ρ).trans ok.ext = (Ext.append Γ ρ).trans
      (Prog.cons (.require (call.wk (Thin.ofExt (Ext.append Γ ρ))).hasCode)
        (.cons (.require (call.wk (Thin.ofExt (Ext.append Γ ρ))).notSelf) ok)).ext from
      Subsingleton.elim _ _]
    exact COut.thenF_drop _ h₃
  | tryError hsf hP =>
    have herr := herr (holdsC_selfFails_notSelf call rets sargs sbody σ (hsf rfl))
    rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at herr
    exact COut.thenF_drop _ (holdsC_modalK σ err _ φ herr _ hP)
  | tryPanic hsf hP =>
    rename_i v o
    have h₂ := holdsC_binders_all code.binders σ _ (code.decodeT v)
      (hpnc (holdsC_selfFails_notSelf call rets sargs sbody σ (hsf rfl)))
    exact COut.thenF_drop _ (holdsC_modalK _ pnc _ φ h₂ o hP)
  | tryOther hsf hP =>
    have hoth := hoth (holdsC_selfFails_notSelf call rets sargs sbody σ (hsf rfl))
    rw [show (Ext.append Γ []).trans other.ext = other.ext from Subsingleton.elim _ _] at hoth
    exact COut.thenF_drop _ (holdsC_modalK σ other _ φ hoth _ hP)
  | trySelfError _ hs hc hP =>
    have herr := herr (holdsC_selfFails_halt call rets sargs sbody σ hs (.inl rfl) hc)
    rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at herr
    exact COut.thenF_drop _ (holdsC_modalK σ err _ φ herr _ hP)
  | trySelfPanic _hz hs hc hP =>
    rename_i v o
    have h₂ := holdsC_binders_all code.binders σ _ (code.decodeT v)
      (hpnc (holdsC_selfFails_halt call rets sargs sbody σ hs (.inr rfl) hc))
    exact COut.thenF_drop _ (holdsC_modalK _ pnc _ φ h₂ o hP)
  | trySelfOther _ hs hc hP =>
    have hoth := hoth (holdsC_selfFails_halt call rets sargs sbody σ hs (.inl rfl) hc)
    rw [show (Ext.append Γ []).trans other.ext = other.ext from Subsingleton.elim _ _] at hoth
    exact COut.thenF_drop _ (holdsC_modalK σ other _ φ hoth _ hP)
  | trySelfOk hz hs hc hP =>
    rename_i o₁ o
    have hc0 : call.hasCode.evalT σ = .ok true := by
      rw [ExtCall.hasCode_evalT]; simp only [hz, decide_false, Bool.not_false]
    have hi : call.isSelf.evalT σ = .ok true := by
      rw [ExtCall.isSelf_evalT]; simp only [hs, decide_true]
    have h₃ := holdsC_modalK σ (.cons (.require call.hasCode) (.cons (.require call.isSelf)
        (.cons (.call call.fn sargs (.rets rets) sbody) ok))) _ φ h0 _
      (ExecP.require_true hc0 (ExecP.require_true hi (ExecP.cons hc hP)))
    rw [COut.thenF_map_cat, COut.thenF_map_cat, show (Ext.append Γ []).trans
      (Prog.cons (.require call.hasCode) (.cons (.require call.isSelf)
        (.cons (.call call.fn sargs (.rets rets) sbody) ok))).ext =
      (Ext.append Γ ρ).trans ok.ext from Subsingleton.elim _ _] at h₃
    cases o with
    | ok o' => exact fun o'' he => h₃ o'' (.pop he)
    | halt _ => exact h₃
    | violated => exact h₃
  | trySelfHalt _ _ _ _ h2 => exact ⟨trivial, h2⟩
  | trySelfViolated hz hs hc =>
    have hc0 : call.hasCode.evalT σ = .ok true := by
      rw [ExtCall.hasCode_evalT]; simp only [hz, decide_false, Bool.not_false]
    have hi : call.isSelf.evalT σ = .ok true := by
      rw [ExtCall.isSelf_evalT]; simp only [hs, decide_true]
    exact holdsC_modalK σ (.cons (.require call.hasCode) (.cons (.require call.isSelf)
        (.cons (.call call.fn sargs (.rets rets) sbody) ok))) _ φ h0 _
      (ExecP.require_true hc0 (ExecP.require_true hi (ExecP.violated hc)))

/-- **`sendNoCallbackBox`, with callbacks unset**: a gas-limited send runs as
its typed run, the payment booked and `pv` true, or nothing booked and `pv`
false. -/
theorem holdsC_sendDet {m : Modality} (hp : pay = false) (pv : Idx Γ (.val .bool))
    (sadr se : Simple C Γ .uint)
    (hok : holdsC I pay σ (.upd m ((Upd.nil.snoc (UpdElem.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (p := .bool) true)))) (Fml.modalK m ω κ φ)))
    (hf : holdsC I pay σ (.upd m (Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false))))
      (Fml.modalK m ω κ φ))) :
    holdsC I pay σ (.modal m (.cons (.send pv (.simple sadr) (.simple se) false) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  rw [ExecS.detIn_inv he (by show (pay || false) = false; rw [hp]; rfl)]
  change COut.thenF _ _ _ _ (COut.ofRes (TRun.send pv (.simple sadr) (.simple se) σ))
  rcases TRun.send_cases pv (.simple sadr) (.simple se) σ with ⟨e, ht, _⟩ | ⟨o₂, ht, hs | hs⟩
  · exact nomatch ht
  · rw [hs]
    have hL := (Upd.lands_of_applyP (transfer_booking sadr se ht)).choose_spec
    exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hok
      (Upd.lands_snoc_local hL pv (v := (true : Bool)) rfl)))
  · rw [hs]
    exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hf
      (Upd.lands_snoc_local (Upd.lands_nil σ) pv (v := (false : Bool)) rfl)))

end Taclets

/-! ## A call, with callbacks

`Stmt.step`'s premise for a call inlines its body (`callStep`): the
parameters declared with the arguments (`Args.declsThen`), the body weakened
under the caller's locals (`Thin.atop`) as a block.  With callbacks the call
runs its body in its own frame (`ExecS.callBody`); the inlined block runs the
weakened body, which has the same runs, lifted (`Prog.exec_wk`). -/

section Calls

open DeferredSource.Callback (map_cat_refl singleton_iff block_of_execP)

variable {I : Fml C []} {J : StateInv C}

/-- A callback run from a state equal to another, the outcome at a heap
both have: from the other.  At states whose heaps reduce to the same one
(`hX hY := rfl`), the casts are the identity. -/
theorem ExecS.transport {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {H : HTy} {X Y : State C Γ}
    (hX : X.H = H) (hY : Y.H = H) (e : X = Y) {u : COut C H Γ'} (h : ExecS J X s (hX ▸ u)) :
    ExecS J Y s (hY ▸ u) := by
  subst e; subst hX; exact h

/-- A statement that hands control to nobody and ends in `τ` has that
callback run. -/
theorem ExecS.det_ok {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {σ : State C Γ} {τ : State C Γ'}
    (hs : s.forksIn J.pay = false) (h : Stmt.runSt σ s = .ok τ) :
    ∃ e : σ.H <+: τ.H, ExecS J σ s (.ok ⟨τ, e⟩) := by
  have hd := ExecS.det (J := J) (σ := σ) hs
  cases hr : s.run σ with
  | error e => simp only [Stmt.runSt, hr, Except.map, reduceCtorEq] at h
  | ok o =>
    rw [hr] at hd
    simp only [Stmt.runSt, hr, Except.map, Except.ok.injEq] at h
    subst h
    exact ⟨o.ext, hd⟩

/-- **The parameters declared, with callbacks**: they hand control to nobody,
so the rest runs from the arguments pushed. -/
theorem Args.execP_declsThen {Γ Δ : Ctx} : {ps : Ctx} → (as : Args C Γ ps) →
    (rest : Prog C (ps ++ Γ) Δ) → (σ : State C Γ) → (a : TEnv C σ.H ps) → as.evalT σ = .ok a →
    ∀ {u : COut C σ.H Δ}, ExecP J (σ.withEnv (TEnv.append ps a σ.env)) rest u →
      ExecP J σ (as.declsThen rest) u
  | _, .nil, _, _, _, _, _, h => h
  | _, .snoc (ps := ps') as p x e, rest, σ, a, ha, u, h => by
    obtain ⟨v, a'⟩ := a
    rw [Args.evalT_snoc] at ha
    cases ha' : as.evalT σ with
    | error => rw [ha'] at ha; cases ha
    | ok a'' =>
      rw [ha'] at ha
      cases hv : e.evalT σ with
      | error => simp only [hv, bind, Except.bind] at ha; cases ha
      | ok v' =>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        refine Args.execP_declsThen as _ σ a'' ha' ?_
        obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps' a'' σ.env))
          (s := .declLocal p x (some (e.unders ps'))) rfl
          (by rw [Stmt.runSt_declLocal, Val.evalT_unders, hv]; rfl)
        simpa only [map_cat_refl] using ExecP.cons hd h
  | _, .snocStorage (ps := ps') as R x e, rest, σ, a, ha, u, h => by
    obtain ⟨v, a'⟩ := a
    rw [Args.evalT_snocStorage] at ha
    cases ha' : as.evalT σ with
    | error => rw [ha'] at ha; cases ha
    | ok a'' =>
      rw [ha'] at ha
      cases hv : e.resolveT σ with
      | error => simp only [hv, bind, Except.bind] at ha; cases ha
      | ok q =>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        refine Args.execP_declsThen as _ σ a'' ha' ?_
        obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps' a'' σ.env))
          (s := .declStorage R x (some (.path (e.unders ps')))) rfl
          (by rw [Stmt.runSt_declStorage, SPath.resolveT_unders, hv]; rfl)
        simpa only [map_cat_refl] using ExecP.cons hd h
  | _, .snocMemory (ps := ps') as R x e, rest, σ, a, ha, u, h => by
    obtain ⟨v, a'⟩ := a
    rw [Args.evalT_snocMemory] at ha
    cases ha' : as.evalT σ with
    | error => rw [ha'] at ha; cases ha
    | ok a'' =>
      rw [ha'] at ha
      cases hv : e.mvalT σ with
      | error => simp only [hv, bind, Except.bind] at ha; cases ha
      | ok q =>
        simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        refine Args.execP_declsThen as _ σ a'' ha' ?_
        obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps' a'' σ.env))
          (s := .declMem R x (some (.alias (e.unders ps'))) rfl e.mapFree) rfl
          (by rw [Stmt.runSt_declMem, MPath.mvalT_unders, hv]; rfl)
        simpa only [map_cat_refl] using ExecP.cons hd h

/-- A statement that hands control to nobody and halts has that callback run. -/
theorem ExecS.det_err {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {σ : State C Γ} {e : THalt}
    (hs : s.forksIn J.pay = false) (h : Stmt.runSt σ s = .error e) :
    ExecS J σ s (.halt e) := by
  have hd := ExecS.det (J := J) (σ := σ) hs
  cases hr : s.run σ with
  | ok o => simp only [Stmt.runSt, hr, Except.map, reduceCtorEq] at h
  | error e' =>
    rw [hr] at hd
    simp only [Stmt.runSt, hr, Except.map, Except.error.injEq] at h
    subst h
    exact hd

/-- The parameters declared, an argument halting: the declarations halt. -/
theorem Args.execP_declsThen_halt {Γ Δ : Ctx} : {ps : Ctx} → (as : Args C Γ ps) →
    (rest : Prog C (ps ++ Γ) Δ) → (σ : State C Γ) → {e : THalt} → as.evalT σ = .error e →
      ExecP J σ (as.declsThen rest) (.halt e)
  | _, .nil, _, _, _, h => nomatch h
  | _, .snoc (ps := ps') as p x v, rest, σ, e, ha => by
    rw [Args.evalT_snoc] at ha
    cases ha' : as.evalT σ with
    | error e' =>
      rw [ha'] at ha; cases ha
      exact Args.execP_declsThen_halt as _ σ ha'
    | ok a'' =>
      rw [ha'] at ha
      cases hv : v.evalT σ with
      | ok => simp only [hv, bind, Except.bind, pure, Except.pure, reduceCtorEq] at ha
      | error e' =>
        simp only [hv, bind, Except.bind, Except.error.injEq] at ha
        subst ha
        refine Args.execP_declsThen as _ σ a'' ha' (.halt (ExecS.det_err rfl ?_))
        rw [Stmt.runSt_declLocal, Val.evalT_unders, hv]; rfl
  | _, .snocStorage (ps := ps') as R x v, rest, σ, e, ha => by
    rw [Args.evalT_snocStorage] at ha
    cases ha' : as.evalT σ with
    | error e' =>
      rw [ha'] at ha; cases ha
      exact Args.execP_declsThen_halt as _ σ ha'
    | ok a'' =>
      rw [ha'] at ha
      cases hv : v.resolveT σ with
      | ok => simp only [hv, bind, Except.bind, pure, Except.pure, reduceCtorEq] at ha
      | error e' =>
        simp only [hv, bind, Except.bind, Except.error.injEq] at ha
        subst ha
        refine Args.execP_declsThen as _ σ a'' ha' (.halt (ExecS.det_err rfl ?_))
        rw [Stmt.runSt_declStorage, SPath.resolveT_unders, hv]; rfl
  | _, .snocMemory (ps := ps') as R x v, rest, σ, e, ha => by
    rw [Args.evalT_snocMemory] at ha
    cases ha' : as.evalT σ with
    | error e' =>
      rw [ha'] at ha; cases ha
      exact Args.execP_declsThen_halt as _ σ ha'
    | ok a'' =>
      rw [ha'] at ha
      cases hv : v.mvalT σ with
      | ok => simp only [hv, bind, Except.bind, pure, Except.pure, reduceCtorEq] at ha
      | error e' =>
        simp only [hv, bind, Except.bind, Except.error.injEq] at ha
        subst ha
        refine Args.execP_declsThen as _ σ a'' ha' (.halt (ExecS.det_err rfl ?_))
        rw [Stmt.runSt_declMem, MPath.mvalT_unders, hv]; rfl

/-- Two outcomes over a heap end alike when their states do. -/
theorem Out.eq_of_st {H : HTy} {Γ : Ctx} {a b : Out C H Γ} (h : a.st = b.st) : a = b := by
  cases a; cases b; cases h; rfl

/-- `TEnv.put_atop` at a frame read as `[] ++ ps`, a call's with no return
variable. -/
theorem TEnv.put_atop_nil {H : HTy} {Γ : Ctx} (ps : Ctx) (x : TEnv C H ([] ++ ps))
    (d : TEnv C H (ps ++ Γ)) :
    TEnv.put (Thin.atop ps Γ) x d = TEnv.append ps x (TEnv.drop (Ext.append Γ ps) d) :=
  TEnv.put_atop ps x d

/-- **A call with no result, with callbacks, is its inlined body**
(`Premise.sound_callNone`'s program): the parameters declared, the body
lifted under the caller's locals as a block, the parameters popped. -/
theorem ExecS.callNone_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
    {body : Prog C ([] ++ ps) Γf} {o : COut C σ.H Γ}
    (he : ExecS J σ (.call f args .none body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil)) u ∧
      o = u.map (Out.drop (Ext.append Γ ps)) := by
  cases he with
  | det h => exact nomatch h
  | callArgs ha => exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  | @callBody _ _ _ _ _ _ _ _ _ _ a o' ha hp =>
    obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop ps Γ) (σ.withEnv a)
      (TEnv.append ps a σ.env) hp
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv a).lift (Thin.atop ps Γ) (TEnv.append ps a σ.env))
      (Y := σ.withEnv (TEnv.append ps a σ.env)) rfl rfl (State.withEnv_append_lift σ a).symm
      (block_of_execP hw)
    refine ⟨_, Args.execP_declsThen args _ σ a ha (singleton_iff.mpr hb), ?_⟩
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop ps Γ)) hr).eq_lifted
    rw [hl]
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, TRun.callLeave, State.lift, State.drop, State.withEnv,
        CallRet.leaveT]
      exact congrArg (fun E => (State.mk x.st.storage x.st.H x.st.heap E x.st.net
        x.st.selfBalance x.st.tx : State C Γ)) (TEnv.drop_put_atop_wk (Γ := Γ) _ ps _ a σ.env).symm
    | halt => rfl
    | violated => rfl

/-- **The return variables declared, with callbacks**, at their defaults. -/
theorem Binders.execP_declsThen {Γ Δ : Ctx} : {ρ : Ctx} → (bs : Binders ρ) →
    (rest : Prog C (ρ ++ Γ) Δ) → (σ : State C Γ) → ∀ {u : COut C σ.H Δ},
      ExecP J (σ.withEnv (TEnv.append ρ (bs.defaultsT (C := C)) σ.env)) rest u →
        ExecP J σ (bs.declsThen rest) u
  | _, .nil, _, _, _, h => h
  | _, .snoc (ρ := ρ') bs p x, rest, σ, u, h => by
    refine Binders.execP_declsThen bs _ σ ?_
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J)
      (σ := σ.withEnv (TEnv.append ρ' (bs.defaultsT (C := C)) σ.env))
      (s := .declLocal p x none) rfl (Stmt.runSt_declLocal_none p x _)
    simpa only [map_cat_refl] using ExecP.cons hd h

/-- A call's callback runs: its arguments halt, or its body runs in its frame
(`ExecS.callArgs`, `ExecS.callBody`). -/
theorem ExecS.call_inv {Γ Γ' ps rs Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
    {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf} {o : COut C σ.H Γ'}
    (he : ExecS J σ (.call f args ret body) o) :
    (∃ e, args.evalT σ = .error e ∧ o = .halt e) ∨
    ∃ (a : TEnv C σ.H ps) (o' : COut C (ret.enterT (σ.withEnv a)).st.H Γf),
      args.evalT σ = .ok a ∧ ExecP J (ret.enterT (σ.withEnv a)).st body o' ∧
      o = o'.map (TRun.callLeave ret body.ext σ (ret.enterT (σ.withEnv a))) := by
  cases he with
  | det h => exact nomatch h
  | callArgs ha => exact .inl ⟨_, ha, rfl⟩
  | callBody ha hp => exact .inr ⟨_, _, ha, hp, rfl⟩

/-- **A call of several results, with callbacks, is its inlined body**
(`Premise.sound_callRets`' program): the parameters declared, the return
variables at their defaults, the body lifted under the caller's locals as a
block, the parameters thinned out from under the return variables. -/
theorem ExecS.callRets_inline {Γ ps rs Γf : Ctx} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {bs : Binders rs} {body : Prog C (rs ++ ps) Γf} {o : COut C σ.H (rs ++ Γ)}
    (he : ExecS J σ (.call f args (.rets bs) body) o) :
    ∃ u, ExecP J σ (args.declsThen (bs.declsThen
        (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil))) u ∧
      o = u.map fun x => ⟨x.st.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))), x.ext⟩ := by
  rcases ExecS.call_inv he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.keepAll rs (Thin.atop ps Γ))
      (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a))
      (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)) hp
    have hs : (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)).lift
          (Thin.keepAll rs (Thin.atop ps Γ))
          (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)) =
        (σ.withEnv (TEnv.append ps a σ.env)).withEnv
          (TEnv.append rs (bs.defaultsT (C := C)) (σ.withEnv (TEnv.append ps a σ.env)).env) := by
      simp only [State.lift, State.withEnv, TEnv.put_keepAll, TEnv.put_atop, TEnv.drop_append]
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) a)).lift
          (Thin.keepAll rs (Thin.atop ps Γ))
          (TEnv.append rs (bs.defaultsT (C := C)) (TEnv.append ps a σ.env)))
      (Y := (σ.withEnv (TEnv.append ps a σ.env)).withEnv
          (TEnv.append rs (bs.defaultsT (C := C)) (σ.withEnv (TEnv.append ps a σ.env)).env))
      rfl rfl hs (block_of_execP hw)
    refine ⟨_, Args.execP_declsThen args _ σ a ha
      (Binders.execP_declsThen bs _ _ (singleton_iff.mpr hb)), ?_⟩
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.keepAll rs (Thin.atop ps Γ)))
      hr).eq_lifted
    rw [hl]
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, TRun.callLeave, State.lift, State.drop, State.thin,
        State.withEnv, CallRet.leaveT]
      exact congrArg (fun E => (State.mk x.st.storage x.st.H x.st.heap E x.st.net
        x.st.selfBalance x.st.tx : State C (rs ++ Γ)))
        (TEnv.thin_put_keepAllAtop _ _ _ a σ.env).symm
    | halt => rfl
    | violated => rfl

/-- An outcome's state thinned, read through the frames that thin it. -/
theorem COut.thenF_thin {H : HTy} {Γ Γ' Γ₀ : Ctx} {e : Thin Γ Γ'} {κ : Frames C Γ Γ₀}
    {m : Modality} {p : State C Γ₀ → Prop} (o : COut C H Γ')
    (h : o.thenF J (.drop e κ) m p) :
    (o.map fun x => ⟨x.st.thin e, x.ext⟩).thenF J κ m p := by
  cases o with
  | ok o => exact fun o' he => h o' (.drop he)
  | halt _ => exact h
  | violated => exact h

/-- **A call of several results, with callbacks**: its inlined body, the
parameters thinned out. -/
theorem holdsC_callRets {Γ ps rs Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {bs : Binders rs} {body : Prog C (rs ++ ps) Γf}
    {ω : Prog C (rs ++ Γ) Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (bs.declsThen
        (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
      (.drop (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.rets bs) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callRets_inline he
  exact COut.thenF_thin _ (h _ hu)

/-- **A call with no result, with callbacks**: its inlined body, the
parameters popped. -/
theorem holdsC_callNone {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {body : Prog C ([] ++ ps) Γf} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀}
    {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m
      (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))
      (.pop .capture (Ext.append Γ ps) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args .none body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callNone_inline he
  exact COut.thenF_drop _ (h _ hu)

end Calls

/-! ## Soundness -/

theorem holdsC_and_intro {I : Fml C []} {Γ : Ctx} {τ : State C Γ} {φ ψ : Fml C Γ}
    (a : holdsC I pay τ φ) (b : holdsC I pay τ ψ) : holdsC I pay τ (.and φ ψ) := ⟨a, b⟩

theorem holdsC_and_left {I : Fml C []} {Γ : Ctx} {τ : State C Γ} {φ ψ : Fml C Γ}
    (h : holdsC I pay τ (.and φ ψ)) : holdsC I pay τ φ := h.1

theorem holdsC_and_right {I : Fml C []} {Γ : Ctx} {τ : State C Γ} {φ ψ : Fml C Γ}
    (h : holdsC I pay τ (.and φ ψ)) : holdsC I pay τ ψ := h.2

/-- **Soundness of the calculus with callbacks**, for a first-order invariant
with no payment in it: what `ProvesC I pay H φ` proves holds, its context in
front, when the callees `pay` says may call back. -/
theorem ProvesC.sound_of {I : Fml C []} (hI : I.FO = true) (hT : I.hasTransfer = false)
    {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ} (d : ProvesC I pay Γ₀ H φ) :
    ∀ σ, holdsC I pay σ (H.wrap φ) := by
  induction d with
  | plain h hφ => exact fun σ => (holdsC_iff_holds _ hφ σ).2 (Proves.sound h σ)
  | intro _ ih => exact ih
  | @notLeft Γ H X φ _ ih =>
    exact fun σ => Hyps.wrapC_mono (ψ := .imp (.not X) φ) _ (fun _ hX hn => (hn hX).elim) σ (ih σ)
  | @hideLeft Γ H a φ _ ih =>
    exact fun σ => Hyps.wrapC_mono (ψ := .imp a φ) _ (fun _ h _ => h) σ (ih σ)
  | allIntro _ ih => exact ih
  | updIntro _ ih => exact ih
  | bindIntro _ ih => exact ih
  | update d hs _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_update hs
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | updates d hs _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_updates hs
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | guardedUpdates d hs _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_guardedUpdates hs (Stmt.runs _ _ _ _ d.toStep τ)
      (holdsC_and_intro a b)
  | unfold d hs hP _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_unfold hs hP
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | unfoldReceiver _ _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_unfoldReceiver h) σ (ih σ)
  | bind d hs hP _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_bind hs hP
      (Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | split d _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_split (Stmt.runs _ _ _ _ d.toStep τ) (holdsC_and_intro a b)
  | @empty Γ Γ₂ H m κ φ _ ih =>
    exact fun σ => H.wrapC_mono (φ := κ.exit m φ) (ψ := .modal m .nil κ φ)
      (fun τ h o ho => by cases ho; exact holdsC_exit_after κ φ τ h) σ (ih σ)
  | done d hs _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun τ h => holdsC_done hs
      (by exact Stmt.runs _ _ _ _ d.toStep τ) h) σ (ih σ)
  | assert _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_assert (holdsC_and_intro a b)
  | sendDet hp _ _ iho ihf =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (iho σ) (ihf σ)
    exact fun τ a b => holdsC_sendDet hp _ _ _ a b
  | block _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_block h) σ (ih σ)
  | callNone _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callNone h) σ (ih σ)
  | callRets _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callRets h) σ (ih σ)
  | callback d _ _ ihx ihr =>
    cases d
    exact fun σ => Hyps.wrapC_and _ (fun τ a b => holdsC_transferCb hI hT _ _ a b) σ
      (ihx σ) (ihr σ)
  | send d _ _ _ ihx iho ihf =>
    cases d
    intro σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ) (iho σ)) (ihf σ)
    exact fun τ ab c => holdsC_sendCb hI hT _ _ _ _ (holdsC_and_left ab) (holdsC_and_right ab) c
  | sendD d _ _ _ _ _ ihx iho ihf =>
    cases d
    intro σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ) (iho σ)) (ihf σ)
    exact fun τ ab c => holdsC_sendCb hI hT _ _ _ _ (holdsC_and_left ab) (holdsC_and_right ab) c
  | sendDetD hp _ _ _ _ iho ihf =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (iho σ) (ihf σ)
    exact fun τ a b => holdsC_sendDet hp _ _ _ a b
  | tryCall d _ _ _ ihx iho ihc =>
    cases d
    intro σ
    have h₁ := ihc _ List.mem_cons_self σ
    have h₂ := ihc _ (List.mem_cons_of_mem _ List.mem_cons_self) σ
    have h₃ := ihc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ) (iho σ))
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₁
        (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₂ h₃))
    exact fun τ ab cd => holdsC_tryCb hI hT _ _ _ _ _ _ _ _ _ (holdsC_and_left ab)
      (holdsC_and_right ab) (holdsC_and_left cd) (holdsC_and_left (holdsC_and_right cd))
      (holdsC_and_right (holdsC_and_right cd))
  | trySelf d _ _ _ _ ihx ih0 iho ihc =>
    cases d
    intro σ
    have h₁ := ihc _ List.mem_cons_self σ
    have h₂ := ihc _ (List.mem_cons_of_mem _ List.mem_cons_self) σ
    have h₃ := ihc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) σ
    refine Hyps.wrapC_and _ ?_ σ
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ihx σ)
        (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ (ih0 σ) (iho σ)))
      (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₁
        (Hyps.wrapC_and _ (fun _ a b => holdsC_and_intro a b) σ h₂ h₃))
    exact fun τ ab cd => holdsC_trySelfCb hI hT _ _ _ _ _ _ _ _ _ (holdsC_and_left ab)
      (holdsC_and_left (holdsC_and_right ab)) (holdsC_and_right (holdsC_and_right ab))
      (holdsC_and_left cd) (holdsC_and_left (holdsC_and_right cd))
      (holdsC_and_right (holdsC_and_right cd))

/-- **A derivation from the empty context proves validity with callbacks**
(the invariant first-order, `Invariant.fo`). -/
theorem ProvesC.valid {I : Invariant C} {φ : Fml C []}
    (d : ProvesC I.fml pay [] .nil φ) : ValidC I φ pay :=
  ProvesC.sound_of I.fo I.noTransfer d

/-- The same, for a transfer semantics (`ValidT`). -/
theorem ProvesC.validT {ts : TransferSem C} {φ : Fml C []}
    (d : ProvesC ts.inv.fml ts.pay [] .nil φ) : ValidT ts φ :=
  ProvesC.valid d

/-! ## The invariant assumed, opened at its scope

Past a frame end that drops every local, the invariant assumed reads the
global part only; where it is a closed first-order formula it is that
formula read at the scope it is assumed in (`Fml.reclose?`), first-order,
which the closer reads (`Proves.openInv`, at a leaf). -/

/-- A closed term, read at another scope: at the empty scope
(`Tm.toNil?`), then at `Γ'` (`Tm.ofNil`). -/
def Tm.reclose? {Γ Γ' : Ctx} {s : Srt} (t : Tm C Γ s) : Option (Tm C Γ' s) :=
  t.toNil?.map Tm.ofNil

/-- A closed first-order formula, read at another scope. -/
def Fml.reclose? {Γ Γ' : Ctx} : Fml C Γ → Option (Fml C Γ')
  | .tt => some .tt
  | .eq a b => do pure (.eq (← a.reclose?) (← b.reclose?))
  | .wellFormed t => (t.reclose?).map .wellFormed
  | .not φ => (Fml.reclose? φ).map .not
  | .and φ ψ => do pure (.and (← Fml.reclose? φ) (← Fml.reclose? ψ))
  | .imp φ ψ => do pure (.imp (← Fml.reclose? φ) (← Fml.reclose? ψ))
  | _ => none

/-- An assumption opened: the invariant past a frame end that drops every
local, read at the scope. -/
def Fml.openInv {Γ : Ctx} : Fml C Γ → Fml C Γ
  | .upd .box (.drop .nil h) φ => match Fml.reclose? (Γ' := Γ) φ with
    | some φ' => φ'
    | none => .upd .box (.drop .nil h) φ
  | φ => φ

/-- The context with each assumed invariant opened. -/
def Hyps.openInv {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → Hyps C Γ₀ Γ
  | _, .nil => .nil
  | _, .pre H a => .pre (Hyps.openInv H) a.openInv
  | _, .upd H m U => .upd (Hyps.openInv H) m U
  | _, .havoc H => .havoc (Hyps.openInv H)
  | _, .all H x p => .all (Hyps.openInv H) x p
  | _, .bind H m x t => .bind (Hyps.openInv H) m x t
  | _, .anon H xs => .anon (Hyps.openInv H) xs

theorem Tm.reclose_eval {Γ Γ' : Ctx} {s : Srt} {t : Tm C Γ s} {t' : Tm C Γ' s}
    (h : t.reclose? = some t') (σ : State C Γ) (τ : State C Γ') (hg : σ.glob = τ.glob) :
    Srt.SameO s (t'.eval τ) (t.eval σ) := by
  obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Tm.eval_ofNil τ, Tm.eval_toNilS σ t ht₀]
  have key : ∀ g g' : State C [], g = g' → Srt.SameO s (t₀.eval g') (t₀.eval g) := by
    intro g g' e; subst e; exact Srt.SameO.refl _ _
  exact key _ _ hg

theorem Tm.reclose_denote {Γ Γ' : Ctx} {s : Srt} {t : Tm C Γ s} {t' : Tm C Γ' s}
    (h : t.reclose? = some t') (σ : State C Γ) (τ : State C Γ') (hg : σ.glob = τ.glob) :
    t'.denote τ = t.denote σ := by
  obtain ⟨t₀, ht₀, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Tm.denote_ofNil τ, Tm.denote_toNilS σ t ht₀]
  show t₀.denote τ.glob = t₀.denote σ.glob
  rw [hg]

/-- **A closed formula reads alike at another scope**, over the same global
part. -/
theorem holds_reclose {Γ Γ' : Ctx} : (φ : Fml C Γ) → {φ' : Fml C Γ'} → φ.reclose? = some φ' →
    (σ : State C Γ) → (τ : State C Γ') → σ.glob = τ.glob →
      (holds τ φ' ↔ holds σ φ)
  | .tt, _, h, _, _, _ => by cases h; exact Iff.rfl
  | .eq a b, _, h, σ, τ, hg => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rw [holds_eq, holds_eq, Tm.reclose_denote ha _ _ hg, Tm.reclose_denote hb _ _ hg]
  | .wellFormed t, _, h, σ, τ, hg => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [holds_wellFormed, holds_wellFormed, Srt.sameO_st.1 (Tm.reclose_eval ht _ _ hg)]
  | .not φ, _, h, σ, τ, hg => by
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact not_congr (holds_reclose φ hφ σ τ hg)
  | .and φ ψ, _, h, σ, τ, hg => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact and_congr (holds_reclose φ hφ σ τ hg) (holds_reclose ψ hψ σ τ hg)
  | .imp φ ψ, _, h, σ, τ, hg => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact imp_congr (holds_reclose φ hφ σ τ hg) (holds_reclose ψ hψ σ τ hg)
  | .upd .., _, h, _, _, _ | .modal .., _, h, _, _, _ | .havoc _, _, h, _, _, _
  | .all .., _, h, _, _, _ | .bind .., _, h, _, _, _ | .anon .., _, h, _, _, _ => nomatch h

/-! ### The invariant assumed, at the end of a resumed program

"Resume after callback" assumes the invariant past a frame end that drops
every local (`Fml.closedAt`), and a goal past a program that ends where
it is resumed is the postcondition past the frames' scope ends
(`Frames.exit`).  Where the goal is the invariant read at its scope (a
closed first-order formula, `Fml.reclose?`), the assumption is the goal:
`Proves.assumeInv`, KeY's `close` on `I ⟹ I`. -/

/-- Frames that only end scopes. -/
def Frames.popsOnly {Γ Γ₀ : Ctx} : Frames C Γ Γ₀ → Bool
  | .nil => true
  | .seq .nil κ => Frames.popsOnly κ
  | .seq (.cons ..) _ => false
  | .pop _ _ κ | .drop _ κ => Frames.popsOnly κ

/-- Past scope ends, a closed formula holds where the formula it reads as
at the empty scope holds, over the same global part. -/
theorem holds_exit_closed {Γ₀ : Ctx} {φ : Fml C Γ₀} {I : Fml C []} (hφ : φ.reclose? = some I)
    {τ₀ : State C []} (h : holds τ₀ I) :
    {Γ : Ctx} → (κ : Frames C Γ Γ₀) → κ.popsOnly = true → ∀ σ : State C Γ,
      σ.glob = τ₀.glob → holds σ (κ.exit .box φ)
  | _, .nil, _, σ, e => (holds_reclose φ hφ σ τ₀ e).1 h
  | _, .seq .nil κ, hκ, σ, e => holds_exit_closed hφ h κ hκ σ e
  | _, .pop _ _ κ, hκ, _, e =>
    Upd.afterT_intro (fun _ => trivial) fun _ σ' hL =>
      holds_exit_closed hφ h κ hκ σ'
        ((hL.2.1.trans (congrArg Subtype.val (Option.some.inj hL.1).symm)).trans e)
  | _, .drop _ κ, hκ, _, e =>
    Upd.afterT_intro (fun _ => trivial) fun _ σ' hL =>
      holds_exit_closed hφ h κ hκ σ'
        ((hL.2.1.trans (congrArg Subtype.val (Option.some.inj hL.1).symm)).trans e)

/-- **The invariant assumed is the goal**: `…, {havoc}, I ⟹ I`, the
assumption past a frame end that drops every local, the goal past the
program's scope ends, read as `I` at the empty scope. -/
theorem Proves.assumeInv {R : RuleSet} {Γ₀ Γ Δ : Ctx} {H : Hyps C Γ₀ Γ} {I : Fml C []}
    {κ : Frames C Γ Δ} {φ : Fml C Δ} (hκ : κ.popsOnly = true := by rfl)
    (he : φ.reclose? = some I := by rfl) (hb : H.boxOnly = true := by rfl)
    (hm : ((H.pre (Fml.closedAt I)).wrap (κ.exit .box φ)).modalFree = true := by
      first | rfl | decide) :
    Proves C R Γ₀ (H.pre (Fml.closedAt I)) (κ.exit .box φ) := by
  refine .closeHolds (fun σ => H.wrap_valid (φ := .imp (Fml.closedAt I) (κ.exit .box φ)) hb
    (fun τ hτ => ?_) σ) hm
  exact holds_exit_closed he
    (Upd.afterT.of_lands hτ (Upd.lands_drop_nil (Thin.nilTo Γ) τ)) κ hκ τ rfl

/-- An assumption gives it opened. -/
theorem holds_openInv {Γ : Ctx} (a : Fml C Γ) (τ : State C Γ) (h : holds τ a) :
    holds τ a.openInv := by
  unfold Fml.openInv
  split
  · rename_i Δ e φ
    split
    · rename_i φ' hφ
      exact (holds_reclose φ hφ (τ.thin e) τ rfl).2
        (Upd.afterT.of_lands h (Upd.lands_drop_nil e τ))
    · exact h
  · exact h

/-- The context with its assumed invariants opened gives the context. -/
theorem Hyps.wrap_openInv {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) :
    ∀ {φ ψ : Fml C Γ}, (∀ τ, holds τ φ → holds τ ψ) →
      ∀ σ, holds σ (H.openInv.wrap φ) → holds σ (H.wrap ψ) := by
  induction H with
  | nil => intro φ ψ h σ; exact h σ
  | pre H a ih =>
    intro φ ψ h
    exact ih (φ := .imp a.openInv φ) (ψ := .imp a ψ) fun τ f ha => h τ (f (holds_openInv a τ ha))
  | upd H m U ih =>
    intro φ ψ h
    exact ih (φ := .upd m U φ) (ψ := .upd m U ψ) fun τ f =>
      Upd.afterT_imp f fun σ' x => h σ' x
  | havoc H ih =>
    intro φ ψ h
    exact ih (φ := .havoc φ) (ψ := .havoc ψ) fun τ f st nt => h _ (f st nt)
  | all H x p ih =>
    intro φ ψ h
    exact ih (φ := .all x p φ) (ψ := .all x p ψ) fun τ f v => h _ (f v)
  | bind H m x t ih =>
    intro φ ψ h
    exact ih (φ := .bind m x t φ) (ψ := .bind m x t ψ) fun τ f =>
      Modality.forallB_imp (fun _ a => h _ a) f
  | anon H xs ih =>
    intro φ ψ h
    exact ih (φ := .anon xs φ) (ψ := .anon xs ψ) fun τ f b => h _ (f b)

/-- **The invariant assumed, opened**: at a leaf, each assumed invariant read
at its scope, a closed first-order formula the closer reads. -/
theorem Proves.openInv {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (h : Proves C R Γ₀ H.openInv φ)
    (hm : (H.wrap φ).modalFree = true := by first | rfl | decide) : Proves C R Γ₀ H φ :=
  .closeHolds (fun σ => H.wrap_openInv (fun _ h => h) σ (Proves.sound h σ)) hm

/-- info: 'Solidity.ProvesC.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProvesC.valid

end Solidity
