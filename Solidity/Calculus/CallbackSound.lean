import Solidity.Calculus.Callback
import Solidity.Calculus.CallbackHolds
import Solidity.Calculus.CorrectCallback
import Solidity.Calculus.Sound
import Solidity.Calculus.UpdateRules
import Solidity.Semantics.NativeDeferredCallback
import Solidity.Semantics.CallbackFrame

/-!
# The calculus with callbacks is sound

`ProvesC I pay H φ` (`Calculus/Callback.lean`) proves `φ` with callbacks:
what it derives holds, its context in front, when every `try` and value call,
and with `pay` every payment, may call back into the contract and the callee
leaves the invariant as it found it
(`holdsC`, `ValidC`, `Calculus/CallbackHolds.lean`).  `ProvesC.sound_of`
and `ProvesC.fmlValid` take the invariant first-order (`Fml.FO`, a contract
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

/-- **A capture, with callbacks**: whatever the rest calls, the statement
runs as the captured program (`Stmt.CapturesAs`), its fresh locals popped. -/
theorem holdsC_capture {Γ'' : Ctx} {s : Stmt C Γ Γ'} {P : Prog C Γ Γ''} {e : Ext Γ' Γ''}
    (hc : s.CapturesAs pay m P e)
    (h : holdsC I pay σ (.modal m P (.pop .capture e (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  rcases hc _ rfl σ o₁ he with ⟨err, rfl, hm, hp⟩ | ⟨o', ho', rfl⟩
  · exact ⟨hm, hp⟩
  · exact COut.thenF_drop _ (h _ ho')

/-- `loopExit`'s "unwound to the end", `{ b := cond } (b = FALSE)`: the
condition evaluates to `false`. -/
theorem loopExit_cond {Γ : Ctx} (x : Var) {c : Val C Γ .bool} {σ : State C Γ}
    (h : holds σ (.upd .diamond (Upd.nil.decl x (.val (p := .bool) c.lower))
      (Fml.isBool (Tm.pvV (p := .bool) .here) false))) : c.evalT σ = .ok false := by
  have hglob : (Upd.nil.decl x (.val (p := .bool) c.lower)).globT σ =
      (c.lower.eval σ).bind fun _ => some σ.globG := rfl
  cases hc : c.evalT σ with
  | error e =>
    rw [Val.lower_eval_error c σ hc] at hglob
    exact (h.of_noExh hglob (Upd.exh_of_pushFree (by
      simp only [Upd.pushFree, Rhs.pushFree, Val.lower_pushFree, Bool.and_self]))).elim
  | ok v =>
    have hcl : (Rhs.val (p := .bool) c.lower).eval σ =
        some (LTy.VDen.ofT (H := σ.H) (.val .bool) v) := by
      show c.lower.eval σ = _
      exact Val.lower_eval_ok c σ hc
    have hv : v = false :=
      (holds_isBool_pvV _ _ _).1 (h.of_lands (Upd.lands_decl (Upd.lands_nil σ) x hcl))
    rw [hv]

/-- **`loopExit` with callbacks**, under the box: a loop whose condition is
`false` ends where it is, or, its body calling back, diverges. -/
theorem holdsC_loopExit {Γb : Ctx} {c : Val C Γ' .bool} {body : Prog C Γ' Γb} {σ : State C Γ'}
    (hc : c.evalT σ = .ok false) (h : holdsC I pay σ (Fml.modalK .box ω κ φ)) :
    holdsC I pay σ (.modal .box (.cons (.loop (.unwind 0) c body) ω) κ φ) := by
  cases hb : body.callsBack pay with
  | false =>
    refine holdsC_cons_det hb (fun τ hτ => ?_) (fun e he => ?_)
    · rw [Stmt.runSt_loop_unfold, hc] at hτ
      cases hτ
      exact h
    · rw [Stmt.runSt_loop_unfold, hc] at he
      cases he
  | true =>
    refine holdsC_cons fun o₁ he => ?_
    have hl : CallbackUnwk.LoopExec (I.stateInv pay) (.unwind 0) c body σ o₁ :=
      CallbackUnwk.asLoop he
    cases hl with
    | det hf => exact absurd (hb.symm.trans hf) (by decide)
    | halt _ hc' => rw [hc] at hc'; cases hc'
    | exit _ _ => exact COut.after_seq (holdsC_modalK σ ω κ φ h)
    | iter _ hc' => rw [hc] at hc'; cases hc'
    | stop _ hc' => rw [hc] at hc'; cases hc'
    | diverge _ => exact ⟨trivial, nofun⟩

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

/-- Simple payment operands only halt when the payment is refused. -/
private theorem transfer_halt (sadr se : Simple C Γ .uint) {e : THalt}
    (h : TRun.transfer (.simple sadr) (.simple se) σ = .error e) : e = .revert := by
  change (if σ.canPay (sadr.evalT σ) (se.evalT σ) then _ else _) = _ at h
  split at h <;> cases h
  rfl

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
    change COut.thenF _ _ _ _ (COut.ofRes (TRun.transfer _ _ σ))
    cases h : TRun.transfer (.simple sadr) (.simple se) σ with
    | error e =>
      have he := transfer_halt sadr se h
      cases he
      exact ⟨trivial, by decide⟩
    | ok o₂ =>
      have hL := (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec
      have hJ := (holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx hL)
      exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hr hL o₂.st.storage
        o₂.st.net o₂.st.selfBalance ((holdsC_closedAt_iff hI hT _).2 hJ)))
  | transferHalt _ h =>
    have he := transfer_halt sadr se h
    cases he
    exact ⟨trivial, by decide⟩
  | transferViolated _ h hn =>
    exact (hn ((holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx
      (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec))).elim
  | transferResume _hp h hJ hJ' =>
    rename_i st nt sb o₂
    exact COut.after_seq (holdsC_modalK _ ω κ φ
      (Upd.afterT.of_lands hr (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec st nt sb
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
    rcases TRun.send_cases pv (.simple sadr) (.simple se) σ with ⟨e, hs⟩ | ⟨o₂, ht, hs⟩ | hs
    · exact nomatch hs
    · rw [hs]
      have hL := (Upd.lands_of_applyP (transfer_booking sadr se ht)).choose_spec
      have hJ := (holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx hL)
      exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hok
        (Upd.lands_snoc_local hL pv (v := (true : Bool)) rfl) o₂.st.storage o₂.st.net o₂.st.selfBalance
        ((holdsC_closedAt_iff hI hT _).2 hJ)))
    · rw [hs]
      exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hf
        (Upd.lands_snoc_local (Upd.lands_nil σ) pv (v := (false : Bool)) rfl)))
  | sendHalt _ h => nomatch h
  | sendFailed _ h | sendRefused _ h =>
    exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hf
      (Upd.lands_snoc_local (Upd.lands_nil σ) pv (v := (false : Bool)) rfl)))
  | sendViolated _ h hn =>
    exact (hn ((holdsC_closedAt_iff hI hT _).1 (Upd.afterT.of_lands hx
      (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec))).elim
  | sendResume _hp h hJ hJ' =>
    rename_i st nt sb o₂
    exact COut.after_seq (holdsC_modalK _ ω κ φ (Upd.afterT.of_lands hok
      (Upd.lands_snoc_local (Upd.lands_of_applyP (transfer_booking sadr se h)).choose_spec pv
        (v := (true : Bool)) rfl) st nt sb ((holdsC_closedAt_iff hI hT _).2 hJ')))

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
    rename_i st nt sb _ _ r o
    have h₁ := hok st nt sb ((holdsC_closedAt_iff hI hT _).2 hJ')
    have h₂ := holdsC_binders_all rets (σ.havoc st nt sb) _ r h₁
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
    {φ : Fml C Γ₀} {e : THalt} (he : e ≠ .exhausted)
    (h : ExecP (I.stateInv pay) σ P (.halt e)) : ¬ holdsC I pay σ (.modal .diamond P κ φ) := by
  intro hX
  exact he (hX _ h).1

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
  exact holdsC_not_diamond (e := .revert) nofun (ExecP.halt hd)

/-- The contract's own callee, which reverts or panics. -/
theorem holdsC_selfFails_halt {ρ ps Γf : Ctx} (call : ExtCall C Γ) (rets : Binders ρ)
    (sargs : Args C Γ ps) (sbody : Prog C (ρ ++ ps) Γf) (σ : State C Γ)
    (hs : (call.addr.evalT σ).1 = σ.tx.selfAddress.1) {e : THalt} (he : e ≠ .exhausted)
    (hc : ExecS (I.stateInv pay) σ (.call call.fn sargs (.rets rets) sbody) (.halt e)) :
    holdsC I pay σ (call.selfFails rets sargs sbody) := by
  have hi : call.isSelf.evalT σ = .ok true := by
    rw [ExtCall.isSelf_evalT]; simp only [hs, decide_true]
  exact holdsC_not_diamond he (ExecP.require_true hi (ExecP.halt (P := .nil) hc))

/-- **A self-call's callee panics with a code it lists, with callbacks**
(`Prog.panicCodes`): a callee whose codes are known calls nobody back, so
its callback run is its run (`ExecS.eq_run`, `Prog.panicCodes_call`). -/
theorem Prog.panicCodes_exec {J : StateInv C} {ρ ps Γf : Ctx} {sbody : Prog C (ρ ++ ps) Γf}
    {ks : List Semantics.Word} (hK : sbody.panicCodes = some ks) {f : Name}
    (sargs : Args C Γ ps) (rets : Binders ρ) (σ : State C Γ) {e : THalt}
    (hc : ExecS J σ (.call f sargs (.rets rets) sbody) (.halt e)) :
    e ≠ .panic ∧ ∀ d v, e = .revertWith d → Semantics.decodePanic d = some v → v ∈ ks := by
  have ht : Stmt.callsBack J.pay (.call f sargs (.rets rets) sbody) = false :=
    Prog.callsBack_of_hasTransfer sbody (Prog.panicCodes_hasTransfer hK)
  have he := ExecS.eq_run hc ht
  have hr : TRun.call sargs (.rets rets) sbody.ext sbody.runR σ = .error e := by
    change COut.halt e = COut.ofRes (TRun.call sargs (.rets rets) sbody.ext sbody.runR σ) at he
    revert he
    cases TRun.call sargs (.rets rets) sbody.ext sbody.runR σ with
    | ok _ => intro he; cases he
    | error e' => intro he; cases he; rfl
  exact Prog.panicCodes_call hK sargs rets σ hr

/-- **The guarded `Panic` clause with callbacks** (`CodeBinder.guard`):
where the receiver is another contract, or `c` is one of the codes the
callee may panic with, the guard passes, and the clause's goal is its
block's. -/
theorem holdsC_tryPanicG {κc Γ₃ Γ₂ Γ₀ : Ctx} (call : ExtCall C Γ) (code : CodeBinder κc)
    (K : Option (List Semantics.Word)) (pnc : Prog C (κc ++ Γ) Γ₃) (σ : State C Γ)
    (c : Semantics.Word) (ω : Prog C Γ Γ₂) (κ : Frames C Γ₂ Γ₀) (φ : Fml C Γ₀)
    (hc : ∀ ks, K = some ks → (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1 ∨ c ∈ ks)
    (h : holdsC I pay σ (code.binders.all (Fml.modalK .box (code.guard call K pnc)
      (.pop .block ((Ext.append Γ κc).trans (code.guard call K pnc).ext) (.seq ω κ)) φ))) :
    holdsC I pay (σ.withEnv (TEnv.append κc (code.decodeT (H := σ.H) c) σ.env))
      (.modal .box pnc (.pop .block ((Ext.append Γ κc).trans pnc.ext) (.seq ω κ)) φ) := by
  have h₂ := holdsC_binders_all code.binders σ _ (code.decodeT (H := σ.H) c) h
  cases K with
  | none => cases code <;> exact holdsC_modalK _ _ _ φ h₂
  | some ks =>
    cases code with
    | none =>
      cases ks with
      | nil =>
        have hn : call.notSelf.evalT
            (σ.withEnv (TEnv.append [] (CodeBinder.none.decodeT (H := σ.H) c) σ.env)) =
            .ok true := by
          show Except.ok (!decide ((call.addr.evalT σ).1 = σ.tx.selfAddress.1)) = _
          rcases hc [] rfl with hs | hs
          · rw [decide_eq_false hs]; rfl
          · exact absurd hs List.not_mem_nil
        have h₃ := holdsC_modalK _ _ _ φ h₂
        dsimp only [CodeBinder.guard] at h₃
        rw [show (Ext.append Γ []).trans (Prog.cons (.require call.notSelf) pnc).ext =
          (Ext.append Γ []).trans pnc.ext from Subsingleton.elim _ _] at h₃
        intro o hP
        have h₄ := h₃ _ (ExecP.require_true hn hP)
        rwa [COut.thenF_map_cat] at h₄
      | cons _ _ => exact holdsC_modalK _ _ _ φ h₂
    | some x =>
      have ha := ExtCall.addr_wk_append call σ (ρ := [.val .uint])
        ((CodeBinder.some x).decodeT (H := σ.H) c)
      have hg : (Val.binop .or rfl rfl (call.wk (Thin.ofExt (Ext.append Γ [.val .uint]))).notSelf
          (codeGuard ks)).evalT (σ.withEnv (TEnv.append [.val .uint]
            ((CodeBinder.some x).decodeT (H := σ.H) c) σ.env)) = .ok true := by
        refine Val.or_evalT_true _ _ _ (by rw [ExtCall.notSelf_evalT]) ?_
        rcases hc ks rfl with hs | hs
        · refine .inl ?_
          rw [ha]
          show (!decide ((call.addr.evalT σ).1 = σ.tx.selfAddress.1)) = true
          rw [decide_eq_false hs]
          rfl
        · exact .inr (codeGuard_evalT _ ks hs)
      have h₃ := holdsC_modalK _ _ _ φ h₂
      dsimp only [CodeBinder.guard] at h₃
      rw [show (Ext.append Γ [.val .uint]).trans (Prog.cons (.require _) pnc).ext =
        (Ext.append Γ [.val .uint]).trans pnc.ext from Subsingleton.elim _ _] at h₃
      intro o hP
      have h₄ := h₃ _ (ExecP.require_true hg hP)
      rwa [COut.thenF_map_cat] at h₄

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
    (hok : holdsC I pay σ (.imp (Fml.isBool call.notSelf.lower true)
      (.havoc (.imp (Fml.closedAt I) (rets.all (Fml.modalK .box ok
      (.pop .block ((Ext.append Γ ρ).trans ok.ext) (.seq ω κ)) φ))))))
    (herr : holdsC I pay σ (.imp (call.selfFails rets sargs sbody) (Binders.nil.all
      (Fml.modalK .box err (.pop .block ((Ext.append Γ []).trans err.ext) (.seq ω κ)) φ))))
    (hpnc : holdsC I pay σ (.imp (call.selfFails rets sargs sbody) (code.binders.all
      (Fml.modalK .box (code.guard call sbody.panicCodes pnc) (.pop .block
        ((Ext.append Γ κc).trans (code.guard call sbody.panicCodes pnc).ext) (.seq ω κ)) φ))))
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
    rename_i st nt sb _ _ r o
    obtain ⟨hz, hs⟩ := hg rfl
    have hn : call.notSelf.evalT σ = .ok true := by
      rw [ExtCall.notSelf_evalT]
      simp only [hs, decide_false, Bool.not_false]
    have hguard : holdsC I pay σ (Fml.isBool call.notSelf.lower true) :=
      (holdsC_iff_holds _ rfl σ).mpr (holds_isBool_lower call.notSelf σ hn)
    have h₁ := hok hguard st nt sb ((holdsC_closedAt_iff hI hT _).2 hJ')
    have h₂ := holdsC_modalK _ _ _ φ (holdsC_binders_all rets (σ.havoc st nt sb) _ r h₁)
    exact COut.thenF_drop _ (h₂ o hP)

  | tryError hsf hP =>
    have herr := herr (holdsC_selfFails_notSelf call rets sargs sbody σ (hsf rfl))
    rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at herr
    exact COut.thenF_drop _ (holdsC_modalK σ err _ φ herr _ hP)
  | tryPanic hsf hP =>
    rename_i v o
    have h₂ := holdsC_tryPanicG call code _ pnc σ v ω κ φ (fun _ _ => .inl (hsf rfl))
      (hpnc (holdsC_selfFails_notSelf call rets sargs sbody σ (hsf rfl)))
    exact COut.thenF_drop _ (h₂ o hP)
  | tryOther hsf hP =>
    have hoth := hoth (holdsC_selfFails_notSelf call rets sargs sbody σ (hsf rfl))
    rw [show (Ext.append Γ []).trans other.ext = other.ext from Subsingleton.elim _ _] at hoth
    exact COut.thenF_drop _ (holdsC_modalK σ other _ φ hoth _ hP)
  | trySelfError _ hs hc hP =>
    have herr := herr (holdsC_selfFails_halt call rets sargs sbody σ hs (e := .revertWith _) nofun hc)
    rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at herr
    exact COut.thenF_drop _ (holdsC_modalK σ err _ φ herr _ hP)
  | trySelfPanic _hz hs hc he hP =>
    rename_i v e₀ o
    have hK : ∀ ks, sbody.panicCodes = some ks →
        (call.addr.evalT σ).1 ≠ σ.tx.selfAddress.1 ∨ v ∈ ks := by
      intro ks hks
      obtain ⟨hp, hd⟩ := Prog.panicCodes_exec hks sargs rets σ hc
      rcases he with rfl | ⟨d, rfl, hv⟩
      · exact absurd rfl hp
      · exact .inr (hd d v rfl hv)
    have h₂ := holdsC_tryPanicG call code _ pnc σ v ω κ φ hK
      (hpnc (holdsC_selfFails_halt call rets sargs sbody σ hs
        (by rcases he with rfl | ⟨_, rfl, _⟩ <;> nofun) hc))
    exact COut.thenF_drop _ (h₂ o hP)
  | trySelfOther _ hs hc he hP =>
    have hoth := hoth (holdsC_selfFails_halt call rets sargs sbody σ hs
      (by rcases he with rfl | ⟨_, rfl⟩ <;> nofun) hc)
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
  rcases TRun.send_cases pv (.simple sadr) (.simple se) σ with ⟨e, hs⟩ | ⟨o₂, ht, hs⟩ | hs
  · exact nomatch hs
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
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop ps Γ) (σ.withEnv a)
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
      o = o'.map (TRun.callLeave ret body.ext σ (ret.enterT (σ.withEnv a))) :=
  ExecS.call_cases he

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

/-- **A call of one value, with callbacks, is its inlined body**
(`Premise.sound_callVal`'s program): the parameters declared, the return
variable at its default, the body lifted under them as a block, the result
assigned to its target, the frame popped. -/
theorem ExecS.callVal_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name} {args : Args C Γ ps}
    {p : PrimTy} {r : Var} {res : Option (Idx Γ (.val p))} {body : Prog C ([.val p] ++ ps) Γf}
    {o : COut C σ.H Γ} (he : ExecS J σ (.call f args (.val p r res) body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (Prog.callResult res)))) u ∧
      o = u.map (Out.drop (.push (Ext.append Γ ps))) := by
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · have hp' : ExecP J (σ.withEnv (Δ := .val p :: ps) (PrimTy.dflt p, a)) body o' := hp
    obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop (.val p :: ps) Γ)
      (σ.withEnv (Δ := .val p :: ps) (PrimTy.dflt p, a))
      (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env) hp'
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv (Δ := .val p :: ps) (PrimTy.dflt p, a)).lift
        (Thin.atop (.val p :: ps) Γ)
        (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env))
      (Y := σ.withEnv (TEnv.append (.val p :: ps) (PrimTy.dflt p, a)
        σ.env)) rfl rfl
      (State.withEnv_append_lift (ps := .val p :: ps) σ (PrimTy.dflt p, a)).symm
      (block_of_execP hw)
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps a σ.env))
      (s := .declLocal p r none) rfl (Stmt.runSt_declLocal_none p r _)
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop (.val p :: ps) Γ)) hr).eq_lifted
    rw [hl] at hb
    cases o' with
    | halt e =>
      exact ⟨.halt e, Args.execP_declsThen args _ σ a ha
        (by simpa only [map_cat_refl] using ExecP.cons hd (ExecP.halt hb)), rfl⟩
    | violated =>
      exact ⟨.violated, Args.execP_declsThen args _ σ a ha
        (by simpa only [map_cat_refl] using ExecP.cons hd (ExecP.violated hb)), rfl⟩
    | ok x =>
      let y := (Out.drop body.ext x).lift (Thin.atop (.val p :: ps) Γ)
        (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env)
      have hb' : ExecS J (σ.withEnv (TEnv.append (.val p :: ps) (PrimTy.dflt p, a) σ.env))
          (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (.ok y) := hb
      have ht := ExecP.of_run (J := J) (τ := y.st)
        (P := (Prog.callResult res : Prog C (.val p :: (ps ++ Γ)) _)) (by cases res <;> rfl)
      refine ⟨_, Args.execP_declsThen args _ σ a ha
        (by simpa only [map_cat_refl] using ExecP.cons hd (ExecP.cons hb' ht)), ?_⟩
      cases res with
      | none =>
        refine congrArg COut.ok (Out.eq_of_st ?_)
        simp only [Out.drop, Out.lift, Out.cat, TRun.callLeave, State.lift, State.drop,
          State.withEnv, CallRet.leaveT, y]
        erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)]
      | some j =>
        refine congrArg COut.ok (Out.eq_of_st ?_)
        rw [show (Ext.append Γ ps).push = Ext.append Γ (LTy.val p :: ps) from rfl]
        simp only [Out.drop, Out.lift, Out.cat, TRun.callLeave, State.lift, State.drop,
          State.withEnv, State.setLocal, show (j.under ps).there = j.under (LTy.val p :: ps) from rfl,
          TEnv.drop_set_under, CallRet.leaveT, y]
        erw [TEnv.drop_put_atop_wk (Γ := Γ) _ (LTy.val p :: ps)]
        rfl

/-- **A call of a storage reference, with callbacks, is its inlined body**
(`Premise.sound_callStorage`'s program): the parameters declared, the
return alias unset, the body lifted under them as a block, the parameters
thinned out from under the alias. -/
theorem ExecS.callStorage_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {body : Prog C ([.alias R] ++ ps) Γf}
    {o : COut C σ.H (.alias R :: Γ)} (he : ExecS J σ (.call f args (.storage R r) body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.declStorage R r none)
        (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil))) u ∧
      o = u.map fun x => ⟨x.st.thin (.keep (Thin.ofExt (Ext.append Γ ps))), x.ext⟩ := by
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · have hp' : ExecP J (σ.withEnv (Δ := .alias R :: ps) (none, a)) body o' := hp
    obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop (.alias R :: ps) Γ)
      (σ.withEnv (Δ := .alias R :: ps) (none, a))
      (TEnv.append (.alias R :: ps) (none, a) σ.env) hp'
    have hb := ExecS.transport (H := σ.H)
      (X := (σ.withEnv (Δ := .alias R :: ps) (none, a)).lift
        (Thin.atop (.alias R :: ps) Γ) (TEnv.append (.alias R :: ps) (none, a) σ.env))
      (Y := σ.withEnv (TEnv.append (.alias R :: ps) (none, a) σ.env)) rfl rfl
      (State.withEnv_append_lift (ps := .alias R :: ps) σ (none, a)).symm
      (block_of_execP hw)
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ.withEnv (TEnv.append ps a σ.env))
      (s := .declStorage R r none) rfl (Stmt.runSt_declStorage_none R r _)
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop (.alias R :: ps) Γ)) hr).eq_lifted
    rw [hl] at hb
    refine ⟨_, Args.execP_declsThen args _ σ a ha
      (by simpa only [map_cat_refl] using ExecP.cons hd (singleton_iff.mpr hb)), ?_⟩
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, TRun.callLeave, State.lift, State.drop, State.thin,
        State.withEnv, CallRet.leaveT]
      erw [TEnv.thin_put_keepAllAtop (rs := [.alias R]) (r := (none, ()))]
      rfl
    | halt => rfl
    | violated => rfl

/-- **A call of a memory reference, with callbacks, is its inlined body**
(`Premise.sound_callMem`'s program): the parameters declared, the return
object allocated at its default, the body lifted under them as a block,
the parameters thinned out from under the object. -/
theorem ExecS.callMem_inline {Γ ps Γf : Ctx} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {hd : (Ty.ref R).defaultOkS = true}
    {hm : (Ty.ref R).mapFree = true} {body : Prog C ([.mem R] ++ ps) Γf}
    {o : COut C σ.H (.mem R :: Γ)} (he : ExecS J σ (.call f args (.mem R r hd hm) body) o) :
    ∃ u, ExecP J σ (args.declsThen (.cons (.declMem R r none hd hm)
        (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil))) u ∧
      o = u.map fun x => ⟨x.st.thin (.keep (Thin.ofExt (Ext.append Γ ps))), x.ext⟩ := by
  rcases ExecS.call_cases he with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact ⟨.halt _, Args.execP_declsThen_halt args _ σ ha, rfl⟩
  · let g := (σ.withEnv a).allocDefaultG R hm
    let τ := σ.withEnv (TEnv.append ps a σ.env)
    have hp' : ExecP J (g.st.push (t := .mem R) (some g.val)) body o' := hp
    obtain ⟨o'', hw, hr⟩ := Prog.exec_wk J body (Thin.atop (.mem R :: ps) Γ)
      (g.st.push (t := .mem R) (some g.val))
      (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env)) hp'
    have hY : (g.st.push (t := .mem R) (some g.val)).lift (Thin.atop (.mem R :: ps) Γ)
          (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env)) =
        (τ.allocDefaultG R hm).st.push (t := .mem R) (some (τ.allocDefaultG R hm).val) := by
      show _ = ((σ.withEnv (TEnv.append ps a σ.env)).allocDefaultG R hm).st.push (t := .mem R)
        (some ((σ.withEnv (TEnv.append ps a σ.env)).allocDefaultG R hm).val)
      rw [State.withEnv_append_lift σ a, State.allocDefaultG_lift]
      simp only [g, Grew.lift, State.lift, State.push, Thin.atop, State.withEnv, TEnv.put]
      rfl
    have hb := ExecS.transport (H := g.st.H)
      (X := (g.st.push (t := .mem R) (some g.val)).lift (Thin.atop (.mem R :: ps) Γ)
          (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env)))
      (Y := (τ.allocDefaultG R hm).st.push (t := .mem R) (some (τ.allocDefaultG R hm).val))
      rfl rfl hY (block_of_execP hw)
    obtain ⟨_, hd'⟩ := ExecS.det_ok (J := J) (σ := τ)
      (s := .declMem R r none hd hm) rfl (Stmt.runSt_declMem_none R r hd hm _)
    have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (Thin.atop (.mem R :: ps) Γ)) hr).eq_lifted
    rw [hl] at hb
    refine ⟨_, Args.execP_declsThen args _ σ a ha (ExecP.cons hd' (singleton_iff.mpr hb)), ?_⟩
    cases o' with
    | ok x =>
      refine congrArg COut.ok (Out.eq_of_st ?_)
      simp only [Out.drop, Out.lift, Out.cat, TRun.callLeave, State.lift, State.drop, State.thin,
        State.withEnv, CallRet.leaveT]
      erw [TEnv.thin_keep_put_atop]
      rfl
    | halt => rfl
    | violated => rfl

/-- **A call of one value, with callbacks**: its inlined body, the result
assigned, the frame popped. -/
theorem holdsC_callVal {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {p : PrimTy} {r : Var} {res : Option (Idx Γ (.val p))}
    {body : Prog C ([.val p] ++ ps) Γf} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (.cons (.declLocal p r none)
        (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (Prog.callResult res))))
      (.pop .capture (.push (Ext.append Γ ps)) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.val p r res) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callVal_inline he
  exact COut.thenF_drop _ (h _ hu)

/-- **A call of a storage reference, with callbacks**: its inlined body, the
parameters thinned out from under the alias. -/
theorem holdsC_callStorage {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {body : Prog C ([.alias R] ++ ps) Γf}
    {ω : Prog C (.alias R :: Γ) Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (.cons (.declStorage R r none)
        (.cons (.block (body.wk (Thin.atop (.alias R :: ps) Γ)).2.2) .nil)))
      (.drop (.keep (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.storage R r) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callStorage_inline he
  exact COut.thenF_thin _ (h _ hu)

/-- **A call of a memory reference, with callbacks**: its inlined body, the
parameters thinned out from under the object. -/
theorem holdsC_callMem {Γ ps Γf Γ₁ Γ₀ : Ctx} {m : Modality} {σ : State C Γ} {f : Name}
    {args : Args C Γ ps} {R : RefTy} {r : Var} {hd : (Ty.ref R).defaultOkS = true}
    {hm : (Ty.ref R).mapFree = true} {body : Prog C ([.mem R] ++ ps) Γf}
    {ω : Prog C (.mem R :: Γ) Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀}
    (h : holdsC I pay σ (.modal m (args.declsThen (.cons (.declMem R r none hd hm)
        (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil)))
      (.drop (.keep (Thin.ofExt (Ext.append Γ ps))) (.seq ω κ)) φ)) :
    holdsC I pay σ (.modal m (.cons (.call f args (.mem R r hd hm) body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  obtain ⟨u, hu, rfl⟩ := ExecS.callMem_inline he
  exact COut.thenF_thin _ (h _ hu)

end Calls

/-! ## A loop by its invariant, with callbacks

`whileInvariantBox` read over the callback runs (`ProvesC.invBox`): every
loop head is a state the body's frame allows from the first
(`ExecP.frame`: a callback replaces only the storage and the ledger, which a
body that calls back may write, `Prog.frame`'s `hv`), so the premise read
under `{anon(xs)}` (`{havoc}`) holds there (`holdsC_anonHavoc`); the
invariant holds at every head by induction over the iterations
(`ExecS.loop_box`: the typed run's where the body calls nobody back,
`CallbackUnwk.LoopExec`'s otherwise).  Under the box only: a loop whose body
calls back may diverge (`ExecS.loopDiverge`), which no diamond accepts
(`holdsC_diamond_loop`). -/

section Inv

variable {I : Fml C []} {J : StateInv C}

/-- **A state in a loop body's frame is one its anonymised premise covers**,
with callbacks (`holds_anonHavoc`). -/
theorem holdsC_anonHavoc {Γ : Ctx} {σ τ : State C Γ} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Bool} {W : List (LTy × Nat)}
    (hxs : ∀ t (i : Idx Γ t), (t, i.toNat) ∈ W → (⟨t, i⟩ : (t : LTy) × Idx Γ t) ∈ xs)
    (hg : TGFrame (frameMut hv) σ τ) (ha : TLocAgree 0 W σ.env τ.env) {ψ : Fml C Γ}
    (h : holdsC I pay σ (Fml.anonHavoc xs hv ψ)) : holdsC I pay τ ψ := by
  obtain ⟨b, hb⟩ := State.eq_anonHavoc hxs hg ha
  cases hv with
  | false =>
    have hk := hg.keeps (by simp only [frameMut]; decide)
    have hτ : τ = σ.anon xs b := by rw [hb, hk.1, hk.2, hg.selfBalance (by simp only [frameMut]; decide)]; rfl
    rw [hτ]
    exact h b
  | true =>
    rw [hb]
    exact h b τ.storage τ.net τ.selfBalance

/-- **Induction over a loop's callback runs**, under the box: `P` holds at
the first head and at every head an iteration from a head in `P` goes on
in, where the condition is `true`; where it is `false`, `Q` holds. -/
theorem ExecS.loop_box {Γ Γb : Ctx} {a : LoopAnn C Γ} {c : Val C Γ .bool} {body : Prog C Γ Γb}
    {σ : State C Γ} (P Q : State C Γ → Prop) (h0 : P σ)
    (hexit : ∀ τ, P τ → c.evalT τ = .ok false → Q τ)
    (hstep : ∀ τ, P τ → c.evalT τ = .ok true → ∀ o, ExecP J τ body o →
      (o.map (Out.drop body.ext)).after .box P) :
    ∀ o, ExecS J σ (.loop a c body) o → o.after .box Q := by
  intro o he
  cases hb : body.callsBack J.pay with
  | false =>
    rw [ExecS.eq_run_of_forksIn he hb]
    show (COut.ofRes (TLoop.run (fun o : Out C σ.H Γ => (Prog.run o.st body).map
      fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
      (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩)).after .box Q
    refine TLoop.run_induct (P := fun x : Out C σ.H Γ => P x.st)
      (Q := fun r => (COut.ofRes r).after .box Q) h0 (fun x hx => ?_) ⟨trivial, nofun⟩
    unfold TLoop.step
    dsimp only
    cases hc : c.evalT x.st with
    | error e =>
      refine ⟨trivial, fun h => ?_⟩
      cases h
      exact Val.evalT_noPanic x.st c hc
    | ok v =>
      cases v with
      | false => exact hexit _ hx hc
      | true =>
        have hs := hstep _ hx hc _ (ExecP.of_run (J := J) (τ := x.st) (P := body) hb)
        dsimp only
        cases hr : Prog.run x.st body with
        | error e => rw [hr] at hs; exact hs
        | ok y => rw [hr] at hs; exact hs
  | true =>
    have hl : CallbackUnwk.LoopExec J a c body σ o := CallbackUnwk.asLoop he
    clear he
    induction hl with
    | det hf => exact absurd (hb.symm.trans hf) (by decide)
    | halt _ hc =>
      refine ⟨trivial, fun h => ?_⟩
      cases h
      exact Val.evalT_noPanic _ c hc
    | exit _ hc => exact hexit _ h0 hc
    | @iter τ υ o' _ hc hp _ ih =>
      have h1 : P (υ.st.drop body.ext) := hstep _ h0 hc _ hp
      exact (COut.after_map_cat _ _ Q).2 (ih h1)
    | @stop τ o' _ hc hp hn =>
      have h1 := hstep _ h0 hc _ hp
      cases o' with
      | ok => cases hn
      | halt e => exact h1
      | violated => exact h1.elim
    | diverge _ => exact ⟨trivial, nofun⟩

/-- A run through no frame: its outcome read after it. -/
theorem COut.thenF_nil {H : HTy} {Γ : Ctx} {m : Modality} {p : State C Γ → Prop}
    (o : COut C H Γ) (h : o.thenF J .nil m p) : o.after m p := by
  cases o with
  | ok o => exact h _ .nil
  | halt _ => exact h
  | violated => exact h

/-- **`whileInvariantBox` with callbacks**: the invariant now ("invariant
initially valid"); from every state the body's frame allows where it holds,
the body to the invariant where the condition holds ("body preserves
invariant"), the rest where it does not ("use case"); with a break test, a
body that broke goes on to the rest. -/
theorem holdsC_invBox {Γ Γb Γ₁ Γ₀ : Ctx} {Iv : Val C Γ .bool} {dec : Option (Val C Γ .uint)}
    {brk : Bool} {qs : List (LoopQ C Γ)} {c : Val C Γ .bool} {body : Prog C Γ Γb}
    {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀} {xs : List ((t : LTy) × Idx Γ t)}
    {hv : Bool} {k : Nat} (hf : body.frame = some (xs, hv)) {σ : State C Γ}
    (hI : holdsC I pay σ ((invFml Iv qs).invHyp (loopBreak brk c)))
    (hX : holdsC I pay σ (Fml.anonHavoc xs hv (.imp ((invFml Iv qs).invHyp (loopBreak brk c))
      (.upd .box (Upd.nil.decl (fse k) (.val (p := .bool) c.lower))
        (.and (.imp (.isBool (.pvV (p := .bool) .here) true)
          (.upd .box (Upd.nil.pop (.push .refl)) (Fml.modalK .box body (.pop .block body.ext .nil)
            (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)))))
          (.imp (.isBool (.pvV (p := .bool) .here) false)
            (.upd .box (Upd.nil.pop (.push .refl)) (Fml.modalK .box ω κ φ)))))))) :
    holdsC I pay σ (.modal .box (.cons (.loop (.inv Iv dec brk qs) c body) ω) κ φ) := by
  obtain ⟨hwμ, hxs⟩ := Prog.frame_some hf
  have hB := breakTest_loopBreak brk c
  -- the premise at a head the frame allows, the condition read
  have hY : ∀ τ : State C Γ, TGFrame (frameMut hv) σ τ →
      TLocAgree 0 (Prog.writesAt 0 body) σ.env τ.env →
      holdsC I pay τ ((invFml Iv qs).invHyp (loopBreak brk c)) → ∀ v : Bool, c.evalT τ = .ok v →
      (v = true → holdsC I pay τ (Fml.modalK .box body (.pop .block body.ext .nil)
          (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)))) ∧
      (v = false → holdsC I pay τ (Fml.modalK .box ω κ φ)) := by
    intro τ hg hag hIτ v hc
    have hcl : (Rhs.val (p := .bool) c.lower).eval τ =
        some (LTy.VDen.ofT (H := τ.H) (.val .bool) v) := by
      show c.lower.eval τ = _
      exact Val.lower_eval_ok c τ hc
    obtain ⟨hT, hF⟩ := (holdsC_anonHavoc hxs hg hag hX hIτ).of_lands
      (Upd.lands_decl (Upd.lands_nil τ) (fse k) hcl)
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · subst hv
      exact Upd.afterT.of_lands (hT ((holds_isBool_pvV _ _ _).2 rfl)) (Upd.lands_pop_nil _ _)
    · subst hv
      exact Upd.afterT.of_lands (hF ((holds_isBool_pvV _ _ _).2 rfl)) (Upd.lands_pop_nil _ _)
  refine holdsC_cons fun o₁ he => ?_
  have hL := ExecS.loop_box (J := I.stateInv pay)
    (P := fun τ => (TGFrame (frameMut hv) σ τ ∧ TLocAgree 0 (Prog.writesAt 0 body) σ.env τ.env ∧
        holdsC I pay τ ((invFml Iv qs).invHyp (loopBreak brk c))) ∨
      (c.evalT τ = .ok false ∧ holdsC I pay τ (Fml.modalK .box ω κ φ)))
    (Q := fun τ => holdsC I pay τ (Fml.modalK .box ω κ φ)) (.inl ⟨TGFrame.refl σ, TLocAgree.refl _, hI⟩)
    (fun τ hτ hc => by
      rcases hτ with ⟨hg, hag, hIτ⟩ | ⟨_, hR⟩
      · exact (hY τ hg hag hIτ false hc).2 rfl
      · exact hR)
    (fun τ hτ hc o hp => by
      rcases hτ with ⟨hg, hag, hIτ⟩ | ⟨hc', _⟩
      · have hA := holdsC_modalK τ body _ _ ((hY τ hg hag hIτ true hc).1 rfl) o hp
        have hA' := COut.thenF_nil _ (COut.thenF_drop _ hA)
        cases o with
        | halt e => exact hA'
        | violated => exact hA'.elim
        | ok υ =>
          have hpost : holdsC I pay (υ.st.drop body.ext)
              (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)) := hA'
          obtain ⟨hg', ha'⟩ := ExecP.frame hp hwμ 0 υ rfl
          have hfr : TGFrame (frameMut hv) σ (υ.st.drop body.ext) := hg.trans (hg'.withEnv _)
          have hag' : TLocAgree 0 (Prog.writesAt 0 body) σ.env (υ.st.drop body.ext).env :=
            hag.trans ha'
          show _ ∨ _
          cases hBr : loopBreak brk c with
          | none =>
            rw [hBr] at hpost
            exact .inl ⟨hfr, hag', hpost⟩
          | some Bf =>
            rw [hBr] at hpost
            obtain ⟨x, rfl, hx⟩ := hB _ hBr
            by_cases hbk : holdsC I pay (υ.st.drop body.ext)
                (Fml.isBool (Tm.pvV (p := .bool) x) true)
            · refine .inr ⟨hx _ (by rw [← (holds_isBool_pvV x _ true).1 hbk]; rfl), ?_⟩
              exact Upd.afterT.of_lands
                (hpost.2 (Upd.afterT_intro (fun he => by
                    have hl := (Upd.lands_pop_nil (C := C) Ext.refl (υ.st.drop body.ext)).1
                    rw [he] at hl; cases hl)
                  fun _ σ' hL => (Upd.Lands.eq (Upd.lands_pop_nil _ _) hL) ▸ hbk))
                (Upd.lands_pop_nil _ _)
            · refine .inl ⟨hfr, hag', ?_⟩
              exact ⟨hpost.1 (fun hb' => hbk (Upd.afterT.of_lands hb' (Upd.lands_pop_nil _ _))),
                hbk⟩
      · rw [hc'] at hc; cases hc)
    o₁ he
  cases o₁ with
  | ok τ => exact COut.after_seq (holdsC_modalK τ.st ω κ φ hL)
  | halt e => exact hL
  | violated => exact hL.elim

/-- **A diamond over a loop whose body calls back never holds**: the loop
may diverge (`ExecS.loopDiverge`, the over-approximation a box accepts),
whatever its invariant or variant, so no diamond rule over it is sound
(`docs/options.md`, O3). -/
theorem holdsC_diamond_loop {Γ Γb Γ₁ Γ₀ : Ctx} {a : LoopAnn C Γ} {c : Val C Γ .bool}
    {body : Prog C Γ Γb} {ω : Prog C Γ Γ₁} {κ : Frames C Γ₁ Γ₀} {φ : Fml C Γ₀} {σ : State C Γ}
    (hb : body.callsBack pay = true) :
    ¬ holdsC I pay σ (.modal .diamond (.cons (.loop a c body) ω) κ φ) := fun h =>
  nomatch (h _ (.halt (.loopDiverge hb))).1

end Inv

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
  | havocIntro _ ih => exact ih
  | growIntro _ ih => exact ih
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
  | loopExit _ _ ihT ihE =>
    refine fun σ => Hyps.wrapC_and _ ?_ σ (ihT σ) (ihE σ)
    exact fun τ a b => holdsC_loopExit
      (loopExit_cond _ ((holdsC_iff_holds _ rfl τ).1 b)) (a b)
  | @invBox Γ Γb Γ₁ Γ₂ H Iv dec brk qs c body ω κ φ xs hv hf _ _ _ ihI ihT ihE =>
    intro σ
    let A0 : Fml C Γ := (invFml Iv qs).invHyp (loopBreak brk c)
    let U : Upd C Γ (.val .bool :: Γ) := Upd.nil.decl
      (fse (H.freshC I (.modal .box (.cons (.loop (.inv Iv dec brk qs) c body) ω) κ φ)))
      (.val (p := .bool) c.lower)
    let cT : Fml C (.val .bool :: Γ) := .isBool (.pvV (p := .bool) .here) true
    let cF : Fml C (.val .bool :: Γ) := .isBool (.pvV (p := .bool) .here) false
    let A : Fml C (.val .bool :: Γ) := .upd .box (Upd.nil.pop (.push .refl))
      (.modalK .box body (.pop .block body.ext .nil)
        (Fml.invPost .box .refl ω κ φ (invFml Iv qs) (loopBreak brk c)))
    let B : Fml C (.val .bool :: Γ) := .upd .box (Upd.nil.pop (.push .refl)) (.modalK .box ω κ φ)
    have hX : holdsC I pay σ ((H.anonHavoc xs hv).wrap
        (.imp A0 (.upd .box U (.and (.imp cT A) (.imp cF B))))) :=
      (H.anonHavoc xs hv).wrapC_and (φ := .imp A0 (.upd .box U (.imp cT A)))
        (ψ := .imp A0 (.upd .box U (.imp cF B)))
        (χ := .imp A0 (.upd .box U (.and (.imp cT A) (.imp cF B))))
        (fun _ x y hI => Upd.afterT_and (x hI) (y hI) fun _ f g => ⟨f, g⟩) σ (ihT σ) (ihE σ)
    rw [Hyps.wrap_anonHavoc] at hX
    exact H.wrapC_and (fun _ a b => holdsC_invBox hf a b) σ (ihI σ) hX
  | capture _ hc _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_capture hc h) σ (ih σ)
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
  | callVal _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callVal h) σ (ih σ)
  | callStorage _ ih =>
    exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callStorage h) σ (ih σ)
  | callMem _ ih => exact fun σ => Hyps.wrapC_mono _ (fun _ h => holdsC_callMem h) σ (ih σ)
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
  | recCall _ hc _ ih => exact fun σ => hc σ fun ψ hψ => ih ψ hψ σ
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
theorem ProvesC.fmlValid {I : Invariant C} {φ : Fml C []}
    (d : ProvesC I.fml pay [] .nil φ) : ValidC I φ pay :=
  ProvesC.sound_of I.fo I.noTransfer d

/-- The same, for a transfer semantics (`ValidT`). -/
theorem ProvesC.validT {ts : TransferSem C} {φ : Fml C []}
    (d : ProvesC ts.inv.fml ts.pay [] .nil φ) : ValidT ts φ :=
  ProvesC.fmlValid d

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
  | _, .allocAll H x A => .allocAll (Hyps.openInv H) x A
  | _, .grow H => .grow (Hyps.openInv H)

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
    exact ih (φ := .havoc φ) (ψ := .havoc ψ) fun τ f st nt sb => h _ (f st nt sb)
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
  | allocAll H x A ih =>
    intro φ ψ h
    exact ih (φ := .allocAll x A φ) (ψ := .allocAll x A ψ) fun τ f o => h _ (f o)
  | grow H ih =>
    intro φ ψ h
    exact ih (φ := .grow φ) (ψ := .grow ψ) fun τ f st nt => h _ (f st nt)

/-- **The invariant assumed, opened**: at a leaf, each assumed invariant read
at its scope, a closed first-order formula the closer reads. -/
theorem Proves.openInv {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (h : Proves C R Γ₀ H.openInv φ)
    (hm : (H.wrap φ).modalFree = true := by first | rfl | decide) : Proves C R Γ₀ H φ :=
  .closeHolds (fun σ => H.wrap_openInv (fun _ h => h) σ (Proves.sound h σ)) hm

/-- A derivation of the translation proves the direct correctness statement
under the given callback invariant and transfer policy. -/
theorem ProvesC.valid {I : Invariant C} {φ : Spec C []} {pay : Bool}
    (d : ProvesC I.fml pay [] .nil φ.toFml) : Spec.ValidC I φ pay :=
  (Spec.validC_iff I φ pay).mpr (ProvesC.fmlValid d)

/-- info: 'Solidity.ProvesC.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProvesC.valid

/-- info: 'Solidity.ProvesC.fmlValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProvesC.fmlValid

end Solidity
