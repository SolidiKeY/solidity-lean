import Solidity.Calculus.Callback
import Solidity.Calculus.CallbackHolds
import Solidity.Calculus.CorrectCallback
import Solidity.Calculus.Sound
import Solidity.Calculus.UpdateRules
import Solidity.Semantics.NativeDeferredCallback
import Solidity.Semantics.CallbackFrame

/-!
# Callback soundness: the rules and taclets

First-order formulas read alike, outcomes through the frames, a rule with
callbacks, the context read with callbacks, the callback taclets.

A piece of `Calculus/CallbackSound.lean`, whose docstring describes the whole.
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
theorem holdsC_update {s : Stmt C Γ Γ'} {U : Upd C Γ Γ'} (hs : s.callsBack pay = false)
    (hr : Premise.Runs m s (.update U) σ) (h : holdsC I pay σ (.upd m U (Fml.modalK m ω κ φ))) :
    holdsC I pay σ (.modal m (.cons s ω) κ φ) := by
  have deterministic : ∀ {o : COut C σ.H Γ'}, ExecS (I.stateInv pay) σ s o →
      o = .ofRes (s.run σ) := fun he => Stmt.eq_run (I.stateInv pay) s hs he
  refine holdsC_cons fun o₁ he => ?_
  rw [deterministic he]
  cases ht : s.run σ with
  | ok o =>
    have hst : Stmt.runSt σ s = .ok o.st := by simp only [Stmt.runSt, ht]; rfl
    exact COut.after_seq (holdsC_modalK o.st ω κ φ
      (Upd.afterT.of_lands h (Upd.lands_of_applyP (hr.1 _ hst)).choose_spec))
  | error e =>
    have hst : Stmt.runSt σ s = .error e := by simp only [Stmt.runSt, ht]; rfl
    obtain ⟨hp, hd⟩ := hr.2 e hst
    refine ⟨?_, hp⟩
    cases m with
    | box => trivial
    | diamond =>
      by_cases hx : e = .exhausted
      · exact hx
      · have he := hd rfl hx
        exact (Upd.afterT.of_noExh h (Upd.globT_none_of_applyV he.1) he.2).elim

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
receiver another, not at address `0`, the success block from any state the callee leaves in
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
    (hok : holdsC I pay σ (.imp (Fml.isBool call.hasCode.lower true)
      (.imp (Fml.isBool call.notSelf.lower true)
      (.havoc (.imp (Fml.closedAt I) (rets.all (Fml.modalK .box ok
      (.pop .block ((Ext.append Γ ρ).trans ok.ext) (.seq ω κ)) φ)))))))
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
    have hc0 : call.hasCode.evalT σ = .ok true := by
      rw [ExtCall.hasCode_evalT]; simp only [hz, decide_false, Bool.not_false]
    have hcode : holdsC I pay σ (Fml.isBool call.hasCode.lower true) :=
      (holdsC_iff_holds _ rfl σ).mpr (holds_isBool_lower call.hasCode σ hc0)
    have hguard : holdsC I pay σ (Fml.isBool call.notSelf.lower true) :=
      (holdsC_iff_holds _ rfl σ).mpr (holds_isBool_lower call.notSelf σ hn)
    have h₁ := hok hcode hguard st nt sb ((holdsC_closedAt_iff hI hT _).2 hJ')
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

end Solidity
