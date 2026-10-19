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
    (h : ∀ o₁, ExecS (I.stateInv pay) σ s o₁ → o₁.thenF (I.stateInv pay) (.seq ω κ) m (holdsC I pay · φ)) :
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
    have hA := holdsC_modalK σ P _ φ (h.1 ((holdsC_iff_holds c (Fml.callsBack_of_hasTransfer c hT) σ).2 hh))
    exact COut.thenF_drop _ (hA o' hP)
  · obtain ⟨o', hQ, rfl⟩ := (hc' hh).2 _ o₁ he
    have hB := holdsC_modalK σ Q _ φ (h.2 ((holdsC_iff_holds c' (Fml.callsBack_of_hasTransfer c' hT') σ).2 hh))
    exact COut.thenF_drop _ (hB o' hQ)

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
    (h : ∀ τ, holdsC I pay τ φ → holdsC I pay τ ψ) (σ : State C Γ₀) (hφ : holdsC I pay σ (H.wrap φ)) :
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
theorem holdsC_sendCb (hI : I.FO = true) (hT : I.hasTransfer = false) (pv : Idx Γ (.val .bool))
    (sadr se : Simple C Γ .uint) (full : Bool)
    (hx : holdsC I pay σ (.upd .box (Upd.nil.snoc (UpdElem.payTo sadr se)) (Fml.closedAt I)))
    (hok : holdsC I pay σ (.upd .box ((Upd.nil.snoc (UpdElem.payTo sadr se)).snoc
      (.local pv (.val (Tm.lit (p := .bool) true)))) (.havoc (.imp (Fml.closedAt I) (Fml.modalK .box ω κ φ)))))
    (hf : holdsC I pay σ (.upd .box (Upd.nil.snoc (.local pv (.val (Tm.lit (p := .bool) false))))
      (Fml.modalK .box ω κ φ))) :
    holdsC I pay σ (.modal .box (.cons (.send pv (.simple sadr) (.simple se) full) ω) κ φ) := by
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
theorem holdsC_tryCb (hI : I.FO = true) (hT : I.hasTransfer = false) {ρ κc Γok Γe Γ₃ Γ₄ : Ctx}
    (call : ExtCall C Γ) (rets : Binders ρ) (ok : Prog C (ρ ++ Γ) Γok) (err : Prog C Γ Γe)
    (code : CodeBinder κc) (pnc : Prog C (κc ++ Γ) Γ₃) (other : Prog C Γ Γ₄)
    (hx : holdsC I pay σ (Fml.closedAt I))
    (hok : holdsC I pay σ (.havoc (.imp (Fml.closedAt I) (rets.all
      (Fml.modalK .box ok (.pop .block ((Ext.append Γ ρ).trans ok.ext) (.seq ω κ)) φ)))))
    (herr : holdsC I pay σ (Binders.nil.all
      (Fml.modalK .box err (.pop .block ((Ext.append Γ []).trans err.ext) (.seq ω κ)) φ)))
    (hpnc : holdsC I pay σ (code.binders.all
      (Fml.modalK .box pnc (.pop .block ((Ext.append Γ κc).trans pnc.ext) (.seq ω κ)) φ)))
    (hoth : holdsC I pay σ (Binders.nil.all
      (Fml.modalK .box other (.pop .block ((Ext.append Γ []).trans other.ext) (.seq ω κ)) φ))) :
    holdsC I pay σ (.modal .box (.cons (.tryCall call rets ok err code pnc other) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  cases he with
  | det hf => nomatch hf
  | tryRevert => exact ⟨trivial, nofun⟩
  | tryDecode hd => exact ⟨trivial, fun he => rets.decodeT_ne_panic _ (he ▸ hd)⟩
  | tryViolated hn => exact (hn ((holdsC_closedAt_iff hI hT σ).1 hx)).elim
  | tryOk hJ hJ' hd hP =>
    rename_i st nt _ _ r o
    have h₁ := hok st nt ((holdsC_closedAt_iff hI hT _).2 hJ')
    have h₂ := holdsC_binders_all rets (σ.havoc st nt) _ r h₁
    exact COut.thenF_drop _ (holdsC_modalK _ ok _ φ h₂ o hP)
  | tryError hP =>
    rw [show (Ext.append Γ []).trans err.ext = err.ext from Subsingleton.elim _ _] at herr
    exact COut.thenF_drop _ (holdsC_modalK σ err _ φ herr _ hP)
  | tryPanic hP =>
    rename_i v o
    have h₂ := holdsC_binders_all code.binders σ _ (code.decodeT v) hpnc
    exact COut.thenF_drop _ (holdsC_modalK _ pnc _ φ h₂ o hP)
  | tryOther hP =>
    rw [show (Ext.append Γ []).trans other.ext = other.ext from Subsingleton.elim _ _] at hoth
    exact COut.thenF_drop _ (holdsC_modalK σ other _ φ hoth _ hP)

end Taclets

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
    exact fun τ ab cd => holdsC_tryCb hI hT _ _ _ _ _ _ _ (holdsC_and_left ab)
      (holdsC_and_right ab) (holdsC_and_left cd) (holdsC_and_left (holdsC_and_right cd))
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
