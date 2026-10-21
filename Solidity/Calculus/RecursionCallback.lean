import Solidity.Calculus.Recursion
import Solidity.Calculus.CallbackDerive

/-!
# Recursive calls under the callback reading

`docs/kernel-port.md`, "Recursion", row "Callbacks (O7)".  A recursive
call's body is its unrolling (`recUnroll`), so whether it calls back
(`Stmt.callsBack`, `Semantics/Callback.lean`) is read off its frames.  Every
frame is the same body with the recursive site a hole, so it is read off one
frame (`Prog.callsBack_recUnroll`), the frame below by hypothesis:
`sol_no_callback` proves `φ.callsBack pay = false` so, never forcing the
`recDepth` frames.  A recursion that does not call back is then read without
callbacks (`validT_noCallback_iff`), where `rec_auto` proves it.
-/

namespace Solidity

open Solidity (Modality Mutability)

variable {C : Contract}

/-! ## `callsBack` by constructor

The equations `sol_no_callback` rewrites with: one per constructor, so that
`simp` never unfolds a definition at a term that is not one (an invariant
`I.fml`, an unrolling). -/

section Eqns

variable {pay : Bool} {Γ Γ₀ : Ctx}

theorem Prog.callsBack_nil : Prog.callsBack pay (.nil : Prog C Γ Γ) = false := rfl

theorem Fml.callsBack_tt : (Fml.tt : Fml C Γ).callsBack pay = false := rfl
theorem Fml.callsBack_not (φ : Fml C Γ) : (Fml.not φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_upd {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    (Fml.upd m U φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_havoc (φ : Fml C Γ) : (Fml.havoc φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_all (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (Fml.all x p φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_bind (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    (Fml.bind m x t φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_anon (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    (Fml.anon xs φ).callsBack pay = φ.callsBack pay := rfl
theorem Fml.callsBack_closedAt (I : Fml C []) :
    (Fml.closedAt I : Fml C Γ).callsBack pay = I.callsBack pay := rfl

theorem Frames.callsBack_nil : (Frames.nil : Frames C Γ Γ).callsBack pay = false := rfl
theorem Frames.callsBack_pop {Γ' : Ctx} (b : BlockKind) (h : Ext Γ Γ') (κ : Frames C Γ Γ₀) :
    (Frames.pop b h κ).callsBack pay = κ.callsBack pay := rfl
theorem Frames.callsBack_drop {Γ' : Ctx} (h : Thin Γ Γ') (κ : Frames C Γ Γ₀) :
    (Frames.drop h κ).callsBack pay = κ.callsBack pay := rfl

theorem Hyps.wrap_nil' (φ : Fml C Γ₀) : (Hyps.nil : Hyps C Γ₀ Γ₀).wrap φ = φ := rfl
theorem Hyps.wrap_pre' (H : Hyps C Γ₀ Γ) (a φ : Fml C Γ) : (H.pre a).wrap φ = H.wrap (.imp a φ) :=
  rfl
theorem Hyps.wrap_upd' {Δ : Ctx} (H : Hyps C Γ₀ Γ) (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    (H.upd m U).wrap φ = H.wrap (.upd m U φ) := rfl
theorem Hyps.wrap_havoc' (H : Hyps C Γ₀ Γ) (φ : Fml C Γ) : H.havoc.wrap φ = H.wrap (.havoc φ) :=
  rfl
theorem Hyps.wrap_all' (H : Hyps C Γ₀ Γ) (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (H.all x p).wrap φ = H.wrap (.all x p φ) := rfl
theorem Hyps.wrap_bind' (H : Hyps C Γ₀ Γ) (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    (H.bind m x t).wrap φ = H.wrap (.bind m x t φ) := rfl
theorem Hyps.wrap_anon' (H : Hyps C Γ₀ Γ) (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    (H.anon xs).wrap φ = H.wrap (.anon xs φ) := rfl

end Eqns

/-- **A recursive call that does not call back**, read without callbacks
(`ProvesC.recCall`, no goal): where nothing in the sequent calls back, the
two readings agree (`holdsC_iff_holds`), and `rec_auto` proves it `Valid`. -/
theorem ProvesC.recValid {I : Fml C []} {pay : Bool} {Γ Γ' ps rs Γ₁ Γ₂ : Ctx} {H : Hyps C [] Γ}
    {m : Modality} {f : Name} {d : Nat} {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {body : Unit → Prog C (rs ++ ps) (rs ++ ps)} {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂}
    {φ : Fml C Γ₂}
    (h : Valid (H.wrap (.modal m (.cons (.callRec f d args ret body) ω) κ φ)))
    (hφ : (H.wrap (.modal m (.cons (.callRec f d args ret body) ω) κ φ)).callsBack pay = false) :
    ProvesC I pay [] H (.modal m (.cons (.callRec f d args ret body) ω) κ φ) :=
  .recCall [] (fun τ _ => (holdsC_iff_holds _ hφ τ).2 (h τ)) nofun

/-! ## A callback run within its frame

`Stmt.run_frame` for the callback runs: a body within `μ` (`Prog.within`)
leaves the heap, the funds and the transaction, the storage and the ledger
unless `μ` is `nonpayable` (a callback replaces them, `State.havoc`, and only
a `nonpayable` body pays), and writes only its own locals. -/

section Frame

variable {J : StateInv C} {μ : Mutability}

theorem TGFrame.havoc {Γ : Ctx} (σ : State C Γ) (st : Storage C) (nt : Ledger) :
    TGFrame .nonpayable σ (σ.havoc st nt) :=
  ⟨rfl, HEq.rfl, rfl, rfl, fun h => absurd rfl h⟩

mutual

/-- **A callback run of a statement within `μ` runs within `μ`'s frame.** -/
theorem ExecS.frame : {Γ Γ' : Ctx} → {σ : State C Γ} → {s : Stmt C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecS J σ s o → s.within μ = true → (d : Nat) →
    (o' : Out C σ.H Γ') → o = .ok o' →
      TGFrame μ σ o'.st ∧ TLocAgree d (s.writesAt d) σ.env (TEnv.drop s.ext o'.st.env)
  | _, _, σ, s, _, .det _, hw, d, o', ho => by
    cases hr : s.run σ with
    | error => rw [hr] at ho; cases ho
    | ok x =>
      rw [hr] at ho; cases ho
      exact Stmt.run_frame s hw d hr
  | _, _, _, _, _, .transferResume (r := r) (a := a) _ ht _ _, hw, d, o', ho => by
    have hμ := nonpayable_of_within' hw
    subst hμ
    cases ho
    obtain ⟨hg, ha⟩ := Stmt.run_frame (Stmt.transfer r a) hw d ht
    exact ⟨hg.trans (TGFrame.havoc _ _ _), ha⟩
  | _, _, σ, _, _, .sendFailed (pv := pv) _ _, _, d, o', ho => by
    cases ho
    exact ⟨TGFrame.setLocal σ pv _, TLocAgree.set pv _ _⟩
  | _, _, σ, _, _, .sendResume (pv := pv) (r := r) (a := a) _ ht _ _, hw, d, o', ho => by
    have hμ := nonpayable_of_within' hw
    subst hμ
    cases ho
    obtain ⟨hg, ha⟩ := Stmt.run_frame (μ := .nonpayable) (Stmt.transfer r a) hw d ht
    refine ⟨(hg.trans (TGFrame.havoc _ _ _)).trans (TGFrame.setLocal _ pv _), ?_⟩
    exact (ha.mono (W' := pv.outer d) fun _ h => by cases h).trans (TLocAgree.set pv _ _)
  | _, _, _, _, _, .iteThen (thn := thn) (o := o₁) _ hp, hw, d, o', ho => by
    have hw' : (_ && Prog.within μ thn && _) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frame hp hw'.1.2 d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha.left⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .iteElse (els := els) (o := o₁) _ hp, hw, d, o', ho => by
    have hw' : (_ && _ && Prog.within μ els) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frame hp hw'.2 d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha.right⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, σ, _, _, .callBody (ret := ret) (body := body) (a := a) (o := o₁) _ hp, hw, d, o', ho => by
    have hw' : (_ && ret.noMem && Prog.within μ body) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frame hp hw'.2 0
    cases o₁ with
    | ok x =>
      cases ho
      have he := CallRet.enterT_frame (μ := μ) ret hw'.1.2 (σ.withEnv a)
      obtain ⟨hg, -⟩ := ih x rfl
      have hg' := ((TGFrame.env σ a).trans he).trans hg
      exact ⟨hg'.withEnv _, CallRet.leaveT_frame ret hw'.1.2 _ hg'.H σ.env _ d⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .callRec h, hw, d, o', ho => ExecS.frame h hw d o' ho
  | _, _, σ, _, _, .loopExit _ _, _, d, o', ho => by
    cases ho
    exact ⟨TGFrame.refl σ, TLocAgree.refl _⟩
  | _, _, σ, _, _, .loopIter (body := body) (υ := υ) (o := o₁) _ _ hp hl, hw, d, o', ho => by
    have hw' : (_ && Prog.within μ body) = true := hw
    rw [Bool.and_eq_true] at hw'
    obtain ⟨hg, ha⟩ := ExecP.frame hp hw'.2 d υ rfl
    have ih := ExecS.frame hl hw d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg', ha'⟩ := ih x rfl
      exact ⟨(hg.withEnv _).trans hg', ha.trans ha'⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .loopStop (o := o₁) _ _ _ hk, _, _, o', ho => by
    cases o₁ with
    | ok => cases hk
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .block (body := body) (o := o₁) _ hp, hw, d, o', ho => by
    have ih := ExecP.frame hp hw d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .transferHalt .., _, _, _, ho | _, _, _, _, _, .transferViolated .., _, _, _, ho
  | _, _, _, _, _, .sendHalt .., _, _, _, ho | _, _, _, _, _, .sendViolated .., _, _, _, ho
  | _, _, _, _, _, .iteHalt .., _, _, _, ho | _, _, _, _, _, .callArgs .., _, _, _, ho
  | _, _, _, _, _, .loopHalt .., _, _, _, ho | _, _, _, _, _, .loopDiverge .., _, _, _, ho =>
    by cases ho
  | _, _, _, _, _, .callReceiver .., hw, _, _, _
  | _, _, _, _, _, .callReceiverPush .., hw, _, _, _
  | _, _, _, _, _, .callReceiverPushUnset .., hw, _, _, _
  | _, _, _, _, _, .callReceiverPushHalt .., hw, _, _, _
  | _, _, _, _, _, .callReceiverPushViolated .., hw, _, _, _
  | _, _, _, _, _, .tryRevert .., hw, _, _, _ | _, _, _, _, _, .tryDecode .., hw, _, _, _
  | _, _, _, _, _, .tryViolated .., hw, _, _, _ | _, _, _, _, _, .tryOk .., hw, _, _, _
  | _, _, _, _, _, .tryError .., hw, _, _, _ | _, _, _, _, _, .tryPanic .., hw, _, _, _
  | _, _, _, _, _, .tryOther .., hw, _, _, _ | _, _, _, _, _, .trySelfOk .., hw, _, _, _
  | _, _, _, _, _, .trySelfHalt .., hw, _, _, _ | _, _, _, _, _, .trySelfError .., hw, _, _, _
  | _, _, _, _, _, .trySelfOther .., hw, _, _, _ | _, _, _, _, _, .trySelfPanic .., hw, _, _, _
  | _, _, _, _, _, .trySelfViolated .., hw, _, _, _
  | _, _, _, _, _, .catchDataHalt .., hw, _, _, _
  | _, _, _, _, _, .catchDataBody .., hw, _, _, _ => by cases hw
  termination_by structural _ _ _ _ _ h => h

/-- **A callback run of a program within `μ` runs within `μ`'s frame.** -/
theorem ExecP.frame : {Γ Γ' : Ctx} → {σ : State C Γ} → {P : Prog C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecP J σ P o → Prog.within μ P = true → (d : Nat) →
    (o' : Out C σ.H Γ') → o = .ok o' →
      TGFrame μ σ o'.st ∧ TLocAgree d (Prog.writesAt d P) σ.env (TEnv.drop P.ext o'.st.env)
  | _, _, σ, _, _, .nil, _, _, o', ho => by
    cases ho
    exact ⟨TGFrame.refl σ, TLocAgree.refl _⟩
  | _, _, σ, _, _, .cons (s := s) (P := P) (o₁ := o₁) (o := o₂) hs hp, hw, d, o', ho => by
    have hw' : (Stmt.within μ s && Prog.within μ P) = true := hw
    rw [Bool.and_eq_true] at hw'
    obtain ⟨hg₁, ha₁⟩ := ExecS.frame hs hw'.1 d o₁ rfl
    have ih := ExecP.frame hp hw'.2 (d + s.ext.depth)
    cases o₂ with
    | ok x =>
      cases ho
      obtain ⟨hg₂, ha₂⟩ := ih x rfl
      refine ⟨hg₁.trans hg₂, ?_⟩
      show TLocAgree d (Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P) σ.env
        (TEnv.drop (s.ext.trans P.ext) x.st.env)
      rw [TEnv.drop_trans]
      exact ha₁.left.trans (TLocAgree.drop s.ext ha₂).right
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .halt _, _, _, _, ho | _, _, _, _, _, .violated _, _, _, _, ho => by cases ho
  termination_by structural _ _ _ _ _ h => h

end

end Frame

namespace RecursionCallback

open Lean Elab Tactic Meta

/-- Whether `e` mentions an unrolling (`recUnroll`). -/
def hasUnroll (e : Expr) : Bool := (e.find? (·.isConstOf ``recUnroll)).isSome

/-- `X.callsBack pay = false` (or `hasTransfer`): the formula's statements by
`simp`, a recursive call's body frame by frame (`Prog.callsBack_recUnroll`,
the frame below by the hypothesis `ih`), what is left by `rfl` where no
unrolling is left in it. -/
partial def proveNoCallback (g : MVarId) (fuel : Nat := 32) : TacticM Bool := g.withContext do
  if fuel == 0 then return false
  let simpT ← `(tactic| simp only [Hyps.wrap_nil', Hyps.wrap_pre', Hyps.wrap_upd',
      Hyps.wrap_havoc', Hyps.wrap_all', Hyps.wrap_bind', Hyps.wrap_anon', Fml.modalK_nil,
      Fml.modalK_cons, Frames.exit_nil, Frames.exit_seq, Frames.exit_pop, Fml.callsBack_tt,
      Fml.callsBack_not, Fml.callsBack_and,
      Fml.callsBack_imp, Fml.callsBack_upd, Fml.callsBack_modal, Fml.callsBack_havoc,
      Fml.callsBack_all, Fml.callsBack_bind, Fml.callsBack_anon, Fml.callsBack_closedAt,
      Invariant.noCallsBack, Frames.callsBack_nil, Frames.callsBack_seq, Frames.callsBack_pop,
      Frames.callsBack_drop, Prog.callsBack_cons, Prog.callsBack_nil, Stmt.callsBack,
      CallbackWk.callsBack_prog, Bool.or_false, Bool.false_or, Bool.or_self, *])
  let gs ← match ← Recursion.tryOn g (evalTactic simpT) with
    | some gs => pure gs
    | none => pure [g]
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    unless hasUnroll ty do
      if let some [] ← Recursion.tryOn g' (evalTactic (← `(tactic| rfl))) then continue
      return false
    -- an unrolling: no frame calls back where none of one frame does
    let some gs' ← Recursion.tryOn g' (evalTactic (← `(tactic| rw [Prog.callsBack_recUnroll])))
      | return false
    for g'' in gs' do
      let ty ← instantiateMVars (← g''.getType)
      let g'' ← if ty.isForall then do
          let some [g₃] ← Recursion.tryOn g'' (evalTactic (← `(tactic| intro n t ih)))
            | return false
          pure g₃
        else pure g''
      unless ← proveNoCallback g'' (fuel - 1) do return false
  return true

end RecursionCallback

open Lean Elab Tactic Meta in
/-- `sol_no_callback`: `φ.callsBack pay = false` (`Fml.callsBack`, through
the context `Hyps.wrap`), a recursive call's unrolling read off one frame
(`Prog.callsBack_recUnroll`). -/
elab "sol_no_callback" : tactic => do
  let g ← getMainGoal
  unless ← RecursionCallback.proveNoCallback g do
    throwError "sol_no_callback: a statement may call back{indentExpr (← g.getType)}"
  setGoals ((← getGoals).filter (· != g))

end Solidity
