import Solidity.Semantics.CallbackFrame
import Solidity.Calculus.RunFrameMem

/-!
# A callback run that allocates within its grown frame

`ExecS.frame` (`Semantics/CallbackFrame.lean`) for a body that allocates
(`Stmt.withinM`, `Calculus/RunFrameMem.lean`): a callback replaces the
storage and the ledger only, so a callback run of such a body grows the heap
keeping every older object, as its deterministic run does (`TGFrameM`):
`docs/kernel-port.md`, "Recursion", "What is left", step 4.
-/

namespace Solidity

open Solidity (Mutability)

variable {C : Contract}

section Frame

variable {J : StateInv C} {μ : Mutability}

/-- A callback run within `μ`, by `ExecS.frame`. -/
theorem ExecS.frameM_of_within {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'}
    {o : COut C σ.H Γ'} (h : ExecS J σ s o) (hw : s.within μ = true) (d : Nat)
    (o' : Out C σ.H Γ') (ho : o = .ok o') :
    TGFrameM μ σ o'.st o'.ext ∧ TLocAgreeM o'.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o'.st.env) :=
  let ⟨hg, ha⟩ := ExecS.frame h hw d o' ho
  ⟨TGFrameM.ofFrame hg _, TLocAgreeM.ofAgree hg.H ha⟩

mutual

/-- `ExecS.frameM` where the statement is not within `μ` (`ExecS.frame`
covers that one). -/
theorem ExecS.frameM_aux : {Γ Γ' : Ctx} → {σ : State C Γ} → {s : Stmt C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecS J σ s o → s.withinM μ = true → s.within μ = false →
    (d : Nat) → (o' : Out C σ.H Γ') → o = .ok o' →
      TGFrameM μ σ o'.st o'.ext ∧
        TLocAgreeM o'.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o'.st.env)
  | _, _, σ, s, _, .det _, hw, _, d, o', ho => by
    cases hr : s.run σ with
    | error => rw [hr] at ho; cases ho
    | ok x =>
      rw [hr] at ho; cases ho
      exact Stmt.run_frameM s hw d hr
  | _, _, _, _, _, .iteThen (c := c) (thn := thn) (els := els) (o := o₁) _ hp, hw, hwi, d, o',
      ho => by
    have hw' : (c.readsIn μ && Prog.withinM μ thn && Prog.withinM μ els) = true := by
      simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frameM hp hw'.1.2 d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha.left⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .iteElse (c := c) (thn := thn) (els := els) (o := o₁) _ hp, hw, hwi, d, o',
      ho => by
    have hw' : (c.readsIn μ && Prog.withinM μ thn && Prog.withinM μ els) = true := by
      simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frameM hp hw'.2 d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha.right⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, σ, _, _, .callBody (args := args) (ret := ret) (body := body) (a := a) (o := o₁) _ hp,
      hw, hwi, d, o', ho => by
    have hw' : (args.readsIn μ && Prog.withinM μ body) = true := by
      simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frameM hp hw'.2 0
    cases o₁ with
    | ok x =>
      cases ho
      have he := CallRet.enterT_frameM (μ := μ) ret (σ.withEnv a)
      obtain ⟨hg, -⟩ := ih x rfl
      exact ⟨(((TGFrameM.env σ a (List.prefix_refl _)).trans he
        (ret.enterT (σ.withEnv a)).ext).trans hg _).withEnv _,
        CallRet.leaveT_frameM ret _ σ.env _ d⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .callRec h, hw, hwi, d, o', ho => ExecS.frameM_aux h hw hwi d o' ho
  | _, _, _, _, _, .block (body := body) (o := o₁) _ hp, hw, hwi, d, o', ho => by
    have hw' : Prog.withinM μ body = true := by
      simpa only [Stmt.withinM, hwi, Bool.false_or] using hw
    have ih := ExecP.frameM hp hw' d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .transferHalt .., _, _, _, _, ho | _, _, _, _, _, .transferViolated .., _, _, _, _, ho
  | _, _, _, _, _, .sendHalt .., _, _, _, _, ho | _, _, _, _, _, .sendViolated .., _, _, _, _, ho
  | _, _, _, _, _, .iteHalt .., _, _, _, _, ho | _, _, _, _, _, .callArgs .., _, _, _, _, ho
  | _, _, _, _, _, .loopHalt .., _, _, _, _, ho | _, _, _, _, _, .loopDiverge .., _, _, _, _, ho
  | _, _, _, _, _, .tryRevert .., _, _, _, _, ho | _, _, _, _, _, .tryDecode .., _, _, _, _, ho
  | _, _, _, _, _, .tryViolated .., _, _, _, _, ho | _, _, _, _, _, .trySelfHalt .., _, _, _, _, ho
  | _, _, _, _, _, .trySelfViolated .., _, _, _, _, ho => by cases ho
  | _, _, _, _, _, .transferResume .., hw, hwi, _, _, _
  | _, _, _, _, _, .sendFailed .., hw, hwi, _, _, _
  | _, _, _, _, _, .sendRefused .., hw, hwi, _, _, _
  | _, _, _, _, _, .sendResume .., hw, hwi, _, _, _
  | _, _, _, _, _, .loopExit .., hw, hwi, _, _, _
  | _, _, _, _, _, .loopIter .., hw, hwi, _, _, _
  | _, _, _, _, _, .loopStop .., hw, hwi, _, _, _
  | _, _, _, _, _, .tryOk .., hw, hwi, _, _, _
  | _, _, _, _, _, .tryError .., hw, hwi, _, _, _
  | _, _, _, _, _, .tryPanic .., hw, hwi, _, _, _
  | _, _, _, _, _, .tryOther .., hw, hwi, _, _, _
  | _, _, _, _, _, .trySelfOk .., hw, hwi, _, _, _
  | _, _, _, _, _, .trySelfError .., hw, hwi, _, _, _
  | _, _, _, _, _, .trySelfOther .., hw, hwi, _, _, _
  | _, _, _, _, _, .trySelfPanic .., hw, hwi, _, _, _
  | _, _, _, _, _, .callReceiver .., hw, hwi, _, _, _
  | _, _, _, _, _, .callReceiverPush .., hw, hwi, _, _, _
  | _, _, _, _, _, .callReceiverPushUnset .., hw, hwi, _, _, _
  | _, _, _, _, _, .callReceiverPushHalt .., hw, hwi, _, _, _
  | _, _, _, _, _, .callReceiverPushViolated .., hw, hwi, _, _, _
  | _, _, _, _, _, .catchDataHalt .., hw, hwi, _, _, _
  | _, _, _, _, _, .catchDataBody .., hw, hwi, _, _, _ => by
    simp only [Stmt.withinM, hwi, Bool.or_false, Bool.false_eq_true] at hw
  termination_by structural _ _ _ _ _ h => h

/-- **A callback run of a program that allocates within `μ` runs within
`μ`'s grown frame.** -/
theorem ExecP.frameM : {Γ Γ' : Ctx} → {σ : State C Γ} → {P : Prog C Γ Γ'} →
    {o : COut C σ.H Γ'} → ExecP J σ P o → Prog.withinM μ P = true → (d : Nat) →
    (o' : Out C σ.H Γ') → o = .ok o' →
      TGFrameM μ σ o'.st o'.ext ∧
        TLocAgreeM o'.ext d (Prog.writesAt d P) σ.env (TEnv.drop P.ext o'.st.env)
  | _, _, σ, _, _, .nil, _, _, o', ho => by
    cases ho
    exact ⟨TGFrameM.ofFrame (TGFrame.refl σ) _, TLocAgreeM.ofAgree rfl (TLocAgree.refl _)⟩
  | _, _, σ, _, _, .cons (s := s) (P := P) (o₁ := o₁) (o := o₂) hs hp, hw, d, o', ho => by
    rw [Prog.withinM_cons, Bool.and_eq_true] at hw
    have h₁ : TGFrameM μ σ o₁.st o₁.ext ∧
        TLocAgreeM o₁.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o₁.st.env) := by
      cases hwi : s.within μ
      · exact ExecS.frameM_aux hs hw.1 hwi d o₁ rfl
      · exact ExecS.frameM_of_within hs hwi d o₁ rfl
    obtain ⟨hg₁, ha₁⟩ := h₁
    have ih := ExecP.frameM hp hw.2 (d + s.ext.depth)
    cases o₂ with
    | ok x =>
      cases ho
      obtain ⟨hg₂, ha₂⟩ := ih x rfl
      refine ⟨hg₁.trans hg₂ _, ?_⟩
      show TLocAgreeM _ d (Stmt.writesAt d s ++ Prog.writesAt (d + s.ext.depth) P) σ.env
        (TEnv.drop (s.ext.trans P.ext) x.st.env)
      rw [TEnv.drop_trans]
      exact ha₁.left.trans (TLocAgreeM.drop s.ext ha₂).right
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .halt _, _, _, _, ho | _, _, _, _, _, .violated _, _, _, _, ho => by cases ho
  termination_by structural _ _ _ _ _ h => h

end

/-- **A callback run of a statement that allocates within `μ` runs within
`μ`'s grown frame.** -/
theorem ExecS.frameM {Γ Γ' : Ctx} {σ : State C Γ} {s : Stmt C Γ Γ'} {o : COut C σ.H Γ'}
    (h : ExecS J σ s o) (hw : s.withinM μ = true) (d : Nat) (o' : Out C σ.H Γ')
    (ho : o = .ok o') :
    TGFrameM μ σ o'.st o'.ext ∧ TLocAgreeM o'.ext d (s.writesAt d) σ.env (TEnv.drop s.ext o'.st.env) := by
  cases hwi : s.within μ
  · exact ExecS.frameM_aux h hw hwi d o' ho
  · exact ExecS.frameM_of_within h hwi d o' ho

end Frame

end Solidity
