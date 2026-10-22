import Solidity.Semantics.Callback

/-!
# A callback run within its frame

`Stmt.run_frame` (`Semantics/RunFrame.lean`) for the callback runs: what a
recursive contract over the callback runs (`Calculus/RecursionCallback.lean`)
and the loop invariant rule with callbacks (`ProvesC.invBox`,
`Calculus/CallbackSound.lean`) read of a body's run.
-/

namespace Solidity

open Solidity (Mutability)

variable {C : Contract}

/-! ## A callback run within its frame

`Stmt.run_frame` for the callback runs: a body within `μ` (`Prog.within`)
leaves the heap, the funds and the transaction, the storage and the ledger
unless `μ` is `nonpayable` (a callback replaces them, `State.havoc`, and only
a `nonpayable` body pays), and writes only its own locals. -/

section Frame

variable {J : StateInv C} {μ : Mutability}

theorem TGFrame.havoc {Γ : Ctx} (σ : State C Γ) (st : Storage C) (nt : Ledger) (sb : PrimTy.uint.Denote) :
    TGFrame .nonpayable σ (σ.havoc st nt sb) :=
  ⟨rfl, HEq.rfl, (fun h => absurd rfl h), rfl, fun h => absurd rfl h⟩

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
    exact ⟨hg.trans (TGFrame.havoc _ _ _ _), ha⟩
  | _, _, σ, _, _, .sendFailed (pv := pv) _ _, _, d, o', ho
  | _, _, σ, _, _, .sendRefused (pv := pv) _ _, _, d, o', ho => by
    cases ho
    exact ⟨TGFrame.setLocal σ pv _, TLocAgree.set pv _ _⟩
  | _, _, σ, _, _, .sendResume (pv := pv) (r := r) (a := a) _ ht _ _, hw, d, o', ho => by
    have hμ := nonpayable_of_within' hw
    subst hμ
    cases ho
    obtain ⟨hg, ha⟩ := Stmt.run_frame (μ := .nonpayable) (Stmt.transfer r a) hw d ht
    refine ⟨(hg.trans (TGFrame.havoc _ _ _ _)).trans (TGFrame.setLocal _ pv _), ?_⟩
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
  | _, _, _, _, _, .catchDataHalt .., hw, _, _, _
  | _, _, _, _, _, .catchDataBody .., hw, _, _, _ => by cases hw
  | _, _, _, _, _, .tryRevert .., _, _, _, ho | _, _, _, _, _, .tryDecode .., _, _, _, ho
  | _, _, _, _, _, .tryViolated .., _, _, _, ho | _, _, _, _, _, .trySelfHalt .., _, _, _, ho
  | _, _, _, _, _, .trySelfViolated .., _, _, _, ho => by cases ho
  -- a `try` (`Stmt.within`: it pays): each clause from the state it starts in
  | Γ, _, σ, _, _, .tryOk (ρ := ρ) (ok := ok) (st := st) (nt := nt) (sb := sb) (r := r) (o := o₁) _ _ _ hp _,
      hw, d, o', ho => by
    have hw' : ((μ == .nonpayable) && _ && _ && Prog.within μ ok && _ && _ && _) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have hh : TGFrame μ σ (σ.havoc st nt sb) := by
      rw [nonpayable_of_within' hw'.1.1.1.1.1.1]; exact TGFrame.havoc σ st nt sb
    have ih := ExecP.frame hp hw'.1.1.1.2 (d + (Ext.append Γ ρ).depth)
    cases o₁ with
    | ok x =>
      cases ho
      have := TGFrame.clause hh d r ok.ext (ih x rfl)
      exact ⟨this.1, this.2.left.left.left⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .tryError (err := err) (o := o₁) _ hp, hw, d, o', ho
  | _, _, _, _, _, .trySelfError (err := err) (o := o₁) _ _ _ hp, hw, d, o', ho => by
    have hw' : (_ && _ && _ && _ && Prog.within μ err && _ && _) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frame hp hw'.1.1.2 d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha.right.left.left⟩
    | halt => cases ho
    | violated => cases ho
  | _, _, _, _, _, .tryOther (other := other) (o := o₁) _ hp, hw, d, o', ho
  | _, _, _, _, _, .trySelfOther (other := other) (o := o₁) _ _ _ _ hp, hw, d, o', ho => by
    have hw' : (_ && _ && _ && _ && _ && _ && Prog.within μ other) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frame hp hw'.2 d
    cases o₁ with
    | ok x =>
      cases ho
      obtain ⟨hg, ha⟩ := ih x rfl
      exact ⟨hg.withEnv _, ha.right⟩
    | halt => cases ho
    | violated => cases ho
  | Γ, _, σ, _, _, .tryPanic (κ := κ) (pnc := pnc) (o := o₁) _ hp, hw, d, o', ho
  | Γ, _, σ, _, _, .trySelfPanic (κ := κ) (pnc := pnc) (o := o₁) _ _ _ _ hp, hw, d, o', ho => by
    have hw' : (_ && _ && _ && _ && _ && Prog.within μ pnc && _) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have ih := ExecP.frame hp hw'.1.2 (d + (Ext.append Γ κ).depth)
    cases o₁ with
    | ok x =>
      cases ho
      have := TGFrame.clause (TGFrame.refl σ) d _ pnc.ext (ih x rfl)
      exact ⟨this.1, this.2.right.left⟩
    | halt => cases ho
    | violated => cases ho
  | Γ, _, σ, _, _, .trySelfOk (ρ := ρ) (rets := rets) (ok := ok) (sargs := sargs) (sbody := sbody)
      (o₁ := o₁) (o := o₂) _ _ hc hp, hw, d, o', ho => by
    have hw' : ((μ == .nonpayable) && sargs.readsIn μ && Prog.within μ sbody && Prog.within μ ok &&
        _ && _ && _) = true := hw
    simp only [Bool.and_eq_true] at hw'
    have hwc : (sargs.readsIn μ && (CallRet.rets (Γ := Γ) rets).noMem &&
        Prog.within μ sbody) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨hw'.1.1.1.1.1.2, rfl⟩, hw'.1.1.1.1.2⟩
    obtain ⟨hg₁, ha₁⟩ := ExecS.frame hc hwc d o₁ rfl
    have ih := ExecP.frame hp hw'.1.1.1.2 (d + (Ext.append Γ ρ).depth)
    cases o₂ with
    | ok x =>
      cases ho
      obtain ⟨hg₂, ha₂⟩ := ih x rfl
      refine ⟨(hg₁.trans hg₂).withEnv _, ?_⟩
      show TLocAgree d (_ ++ _ ++ _ ++ _) σ.env (TEnv.drop ((Ext.append Γ ρ).trans ok.ext) _)
      rw [TEnv.drop_trans]
      have ha₁' : TLocAgree d (Prog.writesAt (d + (Ext.append Γ ρ).depth) ok) σ.env
          (TEnv.drop (Ext.append Γ ρ) o₁.st.env) :=
        TLocAgree.mono (W := []) (fun _ h => absurd h List.not_mem_nil) ha₁
      exact (ha₁'.trans (TLocAgree.drop (Ext.append Γ ρ) ha₂)).left.left.left
    | halt => cases ho
    | violated => cases ho
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

end Solidity
