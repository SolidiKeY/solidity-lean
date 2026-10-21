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

/-! ## A contract over the callback runs

`FunContract` over `ExecP` instead of `Prog.run`: from a typed state of the
frame where `requires` holds, every callback run of the body, entered as the
call enters it, keeps the invariant, does not panic and, if it ends, ends
where `ensures` holds.  `RecContractC` is `RecContract` so, proved by the
same induction over the frames (`RecContractC.unroll`). -/

section ContractC

open DeferredSource.Callback (map_cat_refl singleton_iff block_of_execP)

variable {I : Fml C []} {pay : Bool} {Γ Γ' ps rs Γf : Ctx} {m : Modality}

/-- **A function contract with callbacks** (`FunContract`, over `ExecP`). -/
def FunContractC (I : Fml C []) (pay : Bool) (ret : CallRet Γ rs Γ') (body : Prog C (rs ++ ps) Γf)
    (req : Fml C ps) (ens : Fml C (rs ++ (Olds ++ ps))) (m : Modality := .box) : Prop :=
  ∀ σ : State C ps, holds σ req → ∀ o, ExecP (I.stateInv pay) (ret.enterT σ).st body o →
    (o.map (Out.drop body.ext)).after m (fun τ => holds (τ.withOlds rs σ.net σ.storage) ens)

/-- **A recursive function's contract with callbacks** (`RecContract`): the
contract at every call returning `rs`, the body within `μ`, the parameters
unwritten. -/
def RecContractC (I : Fml C []) (pay : Bool) (μ : Mutability) (b : Prog C (rs ++ ps) (rs ++ ps))
    (req : Fml C ps) (ens : Fml C (rs ++ (Olds ++ ps))) (m : Modality := .box) : Prop :=
  (∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'), FunContractC I pay ret b req ens m) ∧
    Prog.within μ b = true ∧ writesRets rs.length b = true

/-- The bottom frame meets every contract: it is exhausted. -/
theorem RecContractC.base (μ : Mutability) (req : Fml C ps) (ens : Fml C (rs ++ (Olds ++ ps)))
    (m : Modality) :
    RecContractC I pay μ (Prog.recBase : Prog C (rs ++ ps) (rs ++ ps)) req ens m := by
  refine ⟨fun ret σ _ o h => ?_, rfl, rfl⟩
  cases h with
  | cons hs _ => cases hs
  | halt hs =>
    cases hs with
    | det _ => exact ⟨by cases m <;> first | trivial | rfl, nofun⟩
  | violated hs => cases hs

/-- **Induction over the unrolling**, with callbacks. -/
theorem RecContractC.unroll {μ : Mutability} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    {step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps)}
    (hs : ∀ n (t : Unit → Prog C (rs ++ ps) (rs ++ ps)),
      RecContractC I pay μ (t ()) req ens m → RecContractC I pay μ (step n t) req ens m)
    (d : Nat) : RecContractC I pay μ (recUnroll Prog.recBase step d) req ens m :=
  recUnroll_induct (fun b => RecContractC I pay μ b req ens m) (RecContractC.base μ req ens m) hs d

/-- A contract at a call that returns nothing is one at every such call. -/
theorem FunContractC.forall_none {Γf : Ctx} {b : Prog C ([] ++ ps) Γf} {req : Fml C ps}
    {ens : Fml C ([] ++ (Olds ++ ps))}
    (h : FunContractC (Γ := []) I pay CallRet.none b req ens m) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ [] Γ'), FunContractC I pay ret b req ens m := by
  intro Γ Γ' ret
  cases ret with
  | none => exact h
  | rets bs => cases bs; exact h

/-- A contract at a call that returns one value is one at every such call. -/
theorem FunContractC.forall_val {Γf : Ctx} {p : PrimTy} {b : Prog C ([.val p] ++ ps) Γf}
    {req : Fml C ps} {ens : Fml C ([.val p] ++ (Olds ++ ps))}
    (h : FunContractC (Γ := []) I pay (CallRet.val p (.user "r") Option.none) b req ens m) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ [.val p] Γ'), FunContractC I pay ret b req ens m := by
  intro Γ Γ' ret
  cases ret with
  | val => exact h
  | rets bs =>
    cases bs with
    | snoc bs q x => cases bs; exact h

/-- A contract at a call that returns several values is one at every such
call. -/
theorem FunContractC.forall_rets {Γf : Ctx} {b : Prog C (rs ++ ps) Γf} {req : Fml C ps}
    {ens : Fml C (rs ++ (Olds ++ ps))} (bs : Binders rs) (h2 : 2 ≤ rs.length)
    (h : FunContractC (Γ := []) I pay (CallRet.rets bs) b req ens m) :
    ∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'), FunContractC I pay ret b req ens m := by
  intro Γ Γ' ret
  cases ret with
  | none => simp at h2
  | val => simp at h2
  | mem => simp at h2
  | storage => simp at h2
  | rets bs' =>
    intro σ hσ
    have := h σ hσ
    simp only [CallRet.enterT] at this ⊢
    rw [Binders.defaultsT_eq bs bs'] at this
    exact this

/-- What a formula says past `snapOld` with callbacks, it says of the
snapshots. -/
theorem holdsC_snapOld {Δ : Ctx} {X : Fml C (Olds ++ Δ)} {σ : State C Δ}
    (h : holdsC I pay σ (.upd .box snapOld X)) : holdsC I pay σ.snap X := by
  refine Upd.afterT.of_lands (U := snapOld) h (g := σ.globG) ⟨rfl, rfl, fun i => ?_⟩
  cases i with
  | here => rfl
  | there i =>
    cases i with
    | here => rfl
    | there j => rfl

/-- **The return variables declared, with callbacks**: the rest runs from
the frame the call enters (`CallRet.enterT`). -/
theorem CallRet.execP_declsThen {J : StateInv C} {Δ : Ctx} (ret : CallRet Γ rs Γ')
    (rest : Prog C (rs ++ ps) Δ) (σ : State C ps) {u : COut C (ret.enterT σ).st.H Δ}
    (h : ExecP J (ret.enterT σ).st rest u) :
    ExecP J σ (ret.declsThen rest) (u.map (Out.cat (ret.enterT σ))) := by
  cases ret with
  | none => simpa only [CallRet.enterT, map_cat_refl] using h
  | val p r res =>
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ) (s := .declLocal p r Option.none) rfl
      (Stmt.runSt_declLocal_none p r σ)
    exact ExecP.cons hd h
  | rets bs =>
    have h' : ExecP J σ (bs.declsThen rest) u := Binders.execP_declsThen bs rest σ h
    simpa only [CallRet.enterT, map_cat_refl] using h'
  | mem R r hd hm =>
    obtain ⟨_, hd'⟩ := ExecS.det_ok (J := J) (σ := σ) (s := .declMem R r Option.none hd hm) rfl
      (Stmt.runSt_declMem_none R r hd hm σ)
    exact ExecP.cons hd' h
  | storage R r =>
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := J) (σ := σ) (s := .declStorage R r Option.none) rfl
      (Stmt.runSt_declStorage_none R r σ)
    exact ExecP.cons hd h

/-- A callback run from a state equal to another, of the same heap. -/
theorem ExecP.transport' {J : StateInv C} {Δ Δ' : Ctx} {P : Prog C Δ Δ'} {X Y : State C Δ}
    (e : X = Y) (hH : Y.H = X.H) {u : COut C X.H Δ'} (h : ExecP J X P u) :
    ExecP J Y P (hH ▸ u) := by
  subst e
  exact h

/-- A frame's outcome lifted under the snapshots, read past them
(`State.lift_thinOlds`). -/
theorem Out.lift_thinOlds_st {H : HTy} (n : Ledger) (s : Storage C) (A : TEnv C H rs)
    (B : TEnv C H ps) (y : Out C H (rs ++ ps)) :
    (Out.lift (thinOlds rs ps) (TEnv.append rs A (TEnv.olds n s B)) y).st =
      y.st.withOlds rs n s := by
  simp only [Out.lift]
  rw [TEnv.append_wk]
  exact State.lift_thinOlds _ _ _ _ _

/-- What the obligation's run says of its frame's outcome, lifted under the
snapshots, the contract says of the outcome. -/
theorem after_of_thenF_lift {J : StateInv C} {H₀ : HTy} {Δ : Ctx} (E : Out C H₀ Δ)
    {n : Ledger} {s : Storage C} {A : TEnv C E.st.H rs} {B : TEnv C E.st.H ps}
    {ens : Fml C (rs ++ (Olds ++ ps))} (hens : ens.callsBack pay = false)
    (w : COut C E.st.H (rs ++ ps))
    (h : ((w.map (Out.lift (thinOlds rs ps) (TEnv.append rs A (TEnv.olds n s B)))).map
      (Out.cat E)).thenF J .nil m (fun x => holdsC I pay x ens)) :
    w.after m (fun τ => holds (τ.withOlds rs n s) ens) := by
  cases w with
  | ok y =>
    have h' := h _ .nil
    change holdsC I pay (Out.lift (thinOlds rs ps) (TEnv.append rs A (TEnv.olds n s B)) y).st ens
      at h'
    rw [Out.lift_thinOlds_st] at h'
    exact (holdsC_iff_holds ens hens _).1 h'
  | halt e => exact h
  | violated => exact h

/-- **A contract from its obligation, read with callbacks**
(`FunContract.ofValid`): the body's callback runs are those of the
obligation's block, under the snapshots (`Prog.exec_wk`). -/
theorem FunContractC.ofHoldsC {ret : CallRet Γ rs Γ'} {body : Prog C (rs ++ ps) Γf}
    {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))} (hreq : req.callsBack pay = false)
    (hens : ens.callsBack pay = false)
    (h : ∀ σ : State C ps, holdsC I pay σ (FunContract.obligation ret body req ens m)) :
    FunContractC I pay ret body req ens m := by
  intro σ hr o hp
  have h1 : holdsC I pay σ (.upd .box snapOld (.modal m
      (ret.declsThen (.cons (.block (body.wk (thinOlds rs ps)).2.2) .nil)) .nil ens)) :=
    h σ ((holdsC_iff_holds req hreq σ).2 hr)
  have h2 := holdsC_snapOld h1
  obtain ⟨o', hw, hrel⟩ := Prog.exec_wk (I.stateInv pay) body (thinOlds rs ps) (ret.enterT σ).st
    (TEnv.append rs (TEnv.take rs (ret.enterT σ).st.env)
      (TEnv.olds σ.net σ.storage (TEnv.drop (Ext.append ps rs) (ret.enterT σ).st.env))) hp
  have eX := (State.lift_thinOlds (ret.enterT σ).st (TEnv.take rs (ret.enterT σ).st.env) σ.net
    σ.storage (TEnv.drop (Ext.append ps rs) (ret.enterT σ).st.env)).trans
      (CallRet.enterT_snap ret σ).symm
  have hb := singleton_iff.mpr (block_of_execP hw)
  have hl := (CallbackWk.CWkRel.drop (Prog.wk_over body (thinOlds rs ps)) hrel).eq_lifted
  cases ret
  all_goals
    have hb' := ExecP.transport' eX rfl hb
    have h3 := h2 _ (CallRet.execP_declsThen _ _ σ.snap hb')
    rw [hl] at h3
    exact after_of_thenF_lift _ hens _ h3

end ContractC

/-! ## The rule, with callbacks

`holds_callContract`'s argument over `holdsC`: "pre" and "post" read with
callbacks, the call's runs by the contract (`FunContractC`) and their frame
(`ExecP.frame`), the rest from what "post" says past the call. -/

section RuleC

variable {I : Fml C []} {pay : Bool} {Γ ps rs Γ' Γf Γ₂ Γ₀ : Ctx} {m : Modality}

/-- A first-order formula weakened hands control to nobody. -/
theorem Fml.callsBack_wkFO : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (φ : Fml C Γ) →
    {φ' : Fml C Δ} → φ.wkFO h = some φ' → φ'.callsBack pay = false
  | _, _, _, .tt, _, e => by cases e; rfl
  | _, _, _, .eq _ _, _, e => by cases e; rfl
  | _, _, _, .wellFormed _, _, e => by cases e; rfl
  | _, _, h, .not φ, _, e => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO_not, hφ, Option.map_none, reduceCtorEq] at e
    | some φ' =>
      simp only [Fml.wkFO_not, hφ, Option.map_some, Option.some.injEq] at e
      cases e
      have := Fml.callsBack_wkFO h φ hφ
      exact this
  | _, _, h, .and φ ψ, _, e => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO_and, hφ, Option.bind_none, Option.bind_eq_bind, reduceCtorEq] at e
    | some φ' =>
      cases hψ : ψ.wkFO h with
      | none =>
        simp only [Fml.wkFO_and, hφ, hψ, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
          reduceCtorEq] at e
      | some ψ' =>
        simp only [Fml.wkFO_and, hφ, hψ, Option.bind_some, Option.bind_eq_bind, Option.pure_def,
          Option.some.injEq] at e
        cases e
        show (φ'.callsBack pay || ψ'.callsBack pay) = false
        rw [Fml.callsBack_wkFO h φ hφ, Fml.callsBack_wkFO h ψ hψ]; rfl
  | _, _, h, .imp φ ψ, _, e => by
    cases hφ : φ.wkFO h with
    | none => simp only [Fml.wkFO_imp, hφ, Option.bind_none, Option.bind_eq_bind, reduceCtorEq] at e
    | some φ' =>
      cases hψ : ψ.wkFO h with
      | none =>
        simp only [Fml.wkFO_imp, hφ, hψ, Option.bind_some, Option.bind_none, Option.bind_eq_bind,
          reduceCtorEq] at e
      | some ψ' =>
        simp only [Fml.wkFO_imp, hφ, hψ, Option.bind_some, Option.bind_eq_bind, Option.pure_def,
          Option.some.injEq] at e
        cases e
        show (φ'.callsBack pay || ψ'.callsBack pay) = false
        rw [Fml.callsBack_wkFO h φ hφ, Fml.callsBack_wkFO h ψ hψ]; rfl
  | _, _, h, .all x p φ, _, e => by
    cases hφ : φ.wkFO h.keep with
    | none => simp only [Fml.wkFO_all, hφ, Option.map_none, reduceCtorEq] at e
    | some φ' =>
      simp only [Fml.wkFO_all, hφ, Option.map_some, Option.some.injEq] at e
      cases e
      have := Fml.callsBack_wkFO h.keep φ hφ
      exact this
  | _, _, _, .upd .., _, e | _, _, _, .modal .., _, e | _, _, _, .havoc _, _, e
  | _, _, _, .bind .., _, e | _, _, _, .anon .., _, e => nomatch e

theorem Fml.callsBack_wkD {Δ : Ctx} (h : Thin Γ Δ) (φ : Fml C Γ) :
    (φ.wkD h).callsBack pay = false := by
  unfold Fml.wkD
  cases e : φ.wkFO h with
  | none => rfl
  | some φ' => exact Fml.callsBack_wkFO h φ e

/-- What a weakened `ensures` says, with callbacks, it says on the thinned
state. -/
theorem holdsC_wkD {Δ : Ctx} (h : Thin Γ Δ) (φ : Fml C Γ) (σ : State C Δ)
    (hφ : holds (σ.thin h) φ) : holdsC I pay σ (φ.wkD h) :=
  (holdsC_iff_holds _ (Fml.callsBack_wkD h φ) σ).2 (holds_wkD h φ σ hφ)

/-- The arguments read, then `X` on the parameters declared, with callbacks. -/
theorem holdsC_declsThen {args : Args C Γ ps} {X : Fml C (ps ++ Γ)} {σ : State C Γ}
    (h : holdsC I pay σ (.modal m (args.declsThen .nil) .nil X)) :
    (∀ e, args.evalT σ = .error e → m.onTHalt e ∧ e ≠ .panic) ∧
      ∀ a, args.evalT σ = .ok a → holdsC I pay (σ.withEnv (TEnv.append ps a σ.env)) X := by
  refine ⟨fun e he => h _ (Args.execP_declsThen_halt args _ σ he), fun a ha => ?_⟩
  exact h _ (Args.execP_declsThen args _ σ a ha .nil) _ .nil

/-- "pre", with callbacks: the arguments read, `requires` of the
parameters. -/
theorem holdsC_callPre {args : Args C Γ ps} {req : Fml C ps} {σ : State C Γ}
    (h : holdsC I pay σ (Fml.callPre args req m)) :
    (∀ e, args.evalT σ = .error e → m.onTHalt e ∧ e ≠ .panic) ∧
      ∀ a, args.evalT σ = .ok a → holdsC I pay (σ.withEnv a) req := by
  refine ⟨fun e he => h _ (Args.execP_declsThen_halt args _ σ he), fun a ha => ?_⟩
  have h1 : holdsC I pay ((σ.withEnv (TEnv.append ps a σ.env)).thin (Thin.atop ps Γ)) req :=
    h _ (Args.execP_declsThen args _ σ a ha .nil) _ (.drop .nil)
  rwa [show (σ.withEnv (TEnv.append ps a σ.env)).thin (Thin.atop ps Γ) = σ.withEnv a by
    simp only [State.thin, State.withEnv, TEnv.thin_atop_append]] at h1

/-- "post", opened with callbacks. -/
theorem holdsC_callPost {μ : Mutability} {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {ens : Fml C (rs ++ (Olds ++ ps))} {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {σ : State C Γ} (h : holdsC I pay σ (Fml.callPost μ args ret ens ω κ φ m))
    (a : TEnv C σ.H ps) (ha : args.evalT σ = .ok a) (st : Storage C) (nt : Ledger)
    (hk : μ ≠ .nonpayable → st = σ.storage ∧ nt = σ.net) :
    holdsC I pay ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st nt)
      (Fml.callResult ret ens ω κ φ m) := by
  have hX := holdsC_snapOld ((holdsC_declsThen h).2 a ha)
  cases μ with
  | nonpayable => exact hX st nt
  | pure =>
    obtain ⟨rfl, rfl⟩ := hk (by decide)
    exact hX
  | view =>
    obtain ⟨rfl, rfl⟩ := hk (by decide)
    exact hX

/-- Frames run from a state equal to another, of the same heap. -/
theorem ExecF.transport' {J : StateInv C} {Δ : Ctx} {κ : Frames C Δ Γ₀} {X Y : State C Δ}
    (e : X = Y) (hH : Y.H = X.H) {u : COut C X.H Γ₀} (h : ExecF J X κ u) :
    ExecF J Y κ (hH ▸ u) := by
  subst e
  exact h

/-- **A recursive call by its contract, with callbacks**, up to what it
leaves (`holds_call_of`): the arguments read, the body entered and ended
where `ensures` holds and within its frame, the rest after the call leaves. -/
theorem holdsC_callRec_of {μ : Mutability} {f : Name} {d : Nat} {args : Args C Γ ps}
    {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)} {ω : Prog C Γ' Γ₂}
    {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (hc : FunContractC I pay ret (body ()) req ens m) (hμ : Prog.within μ (body ()) = true)
    (hreq : req.callsBack pay = false) {σ : State C Γ}
    (hpre : holdsC I pay σ (Fml.callPre args req m))
    (hpost : holdsC I pay σ (Fml.callPost μ args ret ens ω κ φ m))
    (k : ∀ (a : TEnv C σ.H ps), args.evalT σ = .ok a →
      ∀ (o : Out C (ret.enterT (σ.withEnv a)).st.H (rs ++ ps)),
      holds (State.withOlds rs (σ.withEnv a).net (σ.withEnv a).storage
        (State.drop (body ()).ext o.st)) ens →
      TGFrame μ (ret.enterT (σ.withEnv a)).st o.st →
      TLocAgree 0 (Prog.writesAt 0 (body ())) (ret.enterT (σ.withEnv a)).st.env
        (TEnv.drop (body ()).ext o.st.env) →
      holdsC I pay ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc o.st.storage o.st.net)
        (Fml.callResult ret ens ω κ φ m) →
      (COut.ok (TRun.callLeave ret (body ()).ext σ (ret.enterT (σ.withEnv a)) o)).thenF
        (I.stateInv pay) (.seq ω κ) m (holdsC I pay · φ)) :
    holdsC I pay σ (.modal m (.cons (.callRec f d args ret body) ω) κ φ) := by
  refine holdsC_cons fun o₁ he => ?_
  have he' : ExecS (I.stateInv pay) σ (.call f args ret (body ())) o₁ := by
    cases he with
    | det h => exact nomatch h
    | callRec h => exact h
  rcases ExecS.call_inv he' with ⟨e, ha, rfl⟩ | ⟨a, o', ha, hp, rfl⟩
  · exact (holdsC_callPre hpre).1 e ha
  · have hr := (holdsC_iff_holds req hreq _).1 ((holdsC_callPre hpre).2 a ha)
    have hct := hc (σ.withEnv a) hr o' hp
    have hfr := ExecP.frame hp hμ 0
    cases o' with
    | ok x =>
      obtain ⟨hg, hag⟩ := hfr x rfl
      refine k a ha x hct hg hag (holdsC_callPost hpost a ha x.st.storage x.st.net fun hn => ?_)
      have hk := hg.keeps hn
      cases ret <;> exact hk
    | halt e => exact hct
    | violated => exact hct.elim

/-- The continuation of a call with no result, with callbacks
(`holds_callNone`). -/
theorem holdsC_callNone_k {μ : Mutability} {body : Prog C ([] ++ ps) Γf}
    {ω : Prog C Γ Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {ens : Fml C ([] ++ (Olds ++ ps))}
    (hw : writesRets 0 body = true) {σ : State C Γ} (a : TEnv C σ.H ps)
    (o : Out C ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)).st.H Γf)
    (hens : holds (State.withOlds [] (σ.withEnv a).net (σ.withEnv a).storage
      (State.drop body.ext o.st)) ens)
    (hg : TGFrame μ ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)).st o.st)
    (hag : TLocAgree 0 (Prog.writesAt 0 body) ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)).st.env
      (TEnv.drop body.ext o.st.env))
    (hX : holdsC I pay ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc o.st.storage o.st.net)
      (Fml.callResult .none ens ω κ φ m)) :
    (COut.ok (TRun.callLeave .none body.ext σ ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a)) o)).thenF
      (I.stateInv pay) (.seq ω κ) m (holdsC I pay · φ) := by
  obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
  obtain ⟨hH, hheap, hsb, htx, -⟩ := hg
  dsimp only [CallRet.enterT, State.withEnv] at hH hheap hsb htx hag hens
  dsimp only at hX
  subst hH
  cases hheap
  have hps : TEnv.drop body.ext env = a :=
    TLocAgree.drop_eq (ρ := []) hag hw
  have hens' : holdsC I pay ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net)
      (ens.wkD (Thin.atop (Olds ++ ps) Γ)) := by
    apply holdsC_wkD
    have hst : (State.drop body.ext ⟨st, σ.H, σ.heap, env, net, sb, tx⟩).withOlds []
        σ.net σ.storage = State.thin (Thin.atop (Olds ++ ps) Γ)
          ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net) := by
      refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
      show TEnv.olds σ.net σ.storage (TEnv.drop body.ext env) =
        TEnv.olds σ.net σ.storage (TEnv.thin (Thin.atop ps Γ) (TEnv.append ps a σ.env))
      rw [TEnv.thin_atop_append, hps]
    exact hst ▸ hens
  have hM := hX hens'
  have hT : State.drop (Ext.append Γ (Olds ++ ps))
      ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net) =
      (TRun.callLeave .none body.ext σ ((CallRet.none (Γ := Γ)).enterT (σ.withEnv a))
        ⟨⟨st, σ.H, σ.heap, env, net, sb, tx⟩, ext⟩).st := by
    simp only [TRun.callLeave]
    rw [TEnv.wk_self]
    exact State.ext' rfl rfl HEq.rfl (heq_of_eq (TEnv.drop_append ps a σ.env)) rfl hsb.symm
      htx.symm
  intro o'' hf
  exact hM _ .nil o'' (.pop (ExecF.transport' hT.symm rfl hf))

/-- The continuation of a call with one result, with callbacks
(`holds_callVal`). -/
theorem holdsC_callVal_k {μ : Mutability} {p : PrimTy} {r : Var}
    {res : Option (Idx Γ (.val p))} {body : Prog C ([.val p] ++ ps) Γf} {ω : Prog C Γ Γ₂}
    {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {ens : Fml C ([.val p] ++ (Olds ++ ps))}
    (hw : writesRets 1 body = true) {σ : State C Γ} (a : TEnv C σ.H ps)
    (o : Out C ((CallRet.val p r res).enterT (σ.withEnv a)).st.H Γf)
    (hens : holds (State.withOlds [.val p] (σ.withEnv a).net (σ.withEnv a).storage
      (State.drop body.ext o.st)) ens)
    (hg : TGFrame μ ((CallRet.val p r res).enterT (σ.withEnv a)).st o.st)
    (hag : TLocAgree 0 (Prog.writesAt 0 body) ((CallRet.val p r res).enterT (σ.withEnv a)).st.env
      (TEnv.drop body.ext o.st.env))
    (hX : holdsC I pay ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc o.st.storage o.st.net)
      (Fml.callResult (.val p r res) ens ω κ φ m)) :
    (COut.ok (TRun.callLeave (.val p r res) body.ext σ
      ((CallRet.val p r res).enterT (σ.withEnv a)) o)).thenF
      (I.stateInv pay) (.seq ω κ) m (holdsC I pay · φ) := by
  obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
  obtain ⟨hH, hheap, hsb, htx, -⟩ := hg
  dsimp only [CallRet.enterT, State.push, State.withEnv] at hH hheap hsb htx hag hens
  dsimp only at hX
  subst hH
  cases hheap
  have hps : (TEnv.drop body.ext env).2 = a :=
    TLocAgree.drop_eq (ρ := [.val p]) (e := (PrimTy.dflt p, a)) hag hw
  have hens' : holdsC I pay (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push
      (t := .val p) (TEnv.drop body.ext env).1)
      (ens.wkD (Thin.atop (.val p :: (Olds ++ ps)) Γ)) := by
    apply holdsC_wkD
    have hst : (State.drop body.ext ⟨st, σ.H, σ.heap, env, net, sb, tx⟩).withOlds [.val p]
        σ.net σ.storage = State.thin (Thin.atop (.val p :: (Olds ++ ps)) Γ)
          (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
            (TEnv.drop body.ext env).1) := by
      refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
      show ((TEnv.drop body.ext env).1, TEnv.olds σ.net σ.storage (TEnv.drop body.ext env).2) =
        ((TEnv.drop body.ext env).1, TEnv.olds σ.net σ.storage
          (TEnv.thin (Thin.atop ps Γ) (TEnv.append ps a σ.env)))
      rw [TEnv.thin_atop_append, hps]
    exact hst ▸ hens
  have hM := hX (TEnv.drop body.ext env).1 hens'
  intro o'' hf
  cases res with
  | none =>
    have hT : State.drop (Ext.append Γ (.val p :: (Olds ++ ps)))
        (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
          (TEnv.drop body.ext env).1) =
        (TRun.callLeave (.val p r Option.none) body.ext σ
          ((CallRet.val p r Option.none).enterT (σ.withEnv a))
          ⟨⟨st, σ.H, σ.heap, env, net, sb, tx⟩, ext⟩).st := by
      simp only [TRun.callLeave]
      rw [TEnv.wk_self]
      exact State.ext' rfl rfl HEq.rfl (heq_of_eq (TEnv.drop_append ps a σ.env)) rfl hsb.symm
        htx.symm
    exact hM _ .nil o'' (.pop (ExecF.transport' hT.symm rfl hf))
  | some j =>
    have hT : State.drop (Ext.append Γ (.val p :: (Olds ++ ps)))
        ((((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
          (TEnv.drop body.ext env).1).setLocal (j.under (Olds ++ ps)).there
            (TEnv.drop body.ext env).1) =
        (TRun.callLeave (.val p r (some j)) body.ext σ
          ((CallRet.val p r (some j)).enterT (σ.withEnv a))
          ⟨⟨st, σ.H, σ.heap, env, net, sb, tx⟩, ext⟩).st := by
      simp only [TRun.callLeave]
      rw [TEnv.wk_self]
      refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb.symm htx.symm
      show TEnv.drop (Ext.append Γ (.val p :: (Olds ++ ps)))
        (TEnv.set (j.under (.val p :: (Olds ++ ps))) _ _) = _
      rw [TEnv.drop_set_under]
      show TEnv.set j _ (TEnv.drop (Ext.append Γ ps) (TEnv.append ps a σ.env)) = _
      rw [TEnv.drop_append]
      rfl
    obtain ⟨_, hd⟩ := ExecS.det_ok (J := I.stateInv pay)
      (σ := ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).push (t := .val p)
        (TEnv.drop body.ext env).1)
      (s := .assignLocal (j.under (Olds ++ ps)).there (.simple (.local .here))) rfl rfl
    exact hM _ (ExecP.cons hd .nil) o'' (.pop (ExecF.transport' hT.symm rfl hf))

/-- The continuation of a call of several results, with callbacks
(`holds_callRets`). -/
theorem holdsC_callRets_k {μ : Mutability} {bs : Binders rs}
    {body : Prog C (rs ++ ps) Γf} {ω : Prog C (rs ++ Γ) Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {ens : Fml C (rs ++ (Olds ++ ps))} (hw : writesRets rs.length body = true) {σ : State C Γ}
    (a : TEnv C σ.H ps) (o : Out C ((CallRet.rets (Γ := Γ) bs).enterT (σ.withEnv a)).st.H Γf)
    (hens : holds (State.withOlds rs (σ.withEnv a).net (σ.withEnv a).storage
      (State.drop body.ext o.st)) ens)
    (hg : TGFrame μ ((CallRet.rets (Γ := Γ) bs).enterT (σ.withEnv a)).st o.st)
    (hag : TLocAgree 0 (Prog.writesAt 0 body)
      ((CallRet.rets (Γ := Γ) bs).enterT (σ.withEnv a)).st.env (TEnv.drop body.ext o.st.env))
    (hX : holdsC I pay ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc o.st.storage o.st.net)
      (Fml.callResult (.rets bs) ens ω κ φ m)) :
    (COut.ok (TRun.callLeave (.rets bs) body.ext σ
      ((CallRet.rets (Γ := Γ) bs).enterT (σ.withEnv a)) o)).thenF
      (I.stateInv pay) (.seq ω κ) m (holdsC I pay · φ) := by
  obtain ⟨⟨st, H', heap, env, net, sb, tx⟩, ext⟩ := o
  obtain ⟨hH, hheap, hsb, htx, -⟩ := hg
  dsimp only [CallRet.enterT, State.withEnv] at hH hheap hsb htx hag hens
  dsimp only at hX
  subst hH
  cases hheap
  have hps : TEnv.drop (Ext.append ps rs) (TEnv.drop body.ext env) = a := by
    rw [TLocAgree.drop_eq hag hw, TEnv.drop_append]
  have hX' := holdsC_binders_all bs _ (.imp (ens.wkD (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ)))
    (.modal m .nil (.drop (Thin.keepAll rs (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
      (.seq ω κ)) φ)) (TEnv.take rs (TEnv.drop body.ext env)) hX
  have hens' : holdsC I pay (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).withEnv
      (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
        ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).env))
      (ens.wkD (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ))) := by
    apply holdsC_wkD
    have hst : (State.drop body.ext ⟨st, σ.H, σ.heap, env, net, sb, tx⟩).withOlds rs
        σ.net σ.storage = State.thin (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ))
          (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).withEnv
            (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
              ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).env)) := by
      refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb htx
      show TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
          (TEnv.olds σ.net σ.storage (TEnv.drop (Ext.append ps rs) (TEnv.drop body.ext env))) =
        TEnv.thin (Thin.keepAll rs (Thin.atop (Olds ++ ps) Γ))
          (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
            (TEnv.olds σ.net σ.storage (TEnv.append ps a σ.env)))
      rw [TEnv.thin_keepAll, hps]
      show _ = TEnv.append rs _ (TEnv.olds σ.net σ.storage (TEnv.thin (Thin.atop ps Γ)
        (TEnv.append ps a σ.env)))
      rw [TEnv.thin_atop_append]
    exact hst ▸ hens
  have hM := hX' hens'
  have hT : State.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
      (((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).withEnv
        (TEnv.append rs (TEnv.take rs (TEnv.drop body.ext env))
          ((σ.withEnv (TEnv.append ps a σ.env)).snap.havoc st net).env)) =
      (TRun.callLeave (.rets bs) body.ext σ ((CallRet.rets (Γ := Γ) bs).enterT (σ.withEnv a))
        ⟨⟨st, σ.H, σ.heap, env, net, sb, tx⟩, ext⟩).st := by
    simp only [TRun.callLeave]
    rw [TEnv.wk_self]
    refine State.ext' rfl rfl HEq.rfl (heq_of_eq ?_) rfl hsb.symm htx.symm
    show TEnv.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ (Olds ++ ps))))
        (TEnv.append rs _ (TEnv.olds σ.net σ.storage (TEnv.append ps a σ.env))) =
          TEnv.append rs _ σ.env
    rw [TEnv.thin_keepAll, TEnv.thin_ofExt]
    show TEnv.append rs _ (TEnv.drop (Ext.append Γ ps) (TEnv.append ps a σ.env)) = _
    rw [TEnv.drop_append]
  intro o'' hf
  exact hM _ .nil o'' (.drop (ExecF.transport' hT.symm rfl hf))

/-- A call whose result is values: none, one, or a tuple's (the returns a
recursive function's contract reads, `CallRet.nVals`). -/
def CallRet.isValues {Γ rs Γ' : Ctx} : CallRet Γ rs Γ' → Bool
  | .none | .val .. | .rets _ => true
  | .mem .. | .storage .. => false

/-- **A recursive call by its contract is sound with callbacks**
(`holds_callContract`, the callee's runs with callbacks). -/
theorem holdsC_callRecContract {μ : Mutability} {f : Name} {d : Nat} {args : Args C Γ ps}
    {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)} {ω : Prog C Γ' Γ₂}
    {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (hc : RecContractC I pay μ (body ()) req ens m) (hreq : req.callsBack pay = false)
    (hk : ret.isValues = true) {σ : State C Γ}
    (hpre : holdsC I pay σ (Fml.callPre args req m))
    (hpost : holdsC I pay σ (Fml.callPost μ args ret ens ω κ φ m)) :
    holdsC I pay σ (.modal m (.cons (.callRec f d args ret body) ω) κ φ) := by
  cases ret with
  | none =>
    exact holdsC_callRec_of (hc.1 _) hc.2.1 hreq hpre hpost
      fun a _ o h₁ h₂ h₃ h₄ => holdsC_callNone_k hc.2.2 a o h₁ h₂ h₃ h₄
  | val =>
    exact holdsC_callRec_of (hc.1 _) hc.2.1 hreq hpre hpost
      fun a _ o h₁ h₂ h₃ h₄ => holdsC_callVal_k hc.2.2 a o h₁ h₂ h₃ h₄
  | rets =>
    exact holdsC_callRec_of (hc.1 _) hc.2.1 hreq hpre hpost
      fun a _ o h₁ h₂ h₃ h₄ => holdsC_callRets_k hc.2.2 a o h₁ h₂ h₃ h₄
  | mem => exact nomatch hk
  | storage => exact nomatch hk

/-- **`useContract` at a recursive call, with callbacks** (Lean,
`ProvesC.recCall`): the goals "pre" and "post", the contract over the
callback runs proved by induction over the frames (`RecContractC.unroll`). -/
theorem ProvesC.recContract {Δ₀ : Ctx} {H : Hyps C Δ₀ Γ} {μ : Mutability} {f : Name} {d : Nat}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'} {body : Unit → Prog C (rs ++ ps) (rs ++ ps)}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (hc : RecContractC I pay μ (body ()) req ens m) (hreq : req.callsBack pay = false)
    (hk : ret.isValues = true)
    («pre» : ProvesC I pay Δ₀ H (Fml.callPre args req m))
    («post» : ProvesC I pay Δ₀ H (Fml.callPost μ args ret ens ω κ φ m)) :
    ProvesC I pay Δ₀ H (.modal m (.cons (.callRec f d args ret body) ω) κ φ) :=
  .recCall [Fml.callPre args req m, Fml.callPost μ args ret ens ω κ φ m]
    (fun τ h => Hyps.wrapC_and H (fun _ a b => holdsC_callRecContract hc hreq hk a b) τ
      (h _ List.mem_cons_self) (h _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (fun ψ hψ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
      rcases hψ with rfl | rfl
      · exact «pre»
      · exact «post»)

theorem holdsC_allCtx : (ps : Ctx) → (ns : List Var) → {φ : Fml C ps} →
    (∀ σ : State C [], holdsC I pay σ (Fml.allCtx ps ns φ)) → ∀ σ : State C ps, holdsC I pay σ φ
  | [], _, _, h, σ => h σ
  | .val p :: ps, ns, φ, h, σ =>
    holdsC_allCtx ps ns.tail (φ := .all (ns.headD (.user "p")) p φ) h (σ.withEnv σ.env.2) σ.env.1
  | .alias R :: ps, ns, φ, h, σ =>
    holdsC_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) (.alias R) φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .mem R :: ps, ns, φ, h, σ =>
    holdsC_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) (.mem R) φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .old :: ps, ns, φ, h, σ =>
    holdsC_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) .old φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .oldNet :: ps, ns, φ, h, σ =>
    holdsC_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) .oldNet φ) h
      (σ.withEnv σ.env.2) σ.env.1
  | .kint :: ps, ns, φ, h, σ =>
    holdsC_allCtx ps ns.tail (φ := .bind .box (ns.headD (.user "p")) .kint φ) h
      (σ.withEnv σ.env.2) σ.env.1

/-- **A contract with callbacks from a derivation of its obligation**
(`FunContract.ofValidCtx`), the frame's parameters bound (`Fml.allCtx`). -/
theorem FunContractC.ofProvesC {Γ Γ' : Ctx} (ns : List Var) {ret : CallRet Γ rs Γ'}
    {body : Prog C (rs ++ ps) Γf} {req : Fml C ps} {ens : Fml C (rs ++ (Olds ++ ps))}
    (hI : I.FO = true) (hreq : req.callsBack pay = false) (hens : ens.callsBack pay = false)
    (h : ProvesC I pay [] .nil (Fml.allCtx ps ns (FunContract.obligation ret body req ens m))) :
    FunContractC I pay ret body req ens m :=
  FunContractC.ofHoldsC hreq hens
    (holdsC_allCtx ps ns (ProvesC.sound_of hI (Fml.hasTransfer_of_FO I hI) h))

end RuleC

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
