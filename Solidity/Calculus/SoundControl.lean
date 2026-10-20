import Solidity.Calculus.SoundLocal

/-!
# Soundness of payments, control flow, declarations

`transferStep`, `sendStep`, `iteStep`, `requireStep`, `assertStep`, the
declarations with an initializer (`Premise.bind`), `revert` and a block,
each `Premise.Sound`.  A `bool` value is a `bool` here, so a split on a
simple condition covers every state (`holds_isBool`), with no stuck case; a
captured `if` condition reads its branches weakened under the captured
local, which run as before by `Semantics/RunWk.lean`'s
`Prog.run_wk` (`Prog.run_wk_up`).

Every hidden binder ranges over a type with a value (`LTy.tdenote_nonempty`):
`memoryLocalDeclInitDrop`'s over the references the heap typing gives the
local's type and an unset local (decision 17'), from which the premise's
`mv = r;` runs as the declaration does, whatever `r` allocates
(`sound_declMemInit`, an alias initializer included).
-/

namespace Solidity
open Solidity (Modality Srt Op0 Op1 Op2 Op3)
open Semantics (Selector)

variable {C : Contract}

open Solidity (Modality)

section Control

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-! ### Payments -/

/-- `transfer_unfold_rightSndArgument`: the amount captured. -/
theorem sound_transferRight (sadr : Simple C Γ .uint) (a : Val C Γ .uint) (x : Var) :
    Premise.Runs m (.transfer (.simple sadr) a)
      (.capture .uint x a (.transfer (.simple sadr.up) (.simple (.local .here)))) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.transfer_pushT σ (t := .val .uint) v
      (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
      (by simp only [Val.evalT, Simple.evalT_up]) (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.transfer _ a σ).map _ = _
  simp only [TRun.transfer, Val.evalT, ok_bind, hh]; rfl

/-- `transfer_unfold_leftFstReceiver`: the receiver captured. -/
theorem sound_transferLeft (r a : Val C Γ .uint) (x : Var) :
    Premise.Runs m (.transfer r a)
      (.capture .uint x r (.transfer (.simple (.local .here)) a.up)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.transfer_pushT σ (t := .val .uint) v
      (.simple (.local .here)) a.up r a (by rw [hv]; rfl) (Val.evalT_up σ (t := .val .uint) v a))
    (fun h hh => ?_)
  show (TRun.transfer r a σ).map _ = _
  simp only [TRun.transfer, hh]; rfl

/-- **A transfer** (`transferStep`). -/
theorem transferStep_sound (k : Nat) (r a : Val C Γ .uint) (q : Premise C Γ Γ)
    (hs : transferStep k m r a = q) : Premise.Runs m (.transfer r a) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact sound_transferBox σ sadr se
      | diamond => cases hs; exact sound_done_false (m := .diamond) σ _
    | _ => cases hs; exact sound_transferRight σ sadr _ _
  | _ => cases hs; exact sound_transferLeft σ _ a _

/-- `send_unfold_rightSndArgument`: the amount captured. -/
theorem sound_sendRight (pv : Idx Γ (.val .bool)) (sadr : Simple C Γ .uint) (a : Val C Γ .uint)
    (x : Var) (full : Bool) :
    Premise.Runs m (.send pv (.simple sadr) a full)
      (.capture .uint x a (.send pv.there (.simple sadr.up) (.simple (.local .here)) full)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.send_pushT σ (t := .val .uint) v pv
      (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
      (by simp only [Val.evalT, Simple.evalT_up]) (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.send pv _ a σ).map _ = _
  simp only [TRun.send, Val.evalT, ok_bind, hh]; rfl

/-- `send_unfold_leftFstReceiver`: the receiver captured. -/
theorem sound_sendLeft (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (x : Var) (full : Bool) :
    Premise.Runs m (.send pv r a full)
      (.capture .uint x r (.send pv.there (.simple (.local .here)) a.up full)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => TRun.send_pushT σ (t := .val .uint) v pv
      (.simple (.local .here)) a.up r a (by rw [hv]; rfl) (Val.evalT_up σ (t := .val .uint) v a))
    (fun h hh => ?_)
  show (TRun.send pv r a σ).map _ = _
  simp only [TRun.send, hh]; rfl

/-- **A send** (`sendStep`). -/
theorem sendStep_sound (k : Nat) (pv : Idx Γ (.val .bool)) (full : Bool) (r a : Val C Γ .uint)
    (q : Premise C Γ Γ) (hs : sendStep k m pv full r a = q) :
    Premise.Runs m (.send pv r a full) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact sound_send (m := .box) σ pv sadr se full _
      | diamond => cases hs; exact sound_send (m := .diamond) σ pv sadr se full _
    | _ => cases hs; exact sound_sendRight σ pv sadr _ _ full
  | _ => cases hs; exact sound_sendLeft σ pv _ a _ full

/-! ### `if`, `require`, `assert` -/

/-- `se = b` holds where `se` is `b`: the condition read on the typed state. -/
theorem holds_isBool (se : Simple C Γ .bool) (b : Bool) :
    holds σ (Fml.isBool se.lower b) ↔ se.evalT σ = b := by
  show holds σ (.eq _ _) ↔ _
  rw [holds_eq, Simple.denote_lowerT σ se]
  show some _ = some b ↔ _
  rw [Option.some.injEq]

/-- A block weakened under one local runs as before, lifted, its locals
popped (`Prog.run_wk` at `up`). -/
theorem Prog.run_wk_up {t : LTy} {Δ : Ctx} (P : Prog C Γ Δ) (w : t.TDenote C σ.H) :
    ((P.wk (Solidity.up (t := t))).2.2.run (σ.push w)).map (Out.drop (P.wk Solidity.up).2.2.ext) =
      pushedT σ w ((P.run σ).map (Out.drop P.ext)) :=
  TWkRel.eq_lifted (TWkRel.drop (Prog.wk_over P Solidity.up) (Prog.run_wk P Solidity.up σ (w, σ.env)))

/-- `ifElseUnfold`: the condition captured, the branches weakened under it. -/
theorem sound_iteCapture {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) (x : Var) :
    Premise.Runs m (.ite c thn els)
      (.capture .bool x c (.ite (.simple (.local .here)) (thn.wk up).2.2 (els.wk up).2.2)) σ := by
  refine Premise.sound_capturePushed σ (fun v hv => ?_) (fun h hh => ?_)
  · show TRun.ite (.simple (.local .here)) _ ((thn.wk up).2.2.runR) _ ((els.wk up).2.2.runR)
      (σ.push v) = pushedT σ v (TRun.ite c thn.ext thn.runR els.ext els.runR σ)
    simp only [TRun.ite, Val.evalT, ok_bind, hv]
    cases v
    · exact Prog.run_wk_up σ els _
    · exact Prog.run_wk_up σ thn _
  · show (TRun.ite c _ _ _ _ σ).map _ = _
    simp only [TRun.ite, hh]; rfl

/-- **An `if`** (`iteStep`). -/
theorem iteStep_sound (k : Nat) {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) (q : Premise C Γ Γ) (hs : iteStep k c thn els = q) :
    Premise.Runs m (.ite c thn els) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.sound_split σ (fun h => ?_) (fun h => ?_) ?_ (fun h J o he => ?_)
      (fun h J o he => ?_)
    · rw [Stmt.runSt_ite_simple, (holds_isBool σ se true).1 h]; rfl
    · rw [Stmt.runSt_ite_simple, (holds_isBool σ se false).1 h]; rfl
    · cases hv : se.evalT σ
      · exact .inr ((holds_isBool σ se false).2 hv)
      · exact .inl ((holds_isBool σ se true).2 hv)
    · have hv := (holds_isBool σ se true).1 h
      cases he with
      | det hf => nomatch hf
      | iteHalt hc => nomatch hc
      | iteThen _ hP => exact ⟨_, hP, rfl⟩
      | iteElse hc _ =>
        have hc : se.evalT σ = false := Except.ok.inj hc
        rw [hv] at hc; nomatch hc
    · have hv := (holds_isBool σ se false).1 h
      cases he with
      | det hf => nomatch hf
      | iteHalt hc => nomatch hc
      | iteThen hc _ =>
        have hc : se.evalT σ = true := Except.ok.inj hc
        rw [hv] at hc; nomatch hc
      | iteElse _ hP => exact ⟨_, hP, rfl⟩
  | _ => cases hs; exact sound_iteCapture σ _ thn els _

/-- `requireConditionCapture`: `⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩`. -/
theorem sound_requireCapture (c : Val C Γ .bool) (x : Var) :
    Premise.Runs m (.require c) (.capture .bool x c (.require (.simple (.local .here)))) σ := by
  refine Premise.sound_capturePushed σ
    (fun v hv => TRun.require_pushT σ (t := .val .bool) v _ c (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.require c σ).map _ = _
  simp only [TRun.require, hh]; rfl

/-- **A `require`** (`requireStep`): `requireSimple`, or the condition
captured. -/
theorem requireStep_sound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : requireStep k c = q) : Premise.Runs m (.require c) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.sound_split σ (fun h => ?_) (fun h => ?_) ?_
      (fun h => ExecS.split_det σ rfl rfl ?_) (fun h => ExecS.split_det σ rfl rfl ?_)
    · show (Prog.runSt σ .nil).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se true).1 h]; rfl
    · show (Prog.runSt σ (.cons .revert .nil)).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se false).1 h]; rfl
    · cases hv : se.evalT σ
      · exact .inr ((holds_isBool σ se false).2 hv)
      · exact .inl ((holds_isBool σ se true).2 hv)
    · show (Prog.runSt σ .nil).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se true).1 h]; rfl
    · show (Prog.runSt σ (.cons .revert .nil)).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (holds_isBool σ se false).1 h]; rfl
  | _ => cases hs; exact sound_requireCapture σ _ _

/-- `assertConditionCapture`: `⟨[ assert(nse); ]⟩ ⇝ ⟨[ bool se = nse; assert(se); ]⟩`. -/
theorem sound_assertCapture (c : Val C Γ .bool) (x : Var) :
    Premise.Runs m (.assert c) (.capture .bool x c (.assert (.simple (.local .here)))) σ := by
  refine Premise.sound_capturePushed σ
    (fun v hv => TRun.assert_pushT σ (t := .val .bool) v _ c (by rw [hv]; rfl)) (fun h hh => ?_)
  show (TRun.assert c σ).map _ = _
  simp only [TRun.assert, hh]; rfl

/-- **An `assert`** (`assertStep`): `assertSimple`, or the condition
captured. -/
theorem assertStep_sound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : assertStep k c = q) : Premise.Runs m (.assert c) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.sound_check σ fun h => ?_
    show (TRun.assert (.simple se) σ).map _ = _
    simp only [TRun.assert, Val.evalT, ok_bind, (holds_isBool σ se true).1 h]; rfl
  | _ => cases hs; exact sound_assertCapture σ _ _

/-! ### Declarations, `revert`, blocks -/

/-- `localValueDeclInitDrop`: `⟨[ T v = e; ]⟩ ⇝ ⟨[ v = e; ]⟩`, `v` bound by
the hidden binder. -/
theorem sound_localValueDeclInitDrop {p : PrimTy} (x : Var) (e : Val C Γ p) :
    Premise.Runs m (.declLocal p x (some e))
      (.bind x (.val p) (.cons (.assignLocal .here e.up) .nil)) σ := by
  refine Premise.sound_bind_all σ fun v => ?_
  rw [Prog.runSt_single, Stmt.runSt_assignLocal, Stmt.runSt_declLocal, Val.evalT_up]
  cases e.evalT σ <;> rfl

/-- `storageLocalDeclInitDrop`: `⟨[ T storage lsv = r; ]⟩ ⇝ ⟨[ lsv = r; ]⟩`. -/
theorem sound_declStorageInit {R : RefTy} (x : Var) (r : ARhs C Γ R) :
    Premise.Runs m (.declStorage R x (some r))
      (.bind x (.alias R) (.cons (.rebind .here r.up) .nil)) σ := by
  refine Premise.sound_bind_all σ fun v => ?_
  rw [Prog.runSt_single]
  show (TRun.rebind .here r.up (σ.push v)).map _ = (TRun.declStorage R (some r) σ).map _
  simp only [TRun.rebind, TRun.declStorage, ARhs.evalT_up]
  cases r.evalT σ <;> rfl

/-- `memoryLocalDeclInitDrop`: `⟨[ T memory mv = r; ]⟩ ⇝ ⟨[ mv = r; ]⟩`.  The
premise's run from any value of `mv`, an unset one among them (decision
17'), is the statement's: `mv = r;` reads nothing of `mv` before it sets it.
An alias `T memory mv = mp;` is the same rule. -/
theorem sound_declMemInit {R : RefTy} (x : Var) (r : MRhs C Γ R)
    (hd : ((some r).isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.Runs m (.declMem R x (some r) hd hm)
      (.bind x (.mem R) (.cons (.rebindMem .here r.up) .nil)) σ := by
  refine Premise.sound_bind_all σ fun v => ?_
  rw [Prog.runSt_single]
  show (TRun.rebindMem .here r.up (σ.push v)).map _ = (TRun.declMem R (some r) hm σ).map _
  simp only [TRun.rebindMem, TRun.declMem, MRhs.evalT_up]
  cases r.evalT σ <;> rfl

/-- A block, its locals popped after it: `⟨[ { body } ]⟩ ⇝ ⟨[ body ]⟩`. -/
theorem sound_block {Γ₂ : Ctx} (body : Prog C Γ Γ₂) :
    Premise.Runs m (.block body) (.unfold body body.ext) σ :=
  Premise.sound_unfold σ (Stmt.runSt_block σ body).symm

/-- `recursiveCallUnfold` (Lean only): a recursive call runs as the call of
its body (`Stmt.run_callRec`). -/
theorem sound_recursiveCallUnfold {ps rs : Ctx} (f : Name) (d : Nat) (args : Args C Γ ps)
    (ret : CallRet Γ rs Γ') (body : Unit → Prog C (rs ++ ps) (rs ++ ps)) :
    Premise.Runs m (.callRec f d args ret body)
      (.unfold (.cons (.call f args ret (body ())) .nil) .refl) σ :=
  Premise.sound_unfold σ (by
    rw [Prog.runSt_single]
    show (Stmt.runSt σ (.call f args ret (body ()))).map _ = Stmt.runSt σ (.call f args ret (body ()))
    cases Stmt.runSt σ (.call f args ret (body ())) <;> rfl)

end Control

end Solidity
