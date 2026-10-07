import Solidity.Calculus.Core.SoundLocal

/-!
# Soundness of the arms on payments, control flow and declarations

`Calculus/Core/Arms.lean`'s `transferStep`, `sendStep`, `iteStep`,
`requireStep`, `assertStep`, and the declarations with an initializer, each
sound in the shape of `Calculus/Core/SoundKit.lean`; `revert` and blocks are
`Calculus/Core/Logic.lean`'s `Stmt.step_sound_revert` and
`Stmt.step_sound_block`.  A split
on a simple condition that reads as no `bool` is stuck
(`Premise.Sound.splitStuck`); a captured `if` condition is sound when its
branches, weakened under the captured local, run as before (`WkRuns`, the
run of `Prog.wk up`; the call arms of `Calculus/Core/Blocks.lean` prove the
run of a weakened block).
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

section Control

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-! ### Payments -/

/-- `transfer_unfold_rightSndArgument`: the amount captured. -/
theorem sound_transferRight (sadr : Simple C Γ .uint) (a : Val C Γ .uint) (x : Var) :
    Premise.Sound m (.transfer (.simple sadr) a)
      (.capture .uint x a (.transfer (.simple sadr.up) (.simple (.local .here)))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_transfer, Stmt.run_transfer,
      Run.transfer_push σ (t := .val .uint) v (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
        (Simple.eval_up (t := .val .uint) sadr σ v) (by rw [hv]; rfl), pushed_drop]
  · obtain ⟨u, hu⟩ := Simple.eval_ok σ sadr
    rw [Stmt.run_transfer]
    simp only [Run.transfer, Val.eval, hu, Res.bind_ok]
    refine Res.Sim.err_bind (Solidity.Value.asInt_noPanic u) ‹_› fun _ _ => ?_
    simp only [hh]
    exact Res.Sim.refl _

/-- `transfer_unfold_leftFstReceiver`: the receiver captured. -/
theorem sound_transferLeft (r a : Val C Γ .uint) (x : Var) :
    Premise.Sound m (.transfer r a) (.capture .uint x r (.transfer (.simple (.local .here)) a.up)) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_transfer, Stmt.run_transfer,
      Run.transfer_push σ (t := .val .uint) v (.simple (.local .here)) a.up r a (by rw [hv]; rfl)
        (Val.eval_up (t := .val .uint) σ v a), pushed_drop]
  · rw [Stmt.run_transfer]
    simp only [Run.transfer, hh]
    exact Res.Sim.refl _

/-- **A transfer** (`transferStep`). -/
theorem transferStep_sound (k : Nat) (r a : Val C Γ .uint) (q : Premise C Γ Γ)
    (hs : transferStep k m r a = some q) : Premise.Sound m (.transfer r a) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact sound_transferBox σ sadr se
      | diamond => cases hs; exact sound_done_false σ _
    | _ => cases hs; exact sound_transferRight σ sadr _ _
  | _ => cases hs; exact sound_transferLeft σ _ a _

/-- `send_unfold_rightSndArgument`: the amount captured. -/
theorem sound_sendRight (pv : Idx Γ (.val .bool)) (sadr : Simple C Γ .uint) (a : Val C Γ .uint)
    (x : Var) :
    Premise.Sound m (.send pv (.simple sadr) a)
      (.capture .uint x a (.send pv.there (.simple sadr.up) (.simple (.local .here)))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_send, Stmt.run_send,
      Run.send_push σ (t := .val .uint) v pv (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
        (Simple.eval_up (t := .val .uint) sadr σ v) (by rw [hv]; rfl), pushed_drop]
  · obtain ⟨u, hu⟩ := Simple.eval_ok σ sadr
    rw [Stmt.run_send]
    simp only [Run.send, Val.eval, hu, Res.bind_ok]
    refine Res.Sim.err_bind (Solidity.Value.asInt_noPanic u) ‹_› fun _ _ => ?_
    simp only [hh]
    exact Res.Sim.refl _

/-- `send_unfold_leftFstReceiver`: the receiver captured. -/
theorem sound_sendLeft (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (x : Var) :
    Premise.Sound m (.send pv r a)
      (.capture .uint x r (.send pv.there (.simple (.local .here)) a.up)) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_send, Stmt.run_send,
      Run.send_push σ (t := .val .uint) v pv (.simple (.local .here)) a.up r a (by rw [hv]; rfl)
        (Val.eval_up (t := .val .uint) σ v a), pushed_drop]
  · rw [Stmt.run_send]
    simp only [Run.send, hh]
    exact Res.Sim.refl _

/-- **A send** (`sendStep`). -/
theorem sendStep_sound (k : Nat) (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (q : Premise C Γ Γ)
    (hs : sendStep k m pv r a = some q) : Premise.Sound m (.send pv r a) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact sound_send σ pv sadr se _
      | diamond => cases hs; exact sound_send σ pv sadr se _
    | _ => cases hs; exact sound_sendRight σ pv sadr _ _
  | _ => cases hs; exact sound_sendLeft σ pv _ a _

/-! ### `if`, `require`, `assert` -/

/-- A block weakened under one local runs as before, its locals popped (the
run of `Prog.wk up`). -/
def WkRuns (σ : State C Γ) (t : LTy) : Prop :=
  ∀ {Δ : Ctx} (P : Prog C Γ Δ) (w : t.Denote C),
    ((P.wk (up (t := t))).2.2.run (σ.push w)).map (State.drop (P.wk up).2.2.ext) =
      pushed w ((P.run σ).map (State.drop P.ext))

/-- `ifElseUnfold`: the condition captured, the branches weakened under it. -/
theorem sound_iteCapture {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂)
    (x : Var) (hwk : WkRuns σ (.val .bool)) :
    Premise.Sound m (.ite c thn els)
      (.capture .bool x c (.ite (.simple (.local .here)) (thn.wk up).2.2 (els.wk up).2.2)) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_ite, Stmt.run_ite]
    simp only [Run.ite, Val.eval, Simple.eval_here, hv, pure_bind, Res.bind_ok]
    cases v with
    | bool b =>
      cases b
      · exact (congrArg _ (hwk els _)).trans (pushed_drop _ _)
      · exact (congrArg _ (hwk thn _)).trans (pushed_drop _ _)
    | int => rfl
  · rw [Stmt.run_ite]
    simp only [Run.ite, hh]
    exact Res.Sim.refl _

/-- **An `if`** (`iteStep`). -/
theorem iteStep_sound (k : Nat) (hwk : WkRuns σ (.val .bool)) {Γ₁ Γ₂ : Ctx}
    (c : Val C Γ .bool) (thn : Prog C Γ Γ₁) (els : Prog C Γ Γ₂) (q : Premise C Γ Γ)
    (hs : iteStep k c thn els = some q) : Premise.Sound m (.ite c thn els) q σ := by
  cases c with
  | simple se =>
    cases hs
    obtain ⟨v, hv⟩ := Simple.eval_ok σ se
    cases v with
    | bool b => exact fun ω κ φ h _ => Stmt.step_sound_ifElseSplit se thn els σ ⟨b, hv⟩ ω κ φ h
    | int n =>
      refine Premise.Sound.splitStuck σ (fun h => nomatch (holds_isBool se σ hv true).1 h)
        (fun h => nomatch (holds_isBool se σ hv false).1 h) ?_
      rw [Stmt.run_ite]
      simp only [Run.ite, Val.eval, hv, Res.bind_ok]
  | _ => cases hs; exact sound_iteCapture σ _ thn els _ hwk

/-- **A `require`** (`requireStep`). -/
theorem requireStep_sound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : requireStep k c = some q) : Premise.Sound m (.require c) q σ := by
  cases c with
  | simple se =>
    cases hs
    obtain ⟨v, hv⟩ := Simple.eval_ok σ se
    cases v with
    | bool b => exact fun ω κ φ h _ => Stmt.step_sound_requireSimple se σ ⟨b, hv⟩ ω κ φ h
    | int n =>
      refine Premise.Sound.splitStuck σ (fun h => nomatch (holds_isBool se σ hv true).1 h)
        (fun h => nomatch (holds_isBool se σ hv false).1 h) ?_
      rw [Stmt.run_require]
      simp only [Val.eval, hv, Res.bind_ok, guardOk]
  | _ => cases hs; exact fun ω κ φ h _ => Stmt.step_sound_requireConditionCapture k _ σ ω κ φ h

/-- **An `assert`** (`assertStep`). -/
theorem assertStep_sound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : assertStep k c = some q) : Premise.Sound m (.assert c) q σ := by
  cases c with
  | simple se => cases hs; exact fun ω κ φ h _ => Stmt.step_sound_assertSimple se σ ω κ φ h
  | _ => cases hs; exact fun ω κ φ h _ => Stmt.step_sound_assertConditionCapture k _ σ ω κ φ h

/-! ### Declarations, `revert`, blocks -/

/-- `storageLocalDeclInitDrop`: `⟨[ T storage lsv = r; ]⟩ ⇝ ⟨[ lsv = r; ]⟩`. -/
theorem sound_declStorageInit {R : RefTy} (x : Var) (r : ARhs C Γ R) :
    Premise.Sound m (.declStorage R x (some r)) (.bind x (.alias R) (.cons (.rebind .here r.up) .nil))
      σ := by
  refine Premise.Sound.bind ⟨none, ?_⟩
  rw [Prog.run_single, Stmt.run_rebind, Stmt.run_declStorage]
  simp only [Run.rebind, Run.declStorage, ARhs.eval_up]
  cases r.eval σ <;> rfl

/-- `memoryLocalDeclInitDrop`: `⟨[ T memory mv = r; ]⟩ ⇝ ⟨[ mv = r; ]⟩`. -/
theorem sound_declMemInit {R : RefTy} (x : Var) (r : MRhs C Γ R)
    (hd : ((some r).isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Premise.Sound m (.declMem R x (some r) hd hm) (.bind x (.mem R) (.cons (.rebindMem .here r.up) .nil))
      σ := by
  refine Premise.Sound.bind ⟨0, ?_⟩
  rw [Prog.run_single, Stmt.run_rebindMem, Stmt.run_declMem]
  simp only [Run.rebindMem, Run.declMem, MRhs.eval_up]
  cases r.eval σ <;> rfl

end Control

end Solidity.Core
