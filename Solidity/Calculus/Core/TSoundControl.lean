import Solidity.Calculus.Core.TSoundLocal

/-!
# Soundness over the typed state: payments, control flow, declarations

`Calculus/Core/SoundControl.lean` and `Logic.lean`'s `Stmt.step_sound_*`
over the typed run: `transferStep`, `sendStep`, `iteStep`, `requireStep`,
`assertStep`, the declarations with an initializer (`Premise.bind`), and a
block, each `Premise.TSound`.  A `bool` value is a `bool` here, so a split
on a simple condition covers every state (`tholds_isBool`), with no stuck
case; a captured `if` condition reads its branches weakened under the
captured local, which run as before by `Semantics/Core/TypedRunWk.lean`'s
`Prog.trun_wk` (`Prog.trun_wk_up`).

The hidden binder of `memoryLocalDeclInitDrop` ranges, under the box, over
the references the heap typing gives the local's type, which may be none
(`docs/intrinsic.md`, decision 12): its arm asks for one under the box
(`tsound_declMemInit`'s `hbox`) where the initializer allocates.  At a
memory alias the object it names is one, and a halt reading it closes the
box (`tsound_declMemAlias`); a storage alias and a value always have one.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

section Control

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-! ### Payments -/

/-- `transfer_unfold_rightSndArgument`: the amount captured. -/
theorem tsound_transferRight (sadr : Simple C Γ .uint) (a : Val C Γ .uint) (x : Var) :
    Premise.TSound m (.transfer (.simple sadr) a)
      (.capture .uint x a (.transfer (.simple sadr.up) (.simple (.local .here)))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .val .uint) v (TRun.transfer_pushT σ (t := .val .uint) v
      (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
      (by simp only [Val.evalT, Simple.evalT_up]) (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.transfer _ a σ).map _ = _
    simp only [TRun.transfer, Val.evalT, ok_bind, hh]; rfl

/-- `transfer_unfold_leftFstReceiver`: the receiver captured. -/
theorem tsound_transferLeft (r a : Val C Γ .uint) (x : Var) :
    Premise.TSound m (.transfer r a)
      (.capture .uint x r (.transfer (.simple (.local .here)) a.up)) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .val .uint) v (TRun.transfer_pushT σ (t := .val .uint) v
      (.simple (.local .here)) a.up r a (by rw [hv]; rfl) (Val.evalT_up σ (t := .val .uint) v a))
  · refine TRes.Sim.err_refl ?_
    show (TRun.transfer r a σ).map _ = _
    simp only [TRun.transfer, hh]; rfl

/-- **A transfer** (`transferStep`). -/
theorem transferStep_tsound (k : Nat) (r a : Val C Γ .uint) (q : Premise C Γ Γ)
    (hs : transferStep k m r a = some q) : Premise.TSound m (.transfer r a) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact tsound_transferBox σ sadr se
      | diamond => cases hs; exact tsound_done_false σ _
    | _ => cases hs; exact tsound_transferRight σ sadr _ _
  | _ => cases hs; exact tsound_transferLeft σ _ a _

/-- `send_unfold_rightSndArgument`: the amount captured. -/
theorem tsound_sendRight (pv : Idx Γ (.val .bool)) (sadr : Simple C Γ .uint) (a : Val C Γ .uint)
    (x : Var) :
    Premise.TSound m (.send pv (.simple sadr) a)
      (.capture .uint x a (.send pv.there (.simple sadr.up) (.simple (.local .here)))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .val .uint) v (TRun.send_pushT σ (t := .val .uint) v pv
      (.simple sadr.up) (.simple (.local .here)) (.simple sadr) a
      (by simp only [Val.evalT, Simple.evalT_up]) (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.send pv _ a σ).map _ = _
    simp only [TRun.send, Val.evalT, ok_bind, hh]; rfl

/-- `send_unfold_leftFstReceiver`: the receiver captured. -/
theorem tsound_sendLeft (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (x : Var) :
    Premise.TSound m (.send pv r a)
      (.capture .uint x r (.send pv.there (.simple (.local .here)) a.up)) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .val .uint) v (TRun.send_pushT σ (t := .val .uint) v pv
      (.simple (.local .here)) a.up r a (by rw [hv]; rfl) (Val.evalT_up σ (t := .val .uint) v a))
  · refine TRes.Sim.err_refl ?_
    show (TRun.send pv r a σ).map _ = _
    simp only [TRun.send, hh]; rfl

/-- **A send** (`sendStep`). -/
theorem sendStep_tsound (k : Nat) (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint)
    (q : Premise C Γ Γ) (hs : sendStep k m pv r a = some q) :
    Premise.TSound m (.send pv r a) q σ := by
  cases r with
  | simple sadr =>
    cases a with
    | simple se =>
      cases m with
      | box => cases hs; exact tsound_send σ pv sadr se _
      | diamond => cases hs; exact tsound_send σ pv sadr se _
    | _ => cases hs; exact tsound_sendRight σ pv sadr _ _
  | _ => cases hs; exact tsound_sendLeft σ pv _ a _

/-! ### `if`, `require`, `assert` -/

/-- `se = b` holds where `se` is `b`: the condition read on the erasure. -/
theorem tholds_isBool (se : Simple C Γ .bool) (b : Bool) :
    tholds σ (Fml.isBool se.lower b) ↔ se.evalT σ = b := by
  show holds σ.erase (Fml.isBool se.lower b) ↔ _
  rw [holds_isBool se σ.erase (Simple.evalT_erase σ se) b]
  exact ⟨fun h => by injection h, fun h => by rw [← h]; rfl⟩

/-- A block weakened under one local runs as before, lifted, its locals
popped (`Prog.trun_wk` at `up`). -/
theorem Prog.trun_wk_up {t : LTy} {Δ : Ctx} (P : Prog C Γ Δ) (w : t.TDenote C σ.H) :
    ((P.wk (Core.up (t := t))).2.2.trun (σ.push w)).map (Out.drop (P.wk Core.up).2.2.ext) =
      pushedT σ w ((P.trun σ).map (Out.drop P.ext)) :=
  TWkRel.eq_lifted (TWkRel.drop (Prog.wk_over P Core.up) (Prog.trun_wk P Core.up σ (w, σ.env)))

/-- `ifElseUnfold`: the condition captured, the branches weakened under it. -/
theorem tsound_iteCapture {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) (x : Var) :
    Premise.TSound m (.ite c thn els)
      (.capture .bool x c (.ite (.simple (.local .here)) (thn.wk up).2.2 (els.wk up).2.2)) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ (t := .val .bool) v ?_
    show TRun.ite (.simple (.local .here)) _ ((thn.wk up).2.2.trunR) _ ((els.wk up).2.2.trunR)
      (σ.push v) = pushedT σ v (TRun.ite c thn.ext thn.trunR els.ext els.trunR σ)
    simp only [TRun.ite, Val.evalT, ok_bind, hv]
    cases v
    · exact Prog.trun_wk_up σ els _
    · exact Prog.trun_wk_up σ thn _
  · refine TRes.Sim.err_refl ?_
    show (TRun.ite c _ _ _ _ σ).map _ = _
    simp only [TRun.ite, hh]; rfl

/-- **An `if`** (`iteStep`). -/
theorem iteStep_tsound (k : Nat) {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) (q : Premise C Γ Γ) (hs : iteStep k c thn els = some q) :
    Premise.TSound m (.ite c thn els) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.tsound_split σ (fun h => ?_) (fun h => ?_) ?_
    · rw [Stmt.trunSt_ite_simple, (tholds_isBool σ se true).1 h]; rfl
    · rw [Stmt.trunSt_ite_simple, (tholds_isBool σ se false).1 h]; rfl
    · cases hv : se.evalT σ
      · exact .inr ((tholds_isBool σ se false).2 hv)
      · exact .inl ((tholds_isBool σ se true).2 hv)
  | _ => cases hs; exact tsound_iteCapture σ _ thn els _

/-- `requireConditionCapture`: `⟨[ require(nse); ]⟩ ⇝ ⟨[ bool se = nse; require(se); ]⟩`. -/
theorem tsound_requireCapture (c : Val C Γ .bool) (x : Var) :
    Premise.TSound m (.require c) (.capture .bool x c (.require (.simple (.local .here)))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .val .bool) v
      (TRun.require_pushT σ (t := .val .bool) v _ c (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.require c σ).map _ = _
    simp only [TRun.require, hh]; rfl

/-- **A `require`** (`requireStep`): `requireSimple`, or the condition
captured. -/
theorem requireStep_tsound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : requireStep k c = some q) : Premise.TSound m (.require c) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.tsound_split σ (fun h => ?_) (fun h => ?_) ?_
    · show (Prog.trunSt σ .nil).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (tholds_isBool σ se true).1 h]; rfl
    · show (Prog.trunSt σ (.cons .revert .nil)).map _ = (TRun.require (.simple se) σ).map _
      simp only [TRun.require, Val.evalT, ok_bind, (tholds_isBool σ se false).1 h]; rfl
    · cases hv : se.evalT σ
      · exact .inr ((tholds_isBool σ se false).2 hv)
      · exact .inl ((tholds_isBool σ se true).2 hv)
  | _ => cases hs; exact tsound_requireCapture σ _ _

/-- `assertConditionCapture`: `⟨[ assert(nse); ]⟩ ⇝ ⟨[ bool se = nse; assert(se); ]⟩`. -/
theorem tsound_assertCapture (c : Val C Γ .bool) (x : Var) :
    Premise.TSound m (.assert c) (.capture .bool x c (.assert (.simple (.local .here)))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .val .bool) v
      (TRun.assert_pushT σ (t := .val .bool) v _ c (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.assert c σ).map _ = _
    simp only [TRun.assert, hh]; rfl

/-- **An `assert`** (`assertStep`): `assertSimple`, or the condition
captured. -/
theorem assertStep_tsound (k : Nat) (c : Val C Γ .bool) (q : Premise C Γ Γ)
    (hs : assertStep k c = some q) : Premise.TSound m (.assert c) q σ := by
  cases c with
  | simple se =>
    cases hs
    refine Premise.tsound_check σ fun h => ?_
    show (TRun.assert (.simple se) σ).map _ = _
    simp only [TRun.assert, Val.evalT, ok_bind, (tholds_isBool σ se true).1 h]; rfl
  | _ => cases hs; exact tsound_assertCapture σ _ _

/-! ### Declarations, `revert`, blocks -/

/-- `localValueDeclInitDrop`: `⟨[ T v = e; ]⟩ ⇝ ⟨[ v = e; ]⟩`, `v` bound by
the hidden binder. -/
theorem tsound_localValueDeclInitDrop {p : PrimTy} (x : Var) (e : Val C Γ p) :
    Premise.TSound m (.declLocal p x (some e))
      (.bind x (.val p) (.cons (.assignLocal .here e.up) .nil)) σ := by
  refine Premise.tsound_bind_all σ (fun v => ?_) fun _ => ⟨PrimTy.dflt p⟩
  rw [Prog.trunSt_single, Stmt.trunSt_assignLocal, Stmt.trunSt_declLocal, Val.evalT_up]
  cases e.evalT σ <;> rfl

/-- `storageLocalDeclInitDrop`: `⟨[ T storage lsv = r; ]⟩ ⇝ ⟨[ lsv = r; ]⟩`. -/
theorem tsound_declStorageInit {R : RefTy} (x : Var) (r : ARhs C Γ R) :
    Premise.TSound m (.declStorage R x (some r))
      (.bind x (.alias R) (.cons (.rebind .here r.up) .nil)) σ := by
  refine Premise.tsound_bind_all σ (fun v => ?_) fun _ => ⟨none⟩
  rw [Prog.trunSt_single]
  show (TRun.rebind .here r.up (σ.push v)).map _ = (TRun.declStorage R (some r) σ).map _
  simp only [TRun.rebind, TRun.declStorage, ARhs.evalT_up]
  cases r.evalT σ <;> rfl

/-- `memoryLocalDeclInitDrop`: `⟨[ T memory mv = r; ]⟩ ⇝ ⟨[ mv = r; ]⟩`.  Under
the box the binder is universal, so the heap typing must give the local's
type a reference (decision 12). -/
theorem tsound_declMemInit {R : RefTy} (x : Var) (r : MRhs C Γ R)
    (hd : ((some r).isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true)
    (hbox : m = .box → Nonempty ((LTy.mem R).TDenote C σ.H)) :
    Premise.TSound m (.declMem R x (some r) hd hm)
      (.bind x (.mem R) (.cons (.rebindMem .here r.up) .nil)) σ := by
  refine Premise.tsound_bind_all σ (fun v => ?_) hbox
  rw [Prog.trunSt_single]
  show (TRun.rebindMem .here r.up (σ.push v)).map _ = (TRun.declMem R (some r) hm σ).map _
  simp only [TRun.rebindMem, TRun.declMem, MRhs.evalT_up]
  cases r.evalT σ <;> rfl

/-- `memoryLocalDeclInitDrop` at an alias, `T memory mv = mp;`: no inhabitant
needed under the box.  The object `mp` names is one; when `mp` halts, it is
not in a panic (`MPath.mvalT_noPanic`), so the box holds. -/
theorem tsound_declMemAlias {R : RefTy} (x : Var) (b : MPath C Γ (.ref R))
    (hd : ((some (MRhs.alias b)).isSome || (Ty.ref R).defaultOkS) = true)
    (hm : (Ty.ref R).mapFree = true) :
    Premise.TSound m (.declMem R x (some (.alias b)) hd hm)
      (.bind x (.mem R) (.cons (.rebindMem .here (MRhs.alias b).up) .nil)) σ := by
  have hs : ∀ v : (LTy.mem R).TDenote C σ.H,
      Prog.trunSt (σ.push v) (.cons (.rebindMem .here (MRhs.alias b).up) .nil) =
        Stmt.trunSt σ (.declMem R x (some (.alias b)) hd hm) := fun v => by
    rw [Prog.trunSt_single]
    show (TRun.rebindMem .here (MRhs.alias b).up (σ.push v)).map _ =
      (TRun.declMem R (some (.alias b)) hm σ).map _
    simp only [TRun.rebindMem, TRun.declMem, MRhs.evalT_up]
    cases (MRhs.alias b).evalT σ <;> rfl
  intro _ _ ω κ φ h
  cases hb : b.mvalT σ with
  | ok r => exact Premise.tsound_bind σ ⟨r, hs r⟩ ω κ φ h
  | error e =>
    cases m with
    | diamond => exact Premise.tsound_bind_all (m := .diamond) σ hs nofun ω κ φ h
    | box =>
      refine Premise.tsound_of_halt σ (e := e) ?_ (fun hp => MPath.mvalT_noPanic σ b (hp ▸ hb))
        ω κ φ h
      show (TRun.declMem R (some (.alias b)) hm σ).map _ = _
      simp only [TRun.declMem, MRhs.evalT, hb]
      rfl

/-- A block, its locals popped after it: `⟨[ { body } ]⟩ ⇝ ⟨[ body ]⟩`. -/
theorem tsound_block {Γ₂ : Ctx} (body : Prog C Γ Γ₂) :
    Premise.TSound m (.block body) (.unfold body body.ext) σ := by
  refine Premise.tsound_unfold σ ?_
  show _ = (TRun.block body.ext body.trunR σ).map _
  simp only [TRun.block]
  show ((body.trunR σ).map (·.st)).map _ = ((body.trunR σ).map _).map _
  cases body.trunR σ <;> rfl

end Control

end Solidity.Core
