import Solidity.Calculus.Core.SoundCapture

/-!
# Soundness of the arms on locals, payments and control flow

`Calculus/Core/Arms.lean`'s `localStep`, `rebindStep`, `opStep`, `incStep`,
`transferStep`, `sendStep`, `iteStep`, `requireStep`, `assertStep`, and
`Step.lean`'s declarations, `revert` and blocks, each sound in the shape
of `Calculus/Core/SoundKit.lean` (`Premise.Sound`).  A capture is
`Calculus/Core/SoundCapture.lean`'s, its statement read on the pushed state
by `Calculus/Core/SoundArms.lean`'s push lemmas.

The split on a simple condition needs it to hold a `bool` (`State.Typed`);
a captured `if` condition needs the branches, weakened under it, to run as
before (`WkRuns`, the run of `Prog.wk up`, which the call arms prove).
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic evalBinop)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

section Local

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- A simple condition holds a `bool` in a typed state. -/
theorem Simple.eval_bool (hσ : σ.Typed) (se : Simple C Γ .bool) :
    ∃ b : Bool, se.eval σ = .ok (.bool b) := by
  cases se with
  | lit n h => simp only [PrimTy.inRange, Bool.false_eq_true] at h
  | bool b => exact ⟨b, rfl⟩
  | «local» i =>
    obtain ⟨b, hb⟩ := hσ i
    exact ⟨b, by rw [← hb]; rfl⟩
  | env k hp => cases hp

theorem evalBinop_error {op : BinOp} (hsc : op.shortCircuits = false) (p : PrimTy) (lv : Value)
    (h : Halt) : evalBinop op p lv (.error h) = .error h := by
  cases op <;> first | rfl | simp only [BinOp.shortCircuits, Bool.true_eq_false] at hsc

/-! ### A local assigned -/

/-- `binopUnfoldRight`: `⟨[ v = se ⊕ nse; ]⟩ ⇝ ⟨[ T se' = nse; v = se ⊕ se'; ]⟩`. -/
theorem sound_binopRight {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp) (ha : op.accepts p' = true)
    (hq : op.ret p' = p) (hsc : op.shortCircuits = false) (a : Simple C Γ p') (b : Val C Γ p')
    (x : Var) :
    Premise.Sound m (.assignLocal i (.binop op ha hq (.simple a) b))
      (.capture p' x b (.assignLocal i.there (.binop op ha hq (.simple a.up) (.simple (.local .here)))))
      σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_assignLocal, Stmt.run_assignLocal,
      Run.assignLocal_push σ (t := .val p') v i _ (.binop op ha hq (.simple a) b), pushed_drop]
    simp only [Val.eval, Simple.eval_up, Simple.eval_here, hv]
    rfl
  · obtain ⟨u, hu⟩ := Simple.eval_ok σ a
    show Res.Sim _ (Run.assignLocal i _ σ)
    simp only [Run.assignLocal, Val.eval, hu, hh, Res.bind_ok, evalBinop_error hsc]
    exact Res.Sim.refl _

/-- `storageLengthRead_unfold_rightFst`: the receiver bound first. -/
theorem sound_lenCapture {p : PrimTy} (i : Idx Γ (.val p)) {E : Ty} (b : SPath C Γ (.array E))
    (hp : p = .uint) (x : Var) :
    Premise.Sound m (.assignLocal i (.len b hp))
      (.captureSP x b (.assignLocal i.there (.len (.alias .here) hp))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_assignLocal, Stmt.run_assignLocal,
      Run.assignLocal_push σ (t := .alias _) (some q) i _ (.len b hp), pushed_drop]
    simp only [Val.eval, SPath.resolve_here, hq, State.glob_push, Res.bind_ok, pure_bind]
  · show Res.Sim _ (Run.assignLocal i _ σ)
    simp only [Run.assignLocal, Val.eval, hh]
    exact Res.Sim.refl _

/-- `memoryLengthRead_unfold_rightFst`: the receiver bound first. -/
theorem sound_mlenCapture {p : PrimTy} (i : Idx Γ (.val p)) {E : Ty} (b : MPath C Γ (.array E))
    (hm : (Ty.ref (.array E)).mapFree = true) (hp : p = .uint) (x : Var) :
    Premise.Sound m (.assignLocal i (.mlen b hp))
      (.captureMV x b (.assignLocal i.there (.mlen (.var .here hm) hp))) σ := by
  refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_assignLocal, Stmt.run_assignLocal,
      Run.assignLocal_push σ (t := .mem _) id i _ (.mlen b hp), pushed_drop]
    simp only [Val.eval, MPath.mval_here, State.glob_push, Res.bind_ok, pure_bind]
    rw [← bind_assoc, hid]; rfl
  · show Res.Sim _ (Run.assignLocal i _ σ)
    simp only [Run.assignLocal, Val.eval, bind_assoc]
    rw [← bind_assoc, hh]
    exact Res.Sim.refl _

theorem Env.set_set {Γ : Ctx} {t : LTy} (i : Idx Γ t) (v w : t.Denote C) (e : Env C Γ) :
    Env.set i w (Env.set i v e) = Env.set i w e := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg (e.1, ·) (ih v w e.2)

theorem State.setLocal_setLocal {t : LTy} (i : Idx Γ t) (v w : t.Denote C) :
    (σ.setLocal i v).setLocal i w = σ.setLocal i w := by
  show σ.withEnv (Env.set i w (Env.set i v σ.env)) = σ.withEnv (Env.set i w σ.env)
  rw [Env.set_set]

theorem State.get_setLocal {t : LTy} (i : Idx Γ t) (v : t.Denote C) :
    (Env.get i (σ.setLocal i v).env : t.Denote C) = v := Env.get_set i v σ.env

theorem evalBinop_and_true (bv : Value) :
    evalBinop .and .bool bv (.ok (.bool true)) = evalBinop .and .bool (.bool true) (.ok bv) := by
  cases bv with
  | int n => rfl
  | bool x => cases x <;> rfl

theorem evalBinop_or_false (bv : Value) :
    evalBinop .or .bool bv (.ok (.bool false)) = evalBinop .or .bool (.bool false) (.ok bv) := by
  cases bv with
  | int n => rfl
  | bool x => cases x <;> rfl

/-- `logicalAndShortCircuitRhs`: `v = se && nse;` is
`if (se) { v = nse; v = v && true; } else v = false;`. -/
theorem sound_shortAnd (hσ : σ.Typed) (i : Idx Γ (.val .bool)) (ha : BinOp.and.accepts .bool = true)
    (hq : BinOp.and.ret .bool = .bool) (a : Simple C Γ .bool) (b : Val C Γ .bool) :
    Premise.Sound m (.assignLocal i (.binop .and ha hq (.simple a) b))
      (.unfold (.cons (.ite (.simple a)
        (.cons (.assignLocal i b)
          (.cons (.assignLocal i (.binop .and rfl rfl (.simple (.local i)) (.simple (.bool true)))) .nil))
        (.cons (.assignLocal i (.simple (.bool false))) .nil)) .nil) .refl) σ := by
  obtain ⟨ab, hab⟩ := Simple.eval_bool σ hσ a
  refine Premise.Sound.unfoldSim ?_
  rw [Res.map_drop_refl, Prog.run_single, Stmt.run_ite, Stmt.run_assignLocal]
  simp only [Run.ite, Run.assignLocal, Val.eval, hab, Res.bind_ok]
  cases ab with
  | false => exact Res.Sim.refl _
  | true =>
    simp only [Prog.run_cons, Stmt.run_assignLocal, Run.assignLocal, Val.eval, Simple.eval,
      State.get_setLocal, Res.map_drop_refl]
    cases hb : b.eval σ with
    | error h => exact Res.Sim.refl _
    | ok bv =>
      simp only [Res.bind_ok, Except.bind, pure, Except.pure, State.get_setLocal]
      rw [evalBinop_and_true bv]
      cases evalBinop .and .bool (.bool true) (.ok bv) with
      | error => exact Res.Sim.refl _
      | ok r => exact Res.Sim.of_eq (congrArg Except.ok (State.setLocal_setLocal σ i bv r))

/-- `logicalOrShortCircuitRhs`: `v = se || nse;` is
`if (se) v = true; else { v = nse; v = v || false; }`. -/
theorem sound_shortOr (hσ : σ.Typed) (i : Idx Γ (.val .bool)) (ha : BinOp.or.accepts .bool = true)
    (hq : BinOp.or.ret .bool = .bool) (a : Simple C Γ .bool) (b : Val C Γ .bool) :
    Premise.Sound m (.assignLocal i (.binop .or ha hq (.simple a) b))
      (.unfold (.cons (.ite (.simple a)
        (.cons (.assignLocal i (.simple (.bool true))) .nil)
        (.cons (.assignLocal i b)
          (.cons (.assignLocal i (.binop .or rfl rfl (.simple (.local i)) (.simple (.bool false)))) .nil)))
        .nil) .refl) σ := by
  obtain ⟨ab, hab⟩ := Simple.eval_bool σ hσ a
  refine Premise.Sound.unfoldSim ?_
  rw [Res.map_drop_refl, Prog.run_single, Stmt.run_ite, Stmt.run_assignLocal]
  simp only [Run.ite, Run.assignLocal, Val.eval, hab, Res.bind_ok]
  cases ab with
  | true => exact Res.Sim.refl _
  | false =>
    simp only [Prog.run_cons, Stmt.run_assignLocal, Run.assignLocal, Val.eval, Simple.eval,
      State.get_setLocal, Res.map_drop_refl]
    cases hb : b.eval σ with
    | error h => exact Res.Sim.refl _
    | ok bv =>
      simp only [Res.bind_ok, Except.bind, pure, Except.pure, State.get_setLocal]
      rw [evalBinop_or_false bv]
      cases evalBinop .or .bool (.bool false) (.ok bv) with
      | error => exact Res.Sim.refl _
      | ok r => exact Res.Sim.of_eq (congrArg Except.ok (State.setLocal_setLocal σ i bv r))

/-- `logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs` (`shortStep`). -/
theorem shortStep_sound (hσ : σ.Typed) {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (q : Premise C Γ Γ) (hs : shortStep i op ha hq a b = some q) :
    Premise.Sound m (.assignLocal i (.binop op ha hq (.simple a) b)) q σ := by
  cases op <;> cases p' <;> (try cases hs) <;> subst hq <;> cases hs
  · exact sound_shortAnd σ hσ i ha rfl a b
  · exact sound_shortOr σ hσ i ha rfl a b

/-- `binopUnfoldRight`, or the short circuit of `&&`/`||`. -/
theorem binopRight_sound (k : Nat) (hσ : σ.Typed) {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (q : Premise C Γ Γ)
    (hs : (if op.shortCircuits then shortStep i op ha hq a b
      else some (.capture p' (fse k) b
        (.assignLocal i.there (.binop op ha hq (.simple a.up) (.simple (.local .here)))))) = some q) :
    Premise.Sound m (.assignLocal i (.binop op ha hq (.simple a) b)) q σ := by
  cases hsc : op.shortCircuits
  · rw [hsc] at hs; cases hs; exact sound_binopRight σ i op ha hq hsc a b _
  · rw [hsc] at hs; exact shortStep_sound σ hσ i op ha hq a b q hs

/-- **A local assigned** (`localStep`). -/
theorem localStep_sound (k : Nat) (hσ : σ.Typed) {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p)
    (q : Premise C Γ Γ) (hs : localStep k i v = some q) :
    Premise.Sound m (.assignLocal i v) q σ := by
  cases v with
  | simple s => cases hs; exact sound_setLocal σ i _
  | read l =>
    exact SHole.readStep_sound σ k (.local i) (fun _ _ _ h => by cases h; exact sound_setLocal σ i _)
      (fun _ _ _ _ h => by cases h; exact sound_setLocal σ i _)
      (fun _ _ _ _ h => by cases h; exact sound_setLocal σ i _) l q hs
  | binop op ha hq a b =>
    cases a with
    | simple a =>
      cases b with
      | simple b => cases hs; exact sound_setLocal σ i _
      | _ => exact binopRight_sound σ k hσ i op ha hq a _ q hs
    | _ => cases hs; exact fun ω κ φ => Stmt.step_sound_binopUnfoldLeft k i op ha hq _ b σ ω κ φ
  | unop op ha hq a =>
    cases a with
    | simple a => cases hs; exact sound_setLocal σ i _
    | _ => cases hs; exact fun ω κ φ => Stmt.step_sound_unopCapture k i op ha hq _ σ ω κ φ
  | ternary c a b => exact ternaryStep_sound σ k (.local i) c a b q hs
  | readMem l =>
    exact MHole.readStep_sound σ k (.local i) (fun _ _ _ _ _ h => by cases h; exact sound_setLocal σ i _)
      (fun _ _ _ _ _ h => by cases h; exact sound_setLocal σ i _) l q hs
  | len b hp =>
    simp only [localStep] at hs
    split at hs
    · cases hs; exact sound_setLocal σ i _
    · cases hs; exact sound_lenCapture σ i b hp _
  | mlen b hp =>
    cases b with
    | var mv hm => cases hs; exact sound_setLocal σ i _
    | loc l => cases hs; exact sound_mlenCapture σ i (.loc l) _ hp _

end Local

end Solidity.Core
