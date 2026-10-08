import Solidity.Calculus.Core.SoundCapture

/-!
# Soundness of the arms on locals

`Calculus/Core/Arms.lean`'s `localStep` (with the `&&`/`||` short
circuits, stuck on both sides where the local holds no `bool`),
`rebindStep`, `opStep`, `incStep` and `OpLoc.unfoldRecv`, each sound in the
shape of `Calculus/Core/SoundKit.lean` (`Premise.Sound`).  A capture is
`Calculus/Core/SoundCapture.lean`'s, its statement read on the pushed state
by `Calculus/Core/SoundArms.lean`'s push lemmas.
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic evalBinop)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

section Local

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- A `bool` simple value reads as a `bool` in a state whose `bool` locals
hold `bool`s. -/
theorem Simple.eval_bool {se : Simple C Γ .bool} (hT : σ.BoolOK) {v : Value}
    (hv : se.eval σ = .ok v) : ∃ b, v = .bool b := by
  cases se with
  | lit n hn => exact absurd (PrimTy.isNumeric_of_inRange hn) (by decide)
  | bool b => cases hv; exact ⟨b, rfl⟩
  | «local» i => cases hv; exact hT.get i
  | env k hp => cases hp

/-- **A split whose statement is stuck** (a condition that reads as no
`bool`), neither condition holding: the box holds of a stuck run, and the
diamond reads from no such state (its `bool` locals hold `bool`s). -/
theorem Premise.Sound.splitStuck {b : BlockKind} {Δ₁ Δ₂ : Ctx} {c c' : Fml C Γ}
    {P : Prog C Γ Δ₁} {Q : Prog C Γ Δ₂} {s : Stmt C Γ Γ}
    (hst : s.run σ = .error .stuck ∧ ¬ σ.BoolOK) : Premise.Sound m s (.split b c c' P Q) σ := by
  intro _ _ ω κ φ _
  refine holds_modal_intro fun hT => ?_
  cases m with
  | box =>
    rw [run_cons_frames, hst.1]
    exact ⟨trivial, fun h => nomatch h⟩
  | diamond => exact (hst.2 (hT rfl)).elim

/-- **A split is sound** when the branch each condition guards, its locals
popped, runs as `s`, and where neither holds the statement is stuck and the
state has a `bool` local holding no `bool`: one of them holds, or the box
holds of the stuck run, and the diamond does not read from that state. -/
theorem Premise.Sound.split {b : BlockKind} {Δ₁ Δ₂ : Ctx} {c c' : Fml C Γ}
    {P : Prog C Γ Δ₁} {Q : Prog C Γ Δ₂} {s : Stmt C Γ Γ}
    (hc : holds σ c → (Prog.run σ P).map (State.drop P.ext) = s.run σ)
    (hc' : holds σ c' → (Prog.run σ Q).map (State.drop Q.ext) = s.run σ)
    (hst : ¬ holds σ c → ¬ holds σ c' → s.run σ = .error .stuck ∧ ¬ σ.BoolOK) :
    Premise.Sound m s (.split b c c' P Q) σ := by
  intro _ _ ω κ φ h
  by_cases h₁ : holds σ c
  · exact Premise.sound_split σ hc hc' (.inl h₁) ω κ φ h
  by_cases h₂ : holds σ c'
  · exact Premise.sound_split σ hc hc' (.inr h₂) ω κ φ h
  · exact Premise.Sound.splitStuck σ (hst h₁ h₂) ω κ φ h

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
    simp only [Val.eval, MPath.mval_here, State.glob_push, pure_bind]
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
theorem sound_shortAnd (i : Idx Γ (.val .bool)) (ha : BinOp.and.accepts .bool = true)
    (hq : BinOp.and.ret .bool = .bool) (a : Simple C Γ .bool) (b : Val C Γ .bool) :
    Premise.Sound m (.assignLocal i (.binop .and ha hq (.simple a) b))
      (.unfold (.cons (.ite (.simple a)
        (.cons (.assignLocal i b)
          (.cons (.assignLocal i (.binop .and rfl rfl (.simple (.local i)) (.simple (.bool true)))) .nil))
        (.cons (.assignLocal i (.simple (.bool false))) .nil)) .nil) .refl) σ := by
  obtain ⟨av, hav⟩ := Simple.eval_ok σ a
  refine Premise.Sound.unfoldSim ?_
  rw [Res.map_drop_refl, Prog.run_single, Stmt.run_ite, Stmt.run_assignLocal]
  simp only [Run.ite, Run.assignLocal, Val.eval, hav, Res.bind_ok]
  cases av with
  | int n =>
    have hnp : NoPanic (b.eval σ) := Val.eval_noPanic σ b
    cases hb : b.eval σ with
    | error h =>
      show Res.Sim (.error .stuck) (.error h)
      exact ⟨fun e => (nomatch e), fun e => absurd (hb.trans (congrArg _ e)) hnp⟩
    | ok bv => exact Res.Sim.refl (.error .stuck)
  | bool ab =>
  cases ab with
  | false => exact Res.Sim.refl _
  | true =>
    simp only [Prog.run_cons, Stmt.run_assignLocal, Run.assignLocal, Val.eval, Simple.eval]
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
theorem sound_shortOr (i : Idx Γ (.val .bool)) (ha : BinOp.or.accepts .bool = true)
    (hq : BinOp.or.ret .bool = .bool) (a : Simple C Γ .bool) (b : Val C Γ .bool) :
    Premise.Sound m (.assignLocal i (.binop .or ha hq (.simple a) b))
      (.unfold (.cons (.ite (.simple a)
        (.cons (.assignLocal i (.simple (.bool true))) .nil)
        (.cons (.assignLocal i b)
          (.cons (.assignLocal i (.binop .or rfl rfl (.simple (.local i)) (.simple (.bool false)))) .nil)))
        .nil) .refl) σ := by
  obtain ⟨av, hav⟩ := Simple.eval_ok σ a
  refine Premise.Sound.unfoldSim ?_
  rw [Res.map_drop_refl, Prog.run_single, Stmt.run_ite, Stmt.run_assignLocal]
  simp only [Run.ite, Run.assignLocal, Val.eval, hav, Res.bind_ok]
  cases av with
  | int n =>
    have hnp : NoPanic (b.eval σ) := Val.eval_noPanic σ b
    cases hb : b.eval σ with
    | error h =>
      show Res.Sim (.error .stuck) (.error h)
      exact ⟨fun e => (nomatch e), fun e => absurd (hb.trans (congrArg _ e)) hnp⟩
    | ok bv => exact Res.Sim.refl (.error .stuck)
  | bool ab =>
  cases ab with
  | true => exact Res.Sim.refl _
  | false =>
    simp only [Prog.run_cons, Stmt.run_assignLocal, Run.assignLocal, Val.eval, Simple.eval]
    cases hb : b.eval σ with
    | error h => exact Res.Sim.refl _
    | ok bv =>
      simp only [Res.bind_ok, Except.bind, pure, Except.pure, State.get_setLocal]
      rw [evalBinop_or_false bv]
      cases evalBinop .or .bool (.bool false) (.ok bv) with
      | error => exact Res.Sim.refl _
      | ok r => exact Res.Sim.of_eq (congrArg Except.ok (State.setLocal_setLocal σ i bv r))

/-- `logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs` (`shortStep`). -/
theorem shortStep_sound {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (q : Premise C Γ Γ) (hs : shortStep i op ha hq a b = some q) :
    Premise.Sound m (.assignLocal i (.binop op ha hq (.simple a) b)) q σ := by
  cases op <;> cases p' <;> (try cases hs) <;> subst hq <;> cases hs
  · exact sound_shortAnd σ i ha rfl a b
  · exact sound_shortOr σ i ha rfl a b

/-- `binopUnfoldRight`, or the short circuit of `&&`/`||`. -/
theorem binopRight_sound (k : Nat) {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (q : Premise C Γ Γ)
    (hs : (if op.shortCircuits then shortStep i op ha hq a b
      else some (.capture p' (fse k) b
        (.assignLocal i.there (.binop op ha hq (.simple a.up) (.simple (.local .here)))))) = some q) :
    Premise.Sound m (.assignLocal i (.binop op ha hq (.simple a) b)) q σ := by
  cases hsc : op.shortCircuits
  · rw [hsc] at hs; cases hs; exact sound_binopRight σ i op ha hq hsc a b _
  · rw [hsc] at hs; exact shortStep_sound σ i op ha hq a b q hs

/-- **A local assigned** (`localStep`). -/
theorem localStep_sound (k : Nat) {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p)
    (q : Premise C Γ Γ) (hs : localStep k i v = some q) :
    Premise.Sound m (.assignLocal i v) q σ := by
  cases v with
  | simple s => cases hs; exact sound_setLocal σ i _
  | read l =>
    exact SHole.readStep_sound σ k (.local i) l
      (fun _ _ _ _ h => by cases h; exact sound_setLocal σ i _)
      (fun _ _ _ _ _ h => by cases h; exact sound_setLocal σ i _)
      (fun _ _ _ _ _ h => by cases h; exact sound_setLocal σ i _) q hs
  | binop op ha hq a b =>
    cases a with
    | simple a =>
      cases b with
      | simple b => cases hs; exact sound_setLocal σ i _
      | _ => exact binopRight_sound σ k i op ha hq a _ q hs
    | _ => cases hs; exact fun ω κ φ h => Stmt.step_sound_binopUnfoldLeft k i op ha hq _ b σ ω κ φ h
  | unop op ha hq a =>
    cases a with
    | simple a => cases hs; exact sound_setLocal σ i _
    | _ => cases hs; exact fun ω κ φ h => Stmt.step_sound_unopCapture k i op ha hq _ σ ω κ φ h
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

/-! ### An alias bound -/

/-- `storageLocalRootPush_unfold_leftFstReceiver`: the receiver bound first. -/
theorem sound_rebindPushCapture {R : RefTy} (i : Idx Γ (.alias R)) (b : SPath C Γ (.array (.ref R)))
    (hd : (Ty.ref R).defaultOkS = true) (x : Var) :
    Premise.Sound m (.rebind i (.push b hd)) (.captureSP x b (.rebind i.there (.push (.alias .here) hd))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_rebind, Stmt.run_rebind,
      Run.rebind_push σ (t := .alias _) (some q) i _ (.push b hd)
        (ARhs.eval_push_push σ _ _ b hd (by rw [hq]; rfl)), pushed_drop]
  · rw [Stmt.run_rebind]
    simp only [Run.rebind, ARhs.eval, hh]
    exact Res.Sim.refl _

/-- **An alias bound** (`rebindStep`). -/
theorem rebindStep_sound (k : Nat) {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R)
    (q : Premise C Γ Γ) (hs : rebindStep k i r = some q) : Premise.Sound m (.rebind i r) q σ := by
  cases r with
  | path p =>
    cases p with
    | alias j => cases hs; exact sound_rebindPath σ i (.alias j)
    | loc l =>
      exact SHole.readStep_sound σ k (.rebind i) l
        (fun r h _ _ hq => by
          cases hq; exact sound_rebindPath (m := m) σ i (.loc (.root r h)))
        (fun b f hf _ _ hq => by
          cases hq; exact sound_rebindPath (m := m) σ i (.loc (.field b f hf)))
        (fun it b ie _ _ hq => by
          cases hq; exact sound_rebindPath (m := m) σ i (.loc (.index it b (.simple ie)))) q hs
  | push b hd =>
    simp only [rebindStep] at hs
    split at hs
    · cases hs; exact sound_rebindPush σ i b hd
    · cases hs; exact sound_rebindPushCapture σ i b hd _

/-! ### Compound assignment and `++`/`--` -/

/-- A statement on a compound target whose receiver is not simple: the
receiver bound first (`OpLoc.unfoldRecv`), when the statement read with the
bound receiver runs as before and halts where its receiver does. -/
theorem OpLoc.unfoldRecv_sound (k : Nat) {p : PrimTy}
    (s : {t : LTy} → OpLoc C (t :: Γ) p → Stmt C (t :: Γ) (t :: Γ)) (S : OpLoc C Γ p → Stmt C Γ Γ)
    (hpush : ∀ {t : LTy} (w : t.Denote C) (l' : OpLoc C (t :: Γ) p) (l : OpLoc C Γ p),
      OpLoc.Agree σ w l' l → (s l').run (σ.push w) = pushed w ((S l).run σ))
    (hstore : ∀ {sn : Name} (b : SPath C Γ (.struct sn)) f h,
      (S (.field b f h)).run σ = b.resolve σ >>= fun _ => (S (.field b f h)).run σ)
    (hindex : ∀ {R : RefTy} {kp : PrimTy} (it : IndexTy R kp (.prim p)) b ie,
      (S (.index it b ie)).run σ = b.resolve σ >>= fun _ => (S (.index it b ie)).run σ)
    (hmfield : ∀ {sn : Name} (b : MPath C Γ (.struct sn)) f h,
      (S (.mfield b f h)).run σ = (do (← b.mval σ).asRef) >>= fun _ => (S (.mfield b f h)).run σ)
    (hmindex : ∀ {R : RefTy} (a : ArrTy R (.prim p)) b ie,
      (S (.mindex a b ie)).run σ = (do (← b.mval σ).asRef) >>= fun _ => (S (.mindex a b ie)).run σ)
    (l : OpLoc C Γ p) (q : Premise C Γ Γ) (hq : l.unfoldRecv k s = some q) :
    Premise.Sound m (S l) q σ := by
  cases l with
  | field b f h =>
    simp only [OpLoc.unfoldRecv] at hq
    split at hq
    · cases hq
    · cases hq
      refine Premise.Sound.captureSPSim σ (fun r hr => ?_) (fun e he _ => ?_)
      · rw [hpush (t := .alias _) (some r) _ (.field b f h) (.field f h (by rw [hr]; rfl)), pushed_drop]
      · rw [hstore, he]; exact Res.Sim.refl _
  | index it b ie =>
    simp only [OpLoc.unfoldRecv] at hq
    split at hq
    · cases hq
    · cases hq
      refine Premise.Sound.captureSPSim σ (fun r hr => ?_) (fun e he _ => ?_)
      · rw [hpush (t := .alias _) (some r) _ (.index it b ie)
          (.index it (by rw [hr]; rfl) (Simple.eval_up ie σ _)), pushed_drop]
      · rw [hindex, he]; exact Res.Sim.refl _
  | mfield b f h =>
    cases b with
    | var => cases hq
    | loc l =>
      cases hq
      refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun e he _ => ?_)
      · rw [hpush (t := .mem _) id _ (.mfield (.loc l) f h) (.mfield f h ?_), pushed_drop]
        obtain ⟨mv, hmv, hr⟩ := Res.bind_eq_ok.1 hid
        rw [MPath.mval_here, hmv]
        cases mv <;> first | (cases hr; rfl) | (simp only [MVal.asRef] at hr; cases hr)
      · rw [hmfield, he]; exact Res.Sim.refl _
  | mindex a b ie =>
    cases b with
    | var => cases hq
    | loc l =>
      cases hq
      refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun e he _ => ?_)
      · rw [hpush (t := .mem _) id _ (.mindex a (.loc l) ie) (.mindex a ?_ (Simple.eval_up ie σ _)),
          pushed_drop]
        obtain ⟨mv, hmv, hr⟩ := Res.bind_eq_ok.1 hid
        rw [MPath.mval_here, hmv]
        cases mv <;> first | (cases hr; rfl) | (simp only [MVal.asRef] at hr; cases hr)
      · rw [hmindex, he]; exact Res.Sim.refl _
  | _ => cases hq

/-- `compoundAssignValueRhsCapture`: the source captured first. -/
theorem sound_opCapture {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) (x : Var) :
    Premise.Sound m (.opAssign op hop hp l r)
      (.capture p x r (.opAssign op hop hp l.up (.simple (.local .here)))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_opAssign, Stmt.run_opAssign,
      Run.opAssign_push σ (t := .val p) v op (OpLoc.Agree.of_up (t := .val p) σ v l) _ r (by rw [hv]; rfl),
      pushed_drop]
  · rw [Stmt.run_opAssign]
    simp only [Run.opAssign, hh]
    exact Res.Sim.refl _

/-- **A compound assignment** (`opStep`). -/
theorem opStep_sound (k : Nat) {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) (q : Premise C Γ Γ)
    (hs : opStep k op hop hp l r = some q) : Premise.Sound m (.opAssign op hop hp l r) q σ := by
  cases r with
  | simple se =>
    simp only [opStep] at hs
    split at hs
    · rename_i q' hq'
      cases hs
      obtain ⟨v, hv⟩ := Simple.eval_ok σ se
      refine OpLoc.unfoldRecv_sound σ k (fun l' => .opAssign op hop hp l' (.simple se.up))
        (fun l => .opAssign op hop hp l (.simple se)) (fun w l' l hl => ?_) (fun b f h => ?_)
        (fun it b ie => ?_) (fun b f h => ?_) (fun a b ie => ?_) l _ hq'
      · rw [Stmt.run_opAssign, Stmt.run_opAssign]
        exact Run.opAssign_push σ w op hl _ _ (Simple.eval_up se σ w)
      all_goals
        simp only [Stmt.run_opAssign, Run.opAssign, Val.eval, hv, Res.bind_ok, OpLoc.store,
          Loc.resolve, bind_assoc]
      · cases b.resolve σ <;> rfl
      · cases b.resolve σ <;> rfl
      · cases MPath.mval σ b with
        | error => rfl
        | ok mv => simp only [Res.bind_ok]; cases mv.asRef <;> rfl
      · cases MPath.mval σ b with
        | error => rfl
        | ok mv => simp only [Res.bind_ok]; cases mv.asRef <;> rfl
    · cases hs; exact sound_opAssign σ op hop hp l se
  | _ => cases hs; exact sound_opCapture σ op hop hp l _ _

/-- **`l++;`** (`incStep`). -/
theorem incStep_sound (k : Nat) {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (q : Premise C Γ Γ) (hs : incStep k op hp l = some q) :
    Premise.Sound m (.incDec op hp l) q σ := by
  simp only [incStep] at hs
  split at hs
  · rename_i q' hq'
    cases hs
    refine OpLoc.unfoldRecv_sound σ k (fun l' => .incDec op hp l') (fun l => .incDec op hp l)
      (fun w l' l hl => ?_) (fun b f h => ?_) (fun it b ie => ?_) (fun b f h => ?_)
      (fun a b ie => ?_) l _ hq'
    · rw [Stmt.run_incDec, Stmt.run_incDec]
      exact Run.incDec_push σ w op hl
    all_goals
      simp only [Stmt.run_incDec, Run.incDec, OpLoc.bump_field, OpLoc.bump_index,
        OpLoc.bump_mfield, OpLoc.bump_mindex, Loc.resolve, bind_assoc]
    · cases b.resolve σ <;> rfl
    · cases b.resolve σ <;> rfl
    · cases MPath.mval σ b with
      | error => rfl
      | ok mv => simp only [Res.bind_ok]; cases mv.asRef <;> rfl
    · cases MPath.mval σ b with
      | error => rfl
      | ok mv => simp only [Res.bind_ok]; cases mv.asRef <;> rfl
  · cases hs; exact sound_incDec σ op hp l

end Local

end Solidity.Core
