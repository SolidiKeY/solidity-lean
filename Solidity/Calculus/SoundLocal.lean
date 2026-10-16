import Solidity.Calculus.SoundCapture

/-!
# Soundness of the arms on locals

`localStep` with the `&&`/`||` short circuits, `rebindStep`, `opStep`,
`incStep` and `OpLoc.unfoldRecv` (with `binopUnfoldLeft`, `unopCapture`),
each `Premise.Sound`.  A `bool` local holds a `bool` here, so no branch is
stuck: a short circuit runs exactly as its unfolded `if`.
-/

namespace Solidity
open Solidity (Modality Srt Op0 Op1 Op2 Op3)
open Semantics (Selector)

variable {C : Contract}


open Solidity (Modality)

namespace TEnv

variable {H : HTy}

theorem set_set {Γ : Ctx} {t : LTy} : (i : Idx Γ t) → (v w : t.TDenote C H) → (e : TEnv C H Γ) →
    TEnv.set i w (TEnv.set i v e) = TEnv.set i w e
  | .here, _, _, _ => rfl
  | .there i, v, w, e => congrArg (e.1, ·) (set_set i v w e.2)

end TEnv

section Local

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

theorem State.setLocal_setLocal {t : LTy} (i : Idx Γ t) (v w : t.TDenote C σ.H) :
    (σ.setLocal i v).setLocal i w = σ.setLocal i w := by
  simp only [State.setLocal, TEnv.set_set]

theorem State.get_setLocal {t : LTy} (i : Idx Γ t) (v : t.TDenote C σ.H) :
    (TEnv.get i (σ.setLocal i v).env : t.TDenote C σ.H) = v := TEnv.get_set i v σ.env

theorem Stmt.runSt_assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Stmt.runSt σ (.assignLocal i v) = (v.evalT σ).map fun x => σ.setLocal i x := by
  show (TRun.assignLocal i v σ).map _ = _
  simp only [TRun.assignLocal]
  cases v.evalT σ <;> rfl

theorem BinOp.shortT_none {op : BinOp} (hsc : op.shortCircuits = false) {p : PrimTy}
    (x : p.Denote) : op.shortT x = none := by
  cases op <;> first | rfl | simp only [BinOp.shortCircuits, Bool.true_eq_false] at hsc

/-! ### A local assigned -/

/-- `binopUnfoldRight`: `⟨[ v = se ⊕ nse; ]⟩ ⇝ ⟨[ T se' = nse; v = se ⊕ se'; ]⟩`. -/
theorem sound_binopRight {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (hsc : op.shortCircuits = false)
    (a : Simple C Γ p') (b : Val C Γ p') (x : Var) :
    Premise.Runs m (.assignLocal i (.binop op ha hq (.simple a) b))
      (.capture p' x b
        (.assignLocal i.there (.binop op ha hq (.simple a.up) (.simple (.local .here))))) σ := by
  subst hq
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .val p') v (TRun.assignLocal_pushT σ (t := .val p') v i _
      (.binop op ha rfl (.simple a) b) ?_)
    simp only [Val.evalT, Simple.evalT_up, hv]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.assignLocal i _ σ).map _ = _
    simp only [TRun.assignLocal, Val.evalT, ok_bind, BinOp.shortT_none hsc, hh]; rfl

/-- `storageLengthRead_unfold_rightFst`: the receiver bound first. -/
theorem sound_lenCapture {p : PrimTy} (i : Idx Γ (.val p)) {E : Ty} (b : SPath C Γ (.array E))
    (hp : p = .uint) (x : Var) :
    Premise.Runs m (.assignLocal i (.len b hp))
      (.captureSP x b (.assignLocal i.there (.len (.alias .here) hp))) σ := by
  subst hp
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .alias _) (some q) (TRun.assignLocal_pushT σ (t := .alias _)
      (some q) i _ (.len b rfl) ?_)
    simp only [Val.evalT, hq]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.assignLocal i _ σ).map _ = _
    simp only [TRun.assignLocal, Val.evalT, hh]; rfl

/-- `memoryLengthRead_unfold_rightFst`: the receiver bound first. -/
theorem sound_mlenCapture {p : PrimTy} (i : Idx Γ (.val p)) {E : Ty} (b : MPath C Γ (.array E))
    (hm : (Ty.ref (.array E)).mapFree = true) (hp : p = .uint) (x : Var) :
    Premise.Runs m (.assignLocal i (.mlen b hp))
      (.captureMV x b (.assignLocal i.there (.mlen (.var .here hm) hp))) σ := by
  subst hp
  refine Premise.sound_captureMVSim σ (fun r hr => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .mem _) (some r) (TRun.assignLocal_pushT σ (t := .mem _) (some r) i _
      (.mlen b rfl) ?_)
    simp only [Val.evalT, hr]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.assignLocal i _ σ).map _ = _
    simp only [TRun.assignLocal, Val.evalT, hh]; rfl

/-- `binopUnfoldLeft`: `⟨[ v = nse ⊕ e; ]⟩ ⇝ ⟨[ T se = nse; v = se ⊕ e; ]⟩`. -/
theorem sound_binopUnfoldLeft {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a b : Val C Γ p') (x : Var) :
    Premise.Runs m (.assignLocal i (.binop op ha hq a b))
      (.capture p' x a (.assignLocal i.there (.binop op ha hq (.simple (.local .here)) b.up))) σ := by
  subst hq
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .val p') v (TRun.assignLocal_pushT σ (t := .val p') v i _
      (.binop op ha rfl a b) ?_)
    simp only [Val.evalT, Val.evalT_up, hv]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.assignLocal i _ σ).map _ = _
    simp only [TRun.assignLocal, Val.evalT, hh]; rfl

/-- `unopCapture`: `⟨[ v = ⊖nse; ]⟩ ⇝ ⟨[ T se = nse; v = ⊖se; ]⟩`. -/
theorem sound_unopCapture {p p' : PrimTy} (i : Idx Γ (.val p)) (op : UnOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Val C Γ p') (x : Var) :
    Premise.Runs m (.assignLocal i (.unop op ha hq a))
      (.capture p' x a (.assignLocal i.there (.unop op ha hq (.simple (.local .here))))) σ := by
  subst hq
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .val p') v (TRun.assignLocal_pushT σ (t := .val p') v i _
      (.unop op ha rfl a) ?_)
    simp only [Val.evalT, hv]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.assignLocal i _ σ).map _ = _
    simp only [TRun.assignLocal, Val.evalT, hh]; rfl

/-- `logicalAndShortCircuitRhs`: `v = se && nse;` is
`if (se) { v = nse; v = v && true; } else v = false;`. -/
theorem sound_shortAnd (i : Idx Γ (.val .bool)) (ha : BinOp.and.accepts .bool = true)
    (hq : BinOp.and.ret .bool = .bool) (a : Simple C Γ .bool) (b : Val C Γ .bool) :
    Premise.Runs m (.assignLocal i (.binop .and ha hq (.simple a) b))
      (.unfold (.cons (.ite (.simple a)
        (.cons (.assignLocal i b)
          (.cons (.assignLocal i (.binop .and rfl rfl (.simple (.local i)) (.simple (.bool true))))
            .nil))
        (.cons (.assignLocal i (.simple (.bool false))) .nil)) .nil) .refl) σ := by
  refine Premise.sound_unfold σ ?_
  rw [TRes.map_drop_self, Prog.runSt_single, Stmt.runSt_ite_simple, TRes.map_drop_self,
    TRes.map_drop_self, Prog.runSt_cons, Prog.runSt_single]
  simp only [Prog.runSt_single, Stmt.runSt_assignLocal, Val.evalT, ok_bind, BinOp.shortT]
  generalize hv : Simple.evalT σ a = av
  cases av
  · rfl
  · simp only [boolT, if_true]
    cases b.evalT σ with
    | error => rfl
    | ok y =>
      simp only [Except.map, Except.bind, Simple.evalT, State.get_setLocal]
      cases y <;> simp only [State.setLocal_setLocal] <;> rfl

/-- `logicalOrShortCircuitRhs`: `v = se || nse;` is
`if (se) v = true; else { v = nse; v = v || false; }`. -/
theorem sound_shortOr (i : Idx Γ (.val .bool)) (ha : BinOp.or.accepts .bool = true)
    (hq : BinOp.or.ret .bool = .bool) (a : Simple C Γ .bool) (b : Val C Γ .bool) :
    Premise.Runs m (.assignLocal i (.binop .or ha hq (.simple a) b))
      (.unfold (.cons (.ite (.simple a)
        (.cons (.assignLocal i (.simple (.bool true))) .nil)
        (.cons (.assignLocal i b)
          (.cons (.assignLocal i (.binop .or rfl rfl (.simple (.local i)) (.simple (.bool false))))
            .nil)))
        .nil) .refl) σ := by
  refine Premise.sound_unfold σ ?_
  rw [TRes.map_drop_self, Prog.runSt_single, Stmt.runSt_ite_simple, TRes.map_drop_self,
    TRes.map_drop_self, Prog.runSt_single, Prog.runSt_cons]
  simp only [Prog.runSt_single, Stmt.runSt_assignLocal, Val.evalT, ok_bind, BinOp.shortT]
  generalize hv : Simple.evalT σ a = av
  cases av
  · simp only [boolT, Bool.false_eq_true, if_false]
    cases b.evalT σ with
    | error => rfl
    | ok y =>
      simp only [Except.map, Except.bind, Simple.evalT, State.get_setLocal]
      cases y <;> simp only [State.setLocal_setLocal] <;> rfl
  · rfl

/-- `logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs` (`shortStep`). -/
theorem shortStep_sound {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (q : Premise C Γ Γ) (hs : shortStep i op ha hq a b = q) :
    Premise.Runs m (.assignLocal i (.binop op ha hq (.simple a) b)) q σ := by
  subst hs
  cases op <;> cases p' <;> subst hq <;>
    first
    | exact sound_shortAnd σ i ha rfl a b
    | exact sound_shortOr σ i ha rfl a b
    | exact sound_done_false σ _

/-- `binopUnfoldRight`, or the short circuit of `&&`/`||`. -/
theorem binopRight_sound (k : Nat) {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p')
    (q : Premise C Γ Γ)
    (hs : (if op.shortCircuits then shortStep i op ha hq a b
      else .capture p' (fse k) b
        (.assignLocal i.there (.binop op ha hq (.simple a.up) (.simple (.local .here))))) = q) :
    Premise.Runs m (.assignLocal i (.binop op ha hq (.simple a) b)) q σ := by
  cases hsc : op.shortCircuits
  · rw [hsc] at hs; cases hs; exact sound_binopRight σ i op ha hq hsc a b _
  · rw [hsc] at hs; exact shortStep_sound σ i op ha hq a b q hs

/-- **A local assigned** (`localStep`). -/
theorem localStep_sound (k : Nat) {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p)
    (q : Premise C Γ Γ) (hs : localStep k i v = q) :
    Premise.Runs m (.assignLocal i v) q σ := by
  cases v with
  | simple s => cases hs; exact sound_setLocal σ i _
  | modular op a b modulus => cases hs; exact sound_setLocal σ i _
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
    | _ => cases hs; exact sound_binopUnfoldLeft σ i op ha hq _ b _
  | unop op ha hq a =>
    cases a with
    | simple a => cases hs; exact sound_setLocal σ i _
    | _ => cases hs; exact sound_unopCapture σ i op ha hq _ _
  | ternary c a b => exact ternaryStep_sound σ k (.local i) c a b q hs
  | readMem l =>
    exact MHole.readStep_sound σ k (.local i)
      (fun _ _ _ _ _ h => by cases h; exact sound_setLocal σ i _)
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
theorem sound_rebindPushCapture {R : RefTy} (i : Idx Γ (.alias R))
    (b : SPath C Γ (.array (.ref R))) (hd : (Ty.ref R).defaultOkS = true) (x : Var) :
    Premise.Runs m (.rebind i (.push b hd))
      (.captureSP x b (.rebind i.there (.push (.alias .here) hd))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .alias _) (some q) (TRun.rebind_pushT σ (t := .alias _)
      (some q) i _ (.push b hd) ?_)
    simp only [ARhs.evalT, hq]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.rebind i (.push b hd) σ).map _ = _
    simp only [TRun.rebind, ARhs.evalT, hh]; rfl

/-- **An alias bound** (`rebindStep`). -/
theorem rebindStep_sound (k : Nat) {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R)
    (q : Premise C Γ Γ) (hs : rebindStep k i r = q) : Premise.Runs m (.rebind i r) q σ := by
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
    · split at hs
      · cases hs; exact sound_rebindPushMapping σ i b hd (by assumption)
      · cases hs; exact sound_rebindPush σ i b hd
    · cases hs; exact sound_rebindPushCapture σ i b hd _

/-! ### Compound assignment and `++`/`--` -/

/-- A statement on a compound target whose receiver is not simple: the
receiver bound first (`OpLoc.unfoldRecv`), when the statement read with the
bound receiver runs as before and halts where its receiver does. -/
theorem OpLoc.unfoldRecv_sound (k : Nat) {p : PrimTy}
    (s : {t : LTy} → OpLoc C (t :: Γ) p → Stmt C (t :: Γ) (t :: Γ)) (S : OpLoc C Γ p → Stmt C Γ Γ)
    (hpush : ∀ {t : LTy} (w : t.TDenote C σ.H) (l' : OpLoc C (t :: Γ) p) (l : OpLoc C Γ p),
      OpLoc.AgreeT σ w l' l → (s l').run (σ.push w) = pushedT σ w ((S l).run σ))
    (hstore : ∀ {sn : Name} (b : SPath C Γ (.struct sn)) f h e, b.resolveT σ = .error e →
      Stmt.runSt σ (S (.field b f h)) = .error e)
    (hindex : ∀ {R : RefTy} {kp : PrimTy} (it : IndexTy R kp (.prim p)) b ie e,
      b.resolveT σ = .error e → Stmt.runSt σ (S (.index it b ie)) = .error e)
    (hmfield : ∀ {sn : Name} (b : MPath C Γ (.struct sn)) f h e, b.mvalT σ = .error e →
      Stmt.runSt σ (S (.mfield b f h)) = .error e)
    (hmindex : ∀ {R : RefTy} (a : ArrTy R (.prim p)) b ie e, b.mvalT σ = .error e →
      Stmt.runSt σ (S (.mindex a b ie)) = .error e)
    (l : OpLoc C Γ p) (q : Premise C Γ Γ) (hq : l.unfoldRecv k s = some q) :
    Premise.Runs m (S l) q σ := by
  cases l with
  | field b f h =>
    simp only [OpLoc.unfoldRecv] at hq
    split at hq
    · cases hq
    · cases hq
      refine Premise.sound_captureSPSim σ (fun r hr => ?_) (fun e he _ => ?_)
      · exact runSt_pushed σ (t := .alias _) (some r)
          (hpush (some r) (.field (.alias .here) f h) (.field b f h) (.field f h (by rw [hr]; rfl)))
      · exact TRes.Sim.err_refl (hstore b f h e he)
  | index it b ie =>
    simp only [OpLoc.unfoldRecv] at hq
    split at hq
    · cases hq
    · cases hq
      refine Premise.sound_captureSPSim σ (fun r hr => ?_) (fun e he _ => ?_)
      · exact runSt_pushed σ (t := .alias _) (some r) (hpush (some r) (.index it (.alias .here) ie.up) (.index it b ie)
          (.index it (by rw [hr]; rfl) (Simple.evalT_up σ _ ie)))
      · exact TRes.Sim.err_refl (hindex it b ie e he)
  | mfield b f h =>
    cases b with
    | var => cases hq
    | loc l =>
      cases hq
      refine Premise.sound_captureMVSim σ (fun r hr => ?_) (fun e he _ => ?_)
      · exact runSt_pushed σ (t := .mem _) (some r) (hpush (some r)
          (.mfield (.var .here (MPath.loc l).mapFree) f h) (.mfield (.loc l) f h)
          (.mfield f h (by rw [hr]; rfl)))
      · exact TRes.Sim.err_refl (hmfield _ f h e he)
  | mindex a b ie =>
    cases b with
    | var => cases hq
    | loc l =>
      cases hq
      refine Premise.sound_captureMVSim σ (fun r hr => ?_) (fun e he _ => ?_)
      · exact runSt_pushed σ (t := .mem _) (some r) (hpush (some r)
          (.mindex a (.var .here (MPath.loc l).mapFree) ie.up) (.mindex a (.loc l) ie)
          (.mindex a (by rw [hr]; rfl) (Simple.evalT_up σ _ ie)))
      · exact TRes.Sim.err_refl (hmindex a _ ie e he)
  | _ => cases hq

/-- `compoundAssignValueRhsCapture`: the source captured first. -/
theorem sound_opCapture {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) (x : Var) :
    Premise.Runs m (.opAssign op hop hp l r)
      (.capture p x r (.opAssign op hop hp l.up (.simple (.local .here)))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact runSt_pushed σ (t := .val p) v (TRun.opAssign_pushT σ (t := .val p) v op
      (OpLoc.AgreeT.of_up (t := .val p) σ v l) _ r (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.opAssign op l r σ).map _ = _
    simp only [TRun.opAssign, hh]; rfl

/-- **A compound assignment** (`opStep`). -/
theorem opStep_sound (k : Nat) {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) (q : Premise C Γ Γ)
    (hs : opStep k op hop hp l r = q) : Premise.Runs m (.opAssign op hop hp l r) q σ := by
  cases r with
  | simple se =>
    simp only [opStep] at hs
    split at hs
    · rename_i q' hq'
      cases hs
      refine OpLoc.unfoldRecv_sound σ k (fun l' => .opAssign op hop hp l' (.simple se.up))
        (fun l => .opAssign op hop hp l (.simple se)) (fun w l' l hl => ?_)
        (fun b f h e he => ?_) (fun it b ie e he => ?_) (fun b f h e he => ?_)
        (fun a b ie e he => ?_) l _ hq'
      · exact TRun.opAssign_pushT σ w op hl _ _ (by simp only [Val.evalT, Simple.evalT_up])
      all_goals
        show (TRun.opAssign op _ (.simple se) σ).map _ = _
        simp only [TRun.opAssign, Val.evalT, ok_bind, OpLoc.storeT, Loc.resolveT, MLoc.addrT, he]
        rfl
    · cases hs; exact sound_opAssign σ op hop hp l se
  | _ => cases hs; exact sound_opCapture σ op hop hp l _ _

/-- **`l++;`** (`incStep`). -/
theorem incStep_sound (k : Nat) {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    (l : OpLoc C Γ p) (q : Premise C Γ Γ) (hs : incStep k op hp l = q) :
    Premise.Runs m (.incDec op hp l) q σ := by
  simp only [incStep] at hs
  split at hs
  · rename_i q' hq'
    cases hs
    refine OpLoc.unfoldRecv_sound σ k (fun l' => .incDec op hp l') (fun l => .incDec op hp l)
      (fun w l' l hl => ?_) (fun b f h e he => ?_) (fun it b ie e he => ?_)
      (fun b f h e he => ?_) (fun a b ie e he => ?_) l _ hq'
    · exact TRun.incDec_pushT σ w op hl
    all_goals
      show (TRun.incDec op _ σ).map _ = _
      simp only [TRun.incDec, OpLoc.bumpT, Loc.resolveT, MLoc.addrT, he]
      rfl
  · cases hs; exact sound_incDec σ op hp l

end Local

end Solidity
