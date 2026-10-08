import Solidity.Calculus.Core.SoundCapture

/-!
# Soundness of the storage arms

`Calculus/Core/Arms.lean`'s `assignStep`, `copyStep`, `assignFromMemStep`,
`deleteStep`, `pushStep` and `popStep`, each sound in the shape of
`Calculus/Core/SoundKit.lean`.  A rule that captures several parts
(`T se = e; T storage sp = b; T ie = i; sp[ie] = se;`) runs them as a block
(`Prog.run_declLocal_cons` and its kin), its statement read on the pushed
states by the push lemmas, one push at a time.  Where the rule captures
the target before the source the statement reads the other way round, and
the two halt alike (`Res.Sim`).
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

/-! ## Blocks of captures -/

section Blocks

variable {Γ : Ctx} (σ : State C Γ)

theorem Prog.run_declLocal_cons {Γ' : Ctx} (p : PrimTy) (x : Var) (e : Val C Γ p)
    (P : Prog C (.val p :: Γ) Γ') :
    Prog.run σ (.cons (.declLocal p x (some e)) P) = e.eval σ >>= fun v => Prog.run (σ.push v) P := by
  rw [Prog.run_cons, Stmt.run_declLocal]
  simp only [Run.declLocal]
  cases e.eval σ <;> rfl

theorem Prog.run_declStorage_cons {Γ' : Ctx} {R : RefTy} (x : Var) (b : SPath C Γ (.ref R))
    (P : Prog C (.alias R :: Γ) Γ') :
    Prog.run σ (.cons (.declStorage R x (some (.path b))) P) =
      b.resolve σ >>= fun q => Prog.run (σ.push (t := .alias R) (some q)) P := by
  rw [Prog.run_cons, Stmt.run_declStorage]
  simp only [Run.declStorage, ARhs.eval, bind_assoc, pure_bind]
  cases b.resolve σ <;> rfl

theorem Prog.run_declMem_cons {Γ' : Ctx} {R : RefTy} (x : Var) (b : MPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (P : Prog C (.mem R :: Γ) Γ') :
    Prog.run σ (.cons (.declMem R x (some (.alias b)) rfl hm) P) =
      (do (← b.mval σ).asRef) >>= fun id => Prog.run (σ.push (t := .mem R) (some id)) P := by
  rw [Prog.run_cons, Stmt.run_declMem]
  simp only [Run.declMem, MRhs.eval, bind_assoc, pure_bind]
  cases b.mval σ with
  | error => rfl
  | ok mv => simp only [Res.bind_ok]; cases mv.asRef <;> rfl

theorem Res.map_bind' {α β γ : Type} (x : Res α) (f : α → Res β) (g : β → γ) :
    (x >>= f).map g = x >>= fun a => (f a).map g := by
  cases x <;> rfl

theorem pushed2_drop {t u : LTy} (w : t.Denote C) (w' : u.Denote C) (r : Res (State C Γ)) :
    (pushed (Γ := t :: Γ) w' (pushed w r)).map (State.drop (.push (.push .refl))) = r := by
  cases r <;> rfl

theorem pushed3_drop {t u v : LTy} (w : t.Denote C) (w' : u.Denote C) (w'' : v.Denote C)
    (r : Res (State C Γ)) :
    (pushed (Γ := u :: t :: Γ) w'' (pushed (Γ := t :: Γ) w' (pushed w r))).map
      (State.drop (.push (.push (.push .refl)))) = r := by
  cases r <;> rfl

/-- A halt alike to `h` from a run that does not panic and does not end. -/
theorem Res.Sim.err_of_not_ok {α : Type} {h : Halt} (hh : h ≠ .panic) {r : Res α} (hr : NoPanic r)
    (hn : ∀ a, r ≠ .ok a) : Res.Sim (.error h) r := by
  cases r with
  | ok a => exact absurd rfl (hn a)
  | error e => exact ⟨fun e' => absurd e' hh, fun e' => absurd (congrArg Except.error e') hr⟩

theorem Src.value_noPanic {T : Ty} (r : Src C Γ T) : NoPanic (r.value σ) := by
  cases r with
  | val v =>
    have := Val.eval_noPanic σ v
    simp only [Src.value]
    exact NoPanic.bind this fun _ _ => NoPanic.pure _
  | copy p hm =>
    simp only [Src.value]
    exact NoPanic.bind (SPath.resolve_noPanic σ p) fun _ _ => Solidity.State.findStorage_noPanic _ _ _

theorem MPath.mval_noPanic {T : Ty} (b : MPath C Γ T) : NoPanic (b.mval σ) := by
  cases b with
  | var i _ =>
    show NoPanic (memRef σ i >>= fun id => pure (MVal.ref id))
    exact NoPanic.bind (Tm.eval_noPanic σ (.pvI i)) fun _ _ => NoPanic.pure _
  | loc l =>
    show NoPanic (l.read σ)
    rw [← MLoc.eval_lower σ l]
    exact NoPanic.bind (Tm.eval_noPanic σ l.lower) fun _ _ => Solidity.readAddr_noPanic _ _

/-- What a copy out of memory reads first: the object, deep-copied. -/
theorem copyOut_noPanic {R : RefTy} (p : MPath C Γ (.ref R)) :
    NoPanic (do Semantics.copyMem σ.glob (.ref (← (← p.mval σ).asRef))) :=
  NoPanic.bind (MPath.mval_noPanic σ p) fun _ _ =>
    NoPanic.bind (Solidity.MVal.asRef_noPanic _) fun _ _ => Solidity.copyMem_noPanic _ _

end Blocks

/-! ## Storage writes -/

section Store

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- `storageFieldRead_unfold_rightSndResult`, `storageIndexRead_unfold_rightSndResult`:
the source bound to an alias first. -/
theorem sound_copyCapture {R : RefTy} (l : Loc C Γ (.ref R)) (p : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (x : Var) :
    Premise.Sound m (.assign l (.copy p hm)) (.captureSP x p (.assign l.up (.copy (.alias .here) hm))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_assign, Stmt.run_assign,
      Run.assign_push σ (t := .alias R) (some q) l.up _ l (.copy p hm) ?_ (Loc.resolve_up σ _ l),
      pushed_drop]
    simp only [Src.value, SPath.resolve_here, hq, Res.bind_ok, pure_bind, State.glob_push]
  · rw [Stmt.run_assign]
    simp only [Run.assign, Src.value, hh]
    exact Res.Sim.refl _

/-- **A copy into a target of simple parts** (`copyStep`). -/
theorem copyStep_sound (k : Nat) {R : RefTy} (l : Loc C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (p : SPath C Γ (.ref R)) (q : Premise C Γ Γ) (hs : copyStep k l hm p = some q) :
    Premise.Sound m (.assign l (.copy p hm)) q σ := by
  cases p with
  | alias y => cases hs; exact sound_save σ l _
  | loc l' =>
    exact SHole.readStep_sound σ k (.copy l hm) l'
      (fun _ _ _ e hq => by cases hq; subst e; exact sound_save σ l _)
      (fun _ _ _ _ _ hq => by cases hq; exact sound_copyCapture σ l _ hm _)
      (fun _ _ _ _ _ hq => by cases hq; exact sound_copyCapture σ l _ hm _) q hs

/-- `storageFieldWrite_unfold_leftFst`: `T se = e; T storage sp = b; sp.f = se;`. -/
theorem sound_fieldWriteUnfold (k : Nat) {s : Name} {p : PrimTy} (b : SPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.prim p)) (e : Val C Γ p) :
    Premise.Sound m (.assign (.field b f h) (.val e))
      (.unfold (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declStorage _ (fsp k) (some (.path b.up)))
          (.cons (.assign (.field (.alias .here) f h) (.val (.simple (.local (.there .here))))) .nil)))
      (.push (.push .refl))) σ := by
  refine Premise.Sound.unfoldSim (Res.Sim.of_eq ?_)
  rw [Prog.run_declLocal_cons, Res.map_bind']
  rw [Stmt.run_assign]
  cases he : e.eval σ with
  | error h' => simp only [Run.assign, Src.value, he]; rfl
  | ok v =>
    simp only [Res.bind_ok]
    rw [Prog.run_declStorage_cons, Res.map_bind', SPath.resolve_up]
    cases hb : b.resolve σ with
    | error h' => simp only [Run.assign, Src.value, he, Loc.resolve, hb, Res.bind_ok, pure_bind]; rfl
    | ok q =>
      simp only [Res.bind_ok]
      rw [Prog.run_single, Stmt.run_assign,
        Run.assign_push (σ.push (t := .val p) v) (t := .alias _) (some q) _ _
          (.field b.up f h) (.val (.simple (.local .here))) rfl
          (by simp only [Loc.resolve, SPath.resolve_here, SPath.resolve_up, hb, Res.bind_ok, pure_bind]),
        Run.assign_push σ (t := .val p) v (.field b.up f h) (.val (.simple (.local .here)))
          (.field b f h) (.val e)
          (by simp only [Src.value, Val.eval, Simple.eval_here, he, Res.bind_ok, pure_bind])
          (Loc.resolve_up σ _ (.field b f h)),
        pushed2_drop]

/-- `storageFieldWriteStorageRef_unfold_leftFst`: the receiver bound first;
the statement reads the source first. -/
theorem sound_fieldWriteRefUnfold {s : Name} {R : RefTy} (b : SPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.ref R)) (p : SPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (x : Var) :
    Premise.Sound m (.assign (.field b f h) (.copy p hm))
      (.captureSP x b (.assign (.field (.alias .here) f h) (.copy p.up hm))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h' hh hp => ?_)
  · rw [Stmt.run_assign, Stmt.run_assign,
      Run.assign_push σ (t := .alias _) (some q) (.field (.alias .here) f h) (.copy p.up hm)
        (.field b f h) (.copy p hm) (Src.value_up σ _ (.copy p hm))
        (by simp only [Loc.resolve, SPath.resolve_here, hq, Res.bind_ok, pure_bind]),
      pushed_drop]
  · rw [Stmt.run_assign]
    simp only [Run.assign]
    refine Res.Sim.err_bind (Src.value_noPanic σ _) hp fun _ _ => ?_
    simp only [Loc.resolve, hh]
    exact Res.Sim.refl _

/-- `storageIndexWriteCaptureAllComplexRecv`, `…NonSimpleIndex`:
`T se = e; T storage sp = b; T ie = i; sp[ie] = se;`. -/
theorem sound_indexCaptureAll (k : Nat) {R : RefTy} {kp p : PrimTy} (it : IndexTy R kp (.prim p))
    (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (e : Val C Γ p) :
    Premise.Sound m (.assign (.index it b i) (.val e)) (indexCaptureAll k it b i e) σ := by
  refine Premise.Sound.unfoldSim (Res.Sim.of_eq ?_)
  rw [Prog.run_declLocal_cons, Res.map_bind', Stmt.run_assign]
  cases he : e.eval σ with
  | error h' => simp only [Run.assign, Src.value, he]; rfl
  | ok v =>
    simp only [Res.bind_ok]
    rw [Prog.run_declStorage_cons, Res.map_bind', SPath.resolve_up]
    cases hb : b.resolve σ with
    | error h' => simp only [Run.assign, Src.value, he, Loc.resolve, hb, Res.bind_ok, pure_bind]; rfl
    | ok q =>
      simp only [Res.bind_ok]
      rw [Prog.run_declLocal_cons, Res.map_bind', Val.eval_up, Val.eval_up]
      cases hi : i.eval σ with
      | error h' =>
        simp only [Run.assign, Src.value, he, Loc.resolve, hb, hi, Res.bind_ok, pure_bind]; rfl
      | ok n =>
        simp only [Res.bind_ok]
        rw [Prog.run_single, Stmt.run_assign,
          Run.assign_push ((σ.push (t := .val p) v).push (t := .alias R) (some q)) (t := .val kp) n
            _ _ (.index it (.alias .here) i.up.up) (.val (.simple (.local (.there .here)))) rfl
            (by simp only [Loc.resolve, Val.eval, Simple.eval_here, Val.eval_up, hi, State.glob_push]
                rfl),
          Run.assign_push (σ.push (t := .val p) v) (t := .alias R) (some q)
            (.index it (.alias .here) i.up.up) (.val (.simple (.local (.there .here))))
            (.index it b.up i.up) (.val (.simple (.local .here))) rfl
            (by simp only [Loc.resolve, SPath.resolve_here, SPath.resolve_up, Val.eval_up, hb,
                  State.glob_push, Res.bind_ok, pure_bind]),
          Run.assign_push σ (t := .val p) v (.index it b.up i.up) (.val (.simple (.local .here)))
            (.index it b i) (.val e)
            (by simp only [Src.value, Val.eval, Simple.eval_here, he, Res.bind_ok, pure_bind])
            (Loc.resolve_up σ _ (.index it b i)),
          pushed3_drop]

/-- `storageIndexWriteStorageRefCaptureAllComplexRecv`, `…NonSimpleIndex`:
`T storage sp = b; T ie = i; sp[ie] = path;`; the statement reads the source
first. -/
theorem sound_indexRefCaptureAll (k : Nat) {R R' : RefTy} {kp : PrimTy} (it : IndexTy R kp (.ref R'))
    (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (p : SPath C Γ (.ref R'))
    (hm : (Ty.ref R').mapFree = true) :
    Premise.Sound m (.assign (.index it b i) (.copy p hm)) (indexRefCaptureAll k it b i p hm) σ := by
  refine Premise.Sound.unfoldSim ?_
  rw [Prog.run_declStorage_cons, Res.map_bind', Stmt.run_assign]
  cases hb : b.resolve σ with
  | error h' =>
    refine Res.Sim.err_bind (Src.value_noPanic σ _) (fun e => SPath.resolve_noPanic σ b (e ▸ hb))
      fun _ _ => ?_
    simp only [Loc.resolve, hb]
    exact Res.Sim.refl _
  | ok q =>
    simp only [Res.bind_ok]
    rw [Prog.run_declLocal_cons, Res.map_bind', Val.eval_up]
    cases hi : i.eval σ with
    | error h' =>
      refine Res.Sim.err_bind (Src.value_noPanic σ _) (Val.eval_err_ne σ hi) fun _ _ => ?_
      simp only [Loc.resolve, hb, hi, Res.bind_ok]
      exact Res.Sim.refl _
    | ok n =>
      simp only [Res.bind_ok]
      refine Res.Sim.of_eq ?_
      rw [Prog.run_single, Stmt.run_assign,
        Run.assign_push (σ.push (t := .alias R) (some q)) (t := .val kp) n
          (.index it (.alias (.there .here)) (.simple (.local .here))) (.copy p.up.up hm)
          (.index it (.alias .here) i.up) (.copy p.up hm) (Src.value_up _ _ (.copy p.up hm))
          (by simp only [Loc.resolve, Val.eval, Simple.eval_here, Val.eval_up, hi, State.glob_push]
              rfl),
        Run.assign_push σ (t := .alias R) (some q) (.index it (.alias .here) i.up) (.copy p.up hm)
          (.index it b i) (.copy p hm) (Src.value_up σ _ (.copy p hm))
          (by simp only [Loc.resolve, SPath.resolve_here, Val.eval_up, hb, State.glob_push,
                Res.bind_ok, pure_bind]),
        pushed2_drop]

/-- **A storage write** (`assignStep`). -/
theorem assignStep_sound (k : Nat) {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) (q : Premise C Γ Γ)
    (hs : assignStep k l r = some q) : Premise.Sound m (.assign l r) q σ := by
  cases l with
  | root rn h =>
    cases r with
    | val e =>
      exact VHole.step_sound σ k (.store (.root rn h)) (fun _ _ hq => by cases hq; exact sound_save σ _ _)
        e q hs
    | copy p hm =>
      cases p with
      | alias j => cases hs; exact sound_save σ _ _
      | loc l' =>
        exact SHole.readStep_sound σ k (.copy (.root rn h) hm) l'
          (fun _ _ _ e hq => by cases hq; subst e; exact sound_save σ _ _)
          (fun _ _ _ _ e hq => by cases hq; subst e; exact sound_save σ _ _)
          (fun _ _ _ _ e hq => by cases hq; subst e; exact sound_save σ _ _) q hs
  | field b f h =>
    cases r with
    | val e =>
      simp only [assignStep] at hs
      split at hs
      · exact VHole.step_sound σ k (.store (.field b f h))
          (fun _ _ hq => by cases hq; exact sound_save σ _ _) e q hs
      · exact VHole.lower_sound σ k (.store (.field b f h)) e
          (fun _ hq => by cases hq; exact sound_fieldWriteUnfold σ k b f h e) q hs
    | copy p hm =>
      simp only [assignStep] at hs
      split at hs
      · exact copyStep_sound σ k (.field b f h) hm p q hs
      · cases hs; exact sound_fieldWriteRefUnfold σ b f h p hm _
  | index it b i =>
    cases r with
    | val e =>
      simp only [assignStep] at hs
      split at hs
      · cases i with
        | simple ie =>
          exact VHole.step_sound σ k (.store (.index it b (.simple ie)))
            (fun _ _ hq => by cases hq; exact sound_save σ _ _) e q hs
        | _ =>
          exact VHole.lower_sound σ k (.store (.index it b _)) e
            (fun _ hq => by cases hq; exact sound_indexCaptureAll σ k it b _ e) q hs
      · exact VHole.lower_sound σ k (.store (.index it b i)) e
          (fun _ hq => by cases hq; exact sound_indexCaptureAll σ k it b i e) q hs
    | copy p hm =>
      simp only [assignStep] at hs
      split at hs
      · cases i with
        | simple ie => exact copyStep_sound σ k (.index it b (.simple ie)) hm p q hs
        | _ => cases hs; exact sound_indexRefCaptureAll σ k it b _ p hm
      · cases hs; exact sound_indexRefCaptureAll σ k it b i p hm

/-- `memoryToStorageField_unfold_leftFst`: the receiver bound first; the
statement reads the memory source first. -/
theorem sound_fromMemFieldUnfold {s : Name} {R : RefTy} (b : SPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.ref R)) (p : MPath C Γ (.ref R)) (x : Var) :
    Premise.Sound m (.assignFromMem (.field b f h) p)
      (.captureSP x b (.assignFromMem (.field (.alias .here) f h) p.up)) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h' hh hp => ?_)
  · rw [Stmt.run_assignFromMem, Stmt.run_assignFromMem,
      Run.assignFromMem_push σ (t := .alias _) (some q) (.field (.alias .here) f h) (.field b f h) p.up p
        (MPath.mval_up σ _ p) (by simp only [Loc.resolve, SPath.resolve_here, hq, Res.bind_ok, pure_bind]),
      pushed_drop]
  · rw [Stmt.run_assignFromMem]
    simp only [Run.assignFromMem]
    refine Res.Sim.err_bind (MPath.mval_noPanic σ p) hp fun _ _ =>
      Res.Sim.err_bind (Solidity.MVal.asRef_noPanic _) hp fun _ _ =>
        Res.Sim.err_bind (Solidity.copyMem_noPanic _ _) hp fun _ _ => ?_
    simp only [Loc.resolve, hh]
    exact Res.Sim.refl _

/-- `memoryToStorageIndexCaptureAllComplexRecv`, `…NonSimpleIndex`:
`T storage sp = b; T ie = i; sp[ie] = mpath;`; the statement reads the
memory source first. -/
theorem sound_fromMemIndexUnfold (k : Nat) {R R' : RefTy} {kp : PrimTy} (it : IndexTy R kp (.ref R'))
    (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (p : MPath C Γ (.ref R')) :
    Premise.Sound m (.assignFromMem (.index it b i) p)
      (.unfold (.cons (.declStorage R (fsp k) (some (.path b)))
        (.cons (.declLocal kp (fie k) (some i.up))
        (.cons (.assignFromMem (.index it (.alias (.there .here)) (.simple (.local .here))) p.up.up)
          .nil))) (.push (.push .refl))) σ := by
  refine Premise.Sound.unfoldSim ?_
  rw [Prog.run_declStorage_cons, Res.map_bind', Stmt.run_assignFromMem]
  cases hb : b.resolve σ with
  | error h' =>
    have hp : h' ≠ .panic := fun e => SPath.resolve_noPanic σ b (e ▸ hb)
    simp only [Run.assignFromMem]
    refine Res.Sim.err_bind (MPath.mval_noPanic σ p) hp fun _ _ =>
      Res.Sim.err_bind (Solidity.MVal.asRef_noPanic _) hp fun _ _ =>
        Res.Sim.err_bind (Solidity.copyMem_noPanic _ _) hp fun _ _ => ?_
    simp only [Loc.resolve, hb]
    exact Res.Sim.refl _
  | ok q =>
    simp only [Res.bind_ok]
    rw [Prog.run_declLocal_cons, Res.map_bind', Val.eval_up]
    cases hi : i.eval σ with
    | error h' =>
      have hp := Val.eval_err_ne σ hi
      simp only [Run.assignFromMem]
      refine Res.Sim.err_bind (MPath.mval_noPanic σ p) hp fun _ _ =>
        Res.Sim.err_bind (Solidity.MVal.asRef_noPanic _) hp fun _ _ =>
          Res.Sim.err_bind (Solidity.copyMem_noPanic _ _) hp fun _ _ => ?_
      simp only [Loc.resolve, hb, hi, Res.bind_ok]
      exact Res.Sim.refl _
    | ok n =>
      simp only [Res.bind_ok]
      refine Res.Sim.of_eq ?_
      rw [Prog.run_single, Stmt.run_assignFromMem,
        Run.assignFromMem_push (σ.push (t := .alias R) (some q)) (t := .val kp) n
          (.index it (.alias (.there .here)) (.simple (.local .here))) (.index it (.alias .here) i.up)
          p.up.up p.up (MPath.mval_up _ _ p.up)
          (by simp only [Loc.resolve, Val.eval, Simple.eval_here, Val.eval_up, hi, State.glob_push]
              rfl),
        Run.assignFromMem_push σ (t := .alias R) (some q) (.index it (.alias .here) i.up)
          (.index it b i) p.up p (MPath.mval_up σ _ p)
          (by simp only [Loc.resolve, SPath.resolve_here, Val.eval_up, hb, State.glob_push,
                Res.bind_ok, pure_bind]),
        pushed2_drop]

/-- **A storage location written from memory** (`assignFromMemStep`). -/
theorem assignFromMemStep_sound (k : Nat) {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R))
    (q : Premise C Γ Γ) (hs : assignFromMemStep k l p = some q) :
    Premise.Sound m (.assignFromMem l p) q σ := by
  cases l with
  | root rn h => cases hs; exact sound_saveMem σ _ p
  | field b f h =>
    simp only [assignFromMemStep] at hs
    split at hs
    · cases hs; exact sound_saveMem σ _ p
    · cases hs; exact sound_fromMemFieldUnfold σ b f h p _
  | index it b i =>
    simp only [assignFromMemStep] at hs
    split at hs
    · cases i with
      | simple ie => cases hs; exact sound_saveMem σ _ p
      | _ => cases hs; exact sound_fromMemIndexUnfold σ k it b _ p
    · cases hs; exact sound_fromMemIndexUnfold σ k it b i p

/-! ### `delete` -/

/-- `storageFieldDelete_unfold_leftFst`, `storageIndexDelete_unfold_leftFst`:
the receiver bound first. -/
theorem sound_deleteRecvCapture {T : Ty} (l' : Loc C (.alias R :: Γ) T) (b : SPath C Γ (.ref R))
    (l : Loc C Γ T) (x : Var)
    (hl : ∀ q, b.resolve σ = .ok q → l'.resolve (σ.push (t := .alias R) (some q)) = l.resolve σ)
    (herr : ∀ h, b.resolve σ = .error h → l.resolve σ = .error h) :
    Premise.Sound m (.delete l) (.captureSP x b (.delete l')) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_delete, Stmt.run_delete, Run.delete_push σ (t := .alias R) (some q) l' l (hl q hq),
      pushed_drop]
  · rw [Stmt.run_delete]
    simp only [Run.delete, herr h hh]
    exact Res.Sim.refl _

/-- `storageIndexDeleteNonSimpleIndexCapture`: the index captured; the
statement reads the receiver first. -/
theorem sound_deleteIndexCapture {R : RefTy} {kp : PrimTy} {T : Ty} (it : IndexTy R kp T)
    (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.Sound m (.delete (.index it b i))
      (.capture kp x i (.delete (.index it b.up (.simple (.local .here))))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · rw [Stmt.run_delete, Stmt.run_delete,
      Run.delete_push σ (t := .val kp) v (.index it b.up (.simple (.local .here))) (.index it b i)
        (by simp only [Loc.resolve, SPath.resolve_up, Val.eval, Simple.eval_here, hv, State.glob_push]
            rfl),
      pushed_drop]
  · rw [Stmt.run_delete]
    simp only [Run.delete, Loc.resolve, bind_assoc]
    refine Res.Sim.err_bind (SPath.resolve_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact Res.Sim.refl _

/-- **`delete l;`** (`deleteStep`). -/
theorem deleteStep_sound (k : Nat) {T : Ty} (l : Loc C Γ T) (q : Premise C Γ Γ)
    (hs : deleteStep k l = some q) : Premise.Sound m (.delete l) q σ := by
  cases l with
  | root rn h => cases hs; exact sound_delAt σ _
  | field b f h =>
    simp only [deleteStep] at hs
    split at hs
    · cases hs; exact sound_delAt σ _
    · cases hs
      exact sound_deleteRecvCapture σ (.field (.alias .here) f h) b (.field b f h) _
        (fun q hq => by simp only [Loc.resolve, SPath.resolve_here, hq, Res.bind_ok, pure_bind])
        (fun e he => by simp only [Loc.resolve, he]; rfl)
  | index it b i =>
    simp only [deleteStep] at hs
    split at hs
    · cases i with
      | simple ie => cases hs; exact sound_delAt σ _
      | _ => cases hs; exact sound_deleteIndexCapture σ it b _ _
    · cases hs
      exact sound_deleteRecvCapture σ (.index it (.alias .here) i.up) b (.index it b i) _
        (fun q hq => by
          simp only [Loc.resolve, SPath.resolve_here, hq, Val.eval_up, State.glob_push, Res.bind_ok,
            pure_bind])
        (fun e he => by simp only [Loc.resolve, he]; rfl)

/-! ### Push and pop -/

/-- `storagePushValue_unfold_rightSndArgument`: the argument captured; the
statement reads the receiver and the array first. -/
theorem sound_pushCapture {p : PrimTy} (b : SPath C Γ (.array (.prim p))) (e : Val C Γ p)
    (hd : ((some (Src.val e)).isSome || (Ty.prim p).defaultOkS) = true) (x : Var) :
    Premise.Sound m (.push b (some (.val e)) hd)
      (.capture p x e (.push b.up (some (.val (.simple (.local .here)))) rfl)) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · rw [Stmt.run_push, Stmt.run_push,
      Run.push_push σ (t := .val p) v b.up b _ (some (.val e)) (SPath.resolve_up σ _ b)
        (by funext slot; simp only [Src.pushVal, Src.value, Val.eval, Simple.eval_here, hv]; rfl),
      pushed_drop]
  · rw [Stmt.run_push]
    simp only [Run.push]
    refine Res.Sim.err_bind (SPath.resolve_noPanic σ b) hp fun q _ => ?_
    refine Res.Sim.err_of_not_ok hp ?_ fun a ha => ?_
    · rw [NoPanic.map]
      exact Solidity.pushAt_noPanic _ _ _ _ fun _ => by
        simp only [Src.pushVal, Src.value, hh]; exact fun e => hp (Except.error.inj e)
    · simp only [pushAt, Src.pushVal, Src.value, hh] at ha
      revert ha
      cases σ.glob.findStorage q.1 q.2 with
      | error => exact nofun
      | ok sv => cases sv <;> exact nofun

/-- `storagePush_unfold_leftFstReceiver`, `storagePushValue_unfold_leftFstReceiver`:
the receiver bound first. -/
theorem sound_pushRecvCapture {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (hd' : ((v.map Src.up).isSome || E.defaultOkS) = true)
    (x : Var) :
    Premise.Sound m (.push b v hd) (.captureSP x b (.push (.alias .here) (v.map Src.up) hd')) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_push, Stmt.run_push,
      Run.push_push σ (t := .alias _) (some q) (.alias .here) b _ v (by rw [hq]; rfl)
        (Src.pushVal_up σ _ v), pushed_drop]
  · rw [Stmt.run_push]
    simp only [Run.push, hh]
    exact Res.Sim.refl _

/-- **`b.push(v);`** (`pushStep`). -/
theorem pushStep_sound (k : Nat) {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (q : Premise C Γ Γ) (hs : pushStep k b v hd = some q) :
    Premise.Sound m (.push b v hd) q σ := by
  simp only [pushStep] at hs
  split at hs
  · cases v with
    | none =>
      simp only at hs
      split at hs
      · cases hs; exact sound_pushSlot σ b hd
      · cases hs; exact sound_extend σ b hd
    | some r =>
      cases r with
      | val e =>
        cases e with
        | simple se => cases hs; exact sound_pushSome σ b _ hd
        | _ => cases hs; exact sound_pushCapture σ b _ hd _
      | copy p hm => cases hs; exact sound_pushSome σ b _ hd
  · cases hs; exact sound_pushRecvCapture σ b v hd _ _

/-- `storagePop_unfold_leftFstReceiver`: the receiver bound first. -/
theorem sound_popCapture {E : Ty} (b : SPath C Γ (.array E)) (x : Var) :
    Premise.Sound m (.pop b) (.captureSP x b (.pop (.alias .here))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_pop, Stmt.run_pop,
      Run.pop_push σ (t := .alias _) (some q) (.alias .here) b (by rw [hq]; rfl), pushed_drop]
  · rw [Stmt.run_pop]
    simp only [Run.pop, hh]
    exact Res.Sim.refl _

/-- **`b.pop();`** (`popStep`). -/
theorem popStep_sound (k : Nat) {E : Ty} (b : SPath C Γ (.array E)) (q : Premise C Γ Γ)
    (hs : popStep k b = some q) : Premise.Sound m (.pop b) q σ := by
  simp only [popStep] at hs
  split at hs
  · have hp : Premise.Sound m (.pop b) (.upd1 (.storage (.app2 (if E.isMapping then .shrink else .pop)
        .storage b.lower))) σ := sound_pop σ b
    split at hs
    · rename_i hE
      cases hs
      rwa [show E.isMapping = true from hE, if_pos rfl] at hp
    · rename_i hE
      cases hs
      rwa [show E.isMapping = false from Bool.eq_false_iff.mpr hE, if_neg (by decide)] at hp
  · cases hs; exact sound_popCapture σ b _

end Store

end Solidity.Core
