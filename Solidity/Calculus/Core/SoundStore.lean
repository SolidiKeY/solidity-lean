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
      (do (← b.mval σ).asRef) >>= fun id => Prog.run (σ.push (t := .mem R) id) P := by
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

end Store

end Solidity.Core
