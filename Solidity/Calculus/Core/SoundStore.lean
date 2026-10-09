import Solidity.Calculus.Core.SoundCapture

/-!
# Soundness of the storage arms

`assignStep`, `copyStep`, `assignFromMemStep`, `deleteStep`, `pushStep` and
`popStep`, each `Premise.Sound` (`Calculus/Core/ProvesSound.lean`).  A rule
that captures several parts runs them as a block
(`Prog.trunSt_declLocal_cons` and its kin), its statement read on the pushed
states by the typed push lemmas (`Calculus/Core/SoundCapture.lean`), one
push at a time.

No arm carries a condition: a storage copy is on the bridge (no struct
repeats a member name, decision 16), and a push at the bound is exhausted,
which both modalities accept (`TRun.push_nd`, decision 15).
-/

namespace Solidity.Core
open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

/-! ## Blocks of captures -/

section Blocks

variable {Γ : Ctx} (σ : EState C Γ)

theorem Res.map_bind' {α β γ : Type} (x : Res α) (f : α → Res β) (g : β → γ) :
    (x >>= f).map g = x >>= fun a => (f a).map g := by
  cases x <;> rfl

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
    exact NoPanic.bind (SPath.resolve_noPanic σ p) fun _ _ => Semantics.State.findStorage_noPanic _ _ _

theorem MPath.mval_noPanic {T : Ty} (b : MPath C Γ T) : NoPanic (b.mval σ) := by
  cases b with
  | var i _ =>
    show NoPanic (memRef σ i >>= fun id => pure (MVal.ref id))
    exact NoPanic.bind (Tm.eval_noPanic σ (.pvI i)) fun _ _ => NoPanic.pure _
  | loc l =>
    show NoPanic (l.read σ)
    rw [← MLoc.eval_lower σ l]
    exact NoPanic.bind (Tm.eval_noPanic σ l.lower) fun _ _ => Solidity.readAddr_noPanic _ _

end Blocks

open Solidity (Modality)

/-! ## Blocks of captures -/

section Blocks

variable {Γ : Ctx} (σ : TState C Γ)

theorem Prog.trunSt_declLocal_cons {Γ' : Ctx} (p : PrimTy) (x : Var) (e : Val C Γ p)
    (P : Prog C (.val p :: Γ) Γ') :
    Prog.trunSt σ (.cons (.declLocal p x (some e)) P) =
      (e.evalT σ).bind fun v => Prog.trunSt (σ.push (t := .val p) v) P := by
  rw [Prog.trunSt_cons, Stmt.trunSt_declLocal]
  cases e.evalT σ <;> rfl

theorem Prog.trunSt_declStorage_cons {Γ' : Ctx} {R : RefTy} (x : Var) (b : SPath C Γ (.ref R))
    (P : Prog C (.alias R :: Γ) Γ') :
    Prog.trunSt σ (.cons (.declStorage R x (some (.path b))) P) =
      (b.resolveT σ).bind fun q => Prog.trunSt (σ.push (t := .alias R) (some q)) P := by
  rw [Prog.trunSt_cons, Stmt.trunSt_declStorage]
  cases b.resolveT σ <;> rfl

theorem Prog.trunSt_declMem_cons {Γ' : Ctx} {R : RefTy} (x : Var) (b : MPath C Γ (.ref R))
    (P : Prog C (.mem R :: Γ) Γ') :
    Prog.trunSt σ (.cons (.declMem R x (some (.alias b)) rfl b.mapFree) P) =
      (b.mvalT σ).bind fun r => Prog.trunSt (σ.push (t := .mem R) (some r)) P := by
  rw [Prog.trunSt_cons, Stmt.trunSt_declMem]
  cases b.mvalT σ <;> rfl

theorem TRes.map_bind' {α β γ : Type} (x : TRes α) (f : α → TRes β) (g : β → γ) :
    (x.bind f).map g = x.bind fun a => (f a).map g := by
  cases x <;> rfl

/-- Two locals pushed, then popped. -/
theorem pushedT2_drop {t u : LTy} (v : t.TDenote C σ.H) (w : u.TDenote C σ.H)
    (r : TRes (Out C σ.H Γ)) :
    ((pushedT (σ.push v) w (pushedT σ v r)).map (·.st)).map (TState.drop (.push (.push .refl))) =
      r.map (·.st) := by
  cases r <;> rfl

/-- Three locals pushed, then popped. -/
theorem pushedT3_drop {t u y : LTy} (v : t.TDenote C σ.H) (w : u.TDenote C σ.H)
    (z : y.TDenote C σ.H) (r : TRes (Out C σ.H Γ)) :
    ((pushedT ((σ.push v).push w) z (pushedT (σ.push v) w (pushedT σ v r))).map (·.st)).map
      (TState.drop (.push (.push (.push .refl)))) = r.map (·.st) := by
  cases r <;> rfl

/-- A revert alike to a halt from a run that does not panic and does not end. -/
theorem TRes.Sim.err_of_not_ok {α : Type} {h : THalt} (hh : h = .revert) {r : TRes α}
    (hr : r.NoPanic) (hn : ∀ a, r ≠ .ok a) : TRes.Sim (.error h) r :=
  TRes.Sim.err hh hr hn

end Blocks

/-! ## Storage writes -/

section Store

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `storageFieldRead_unfold_rightSndResult`, `storageIndexRead_unfold_rightSndResult`:
the source bound to an alias first. -/
theorem sound_copyCapture {R : RefTy} (l : Loc C Γ (.ref R)) (p : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (x : Var) :
    Premise.Runs m (.assign l (.copy p hm))
      (.captureSP x p (.assign l.up (.copy (.alias .here) hm))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ (t := .alias R) (some q) (TRun.assign_pushT σ (t := .alias R) (some q) l.up _ l
      (.copy p hm) ?_ (Loc.resolveT_up σ _ l))
    simp only [Src.valueT, hq]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.assign l (.copy p hm) σ).map _ = _
    simp only [TRun.assign, Src.valueT, hh]; rfl

/-- **A copy into a target of simple parts** (`copyStep`). -/
theorem copyStep_sound (k : Nat) {R : RefTy} (l : Loc C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (p : SPath C Γ (.ref R))
    (q : Premise C Γ Γ) (hs : copyStep k l hm p = some q) :
    Premise.Runs m (.assign l (.copy p hm)) q σ := by
  cases p with
  | alias y => cases hs; exact sound_save σ l _
  | loc l' =>
    exact SHole.readStep_sound σ k (.copy l hm) l'
      (fun _ _ _ e hq => by cases hq; subst e; exact sound_save σ l _)
      (fun _ _ _ _ _ hq => by cases hq; exact sound_copyCapture σ l _ hm _)
      (fun _ _ _ _ _ hq => by cases hq; exact sound_copyCapture σ l _ hm _) q hs

/-- `storageFieldWrite_unfold_leftFst`: `T se = e; T storage sp = b; sp.f = se;`. -/
theorem sound_fieldWriteUnfold (k : Nat) {s : Name} {p : PrimTy} (b : SPath C Γ (.struct s))
    (f : Name) (h : C.fieldType s f = some (.prim p)) (e : Val C Γ p) :
    Premise.Runs m (.assign (.field b f h) (.val e))
      (.unfold (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declStorage _ (fsp k) (some (.path b.up)))
          (.cons (.assign (.field (.alias .here) f h) (.val (.simple (.local (.there .here))))) .nil)))
      (.push (.push .refl))) σ := by
  refine Premise.sound_unfoldSim σ (TRes.Sim.of_eq ?_)
  rw [Prog.trunSt_declLocal_cons, TRes.map_bind']
  show _ = (TRun.assign (.field b f h) (.val e) σ).map _
  cases he : e.evalT σ with
  | error h' => simp only [TRun.assign, Src.valueT, he]; rfl
  | ok v =>
    show (Prog.trunSt (σ.push (t := .val p) v) _).map _ = _
    rw [Prog.trunSt_declStorage_cons, TRes.map_bind', SPath.resolveT_up]
    cases hb : b.resolveT σ with
    | error h' =>
      simp only [TRun.assign, Src.valueT, he, Loc.resolveT, hb, ok_bind]; rfl
    | ok q =>
      show (Prog.trunSt _ (.cons _ .nil)).map _ = _
      rw [Prog.trunSt_single]
      have h₁ := TRun.assign_pushT (σ.push (t := .val p) v) (t := .alias _) (some q)
        (.field (.alias .here) f h) (.val (.simple (.local (.there .here))))
        (.field b.up f h) (.val (.simple (.local .here))) rfl
        (by simp only [Loc.resolveT, SPath.resolveT_up, hb]; rfl)
      have h₂ := TRun.assign_pushT σ (t := .val p) v (.field b.up f h)
        (.val (.simple (.local .here))) (.field b f h) (.val e)
        (by simp only [Src.valueT, Val.evalT, he]; rfl) (Loc.resolveT_up σ _ (.field b f h))
      show (((TRun.assign _ _ _).map (·.st)).map _) = _
      rw [h₁, h₂]
      exact pushedT2_drop σ (t := .val p) (u := .alias (.struct s)) v (some q) _

/-- `storageFieldWriteStorageRef_unfold_leftFst`: the receiver bound first;
the statement reads the source first. -/
theorem sound_fieldWriteRefUnfold {s : Name} {R : RefTy} (b : SPath C Γ (.struct s)) (f : Name)
    (h : C.fieldType s f = some (.ref R)) (p : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (x : Var) :
    Premise.Runs m (.assign (.field b f h) (.copy p hm))
      (.captureSP x b (.assign (.field (.alias .here) f h) (.copy p.up hm))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h' hh hp => ?_)
  · refine trunSt_pushed σ (t := .alias (.struct s)) (some q) (TRun.assign_pushT σ (t := .alias _) (some q)
      (.field (.alias .here) f h) (.copy p.up hm) (.field b f h) (.copy p hm)
      (Src.valueT_up σ _ (.copy p hm)) ?_)
    simp only [Loc.resolveT, hq]; rfl
  · show TRes.Sim _ ((TRun.assign (.field b f h) (.copy p hm) σ).map _)
    simp only [TRun.assign, TRes.map_bind]
    refine TRes.Sim.err_bind (Src.valueT_noPanic σ _) hp fun _ _ => ?_
    simp only [Loc.resolveT, hh]
    exact TRes.Sim.refl _

/-- `storageIndexWriteCaptureAllComplexRecv`, `…NonSimpleIndex`:
`T se = e; T storage sp = b; T ie = i; sp[ie] = se;`. -/
theorem sound_indexCaptureAll (k : Nat) {R : RefTy} {kp p : PrimTy}
    (it : IndexTy R kp (.prim p)) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (e : Val C Γ p) :
    Premise.Runs m (.assign (.index it b i) (.val e)) (indexCaptureAll k it b i e) σ := by
  refine Premise.sound_unfoldSim σ (TRes.Sim.of_eq ?_)
  rw [Prog.trunSt_declLocal_cons, TRes.map_bind']
  show _ = (TRun.assign (.index it b i) (.val e) σ).map _
  cases he : e.evalT σ with
  | error h' => simp only [TRun.assign, Src.valueT, he]; rfl
  | ok v =>
    show (Prog.trunSt (σ.push (t := .val p) v) _).map _ = _
    rw [Prog.trunSt_declStorage_cons, TRes.map_bind', SPath.resolveT_up]
    cases hb : b.resolveT σ with
    | error h' => simp only [TRun.assign, Src.valueT, he, Loc.resolveT, hb, ok_bind]; rfl
    | ok q =>
      show (Prog.trunSt _ _).map _ = _
      rw [Prog.trunSt_declLocal_cons, TRes.map_bind', Val.evalT_up, Val.evalT_up]
      cases hi : i.evalT σ with
      | error h' =>
        simp only [TRun.assign, Src.valueT, he, Loc.resolveT, hb, hi, ok_bind]; rfl
      | ok n =>
        show (Prog.trunSt _ (.cons _ .nil)).map _ = _
        rw [Prog.trunSt_single]
        have h₁ := TRun.assign_pushT ((σ.push (t := .val p) v).push (t := .alias R) (some q))
          (t := .val kp) n (.index it (.alias (.there .here)) (.simple (.local .here)))
          (.val (.simple (.local (.there (.there .here))))) (.index it (.alias .here) i.up.up)
          (.val (.simple (.local (.there .here)))) rfl
          (by simp only [Loc.resolveT, Val.evalT_up, hi]; rfl)
        have h₂ := TRun.assign_pushT (σ.push (t := .val p) v) (t := .alias R) (some q)
          (.index it (.alias .here) i.up.up) (.val (.simple (.local (.there .here))))
          (.index it b.up i.up) (.val (.simple (.local .here))) rfl
          (by simp only [Loc.resolveT, SPath.resolveT_up, Val.evalT_up, hb]; rfl)
        have h₃ := TRun.assign_pushT σ (t := .val p) v (.index it b.up i.up)
          (.val (.simple (.local .here))) (.index it b i) (.val e)
          (by simp only [Src.valueT, Val.evalT, he]; rfl) (Loc.resolveT_up σ _ (.index it b i))
        show (((TRun.assign _ _ _).map (·.st)).map _) = _
        rw [h₁, h₂, h₃]
        exact pushedT3_drop σ (t := .val p) (u := .alias R) (y := .val kp) v (some q) n _

/-- `storageIndexWriteStorageRefCaptureAllComplexRecv`, `…NonSimpleIndex`:
`T storage sp = b; T ie = i; sp[ie] = path;`; the statement reads the source
first. -/
theorem sound_indexRefCaptureAll (k : Nat) {R R' : RefTy} {kp : PrimTy}
    (it : IndexTy R kp (.ref R')) (b : SPath C Γ (.ref R)) (i : Val C Γ kp)
    (p : SPath C Γ (.ref R')) (hm : (Ty.ref R').mapFree = true) :
    Premise.Runs m (.assign (.index it b i) (.copy p hm)) (indexRefCaptureAll k it b i p hm) σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [Prog.trunSt_declStorage_cons, TRes.map_bind']
  show TRes.Sim _ ((TRun.assign (.index it b i) (.copy p hm) σ).map _)
  cases hb : b.resolveT σ with
  | error h' =>
    have hp : h' = .revert := SPath.resolveT_revert σ b hb
    simp only [TRun.assign, TRes.map_bind]
    refine TRes.Sim.err_bind (Src.valueT_noPanic σ _) hp fun _ _ => ?_
    simp only [Loc.resolveT, hb]
    exact TRes.Sim.refl _
  | ok q =>
    show TRes.Sim ((Prog.trunSt _ _).map _) _
    rw [Prog.trunSt_declLocal_cons, TRes.map_bind', Val.evalT_up]
    cases hi : i.evalT σ with
    | error h' =>
      have hp : h' = .revert := Val.evalT_revert σ i hi
      simp only [TRun.assign, TRes.map_bind]
      refine TRes.Sim.err_bind (Src.valueT_noPanic σ _) hp fun _ _ => ?_
      simp only [Loc.resolveT, hb, hi, ok_bind]
      exact TRes.Sim.refl _
    | ok n =>
      refine TRes.Sim.of_eq ?_
      show (Prog.trunSt _ (.cons _ .nil)).map _ = _
      rw [Prog.trunSt_single]
      have h₁ := TRun.assign_pushT (σ.push (t := .alias R) (some q)) (t := .val kp) n
        (.index it (.alias (.there .here)) (.simple (.local .here))) (.copy p.up.up hm)
        (.index it (.alias .here) i.up) (.copy p.up hm) (Src.valueT_up _ _ (.copy p.up hm))
        (by simp only [Loc.resolveT, Val.evalT_up, hi]; rfl)
      have h₂ := TRun.assign_pushT σ (t := .alias R) (some q) (.index it (.alias .here) i.up)
        (.copy p.up hm) (.index it b i) (.copy p hm) (Src.valueT_up σ _ (.copy p hm))
        (by simp only [Loc.resolveT, Val.evalT_up, hb]; rfl)
      show (((TRun.assign _ _ _).map (·.st)).map _) = _
      rw [h₁, h₂]
      exact pushedT2_drop σ (t := .alias R) (u := .val kp) (some q) n _

/-- **A storage write** (`assignStep`). -/
theorem assignStep_sound (k : Nat) {T : Ty} (l : Loc C Γ T) (r : Src C Γ T)
    (q : Premise C Γ Γ) (hs : assignStep k l r = some q) :
    Premise.Runs m (.assign l r) q σ := by
  cases l with
  | root rn h =>
    cases r with
    | val e =>
      exact VHole.step_sound σ k (.store (.root rn h))
        (fun _ _ hq => by cases hq; exact sound_save σ _ _) e q hs
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
    Premise.Runs m (.assignFromMem (.field b f h) p)
      (.captureSP x b (.assignFromMem (.field (.alias .here) f h) p.up)) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h' hh hp => ?_)
  · refine trunSt_pushed σ (t := .alias (.struct s)) (some q) (TRun.assignFromMem_pushT σ
      (t := .alias _) (some q) (.field (.alias .here) f h) (.field b f h) p.up p
      (MPath.mvalT_up σ _ p) ?_)
    simp only [Loc.resolveT, hq]; rfl
  · show TRes.Sim _ ((TRun.assignFromMem (.field b f h) p σ).map _)
    simp only [TRun.assignFromMem, TRes.map_bind]
    refine TRes.Sim.err_bind (MPath.mvalT_noPanic σ p) hp fun _ _ => ?_
    simp only [Loc.resolveT, hh]
    exact TRes.Sim.refl _

/-- `memoryToStorageIndexCaptureAllComplexRecv`, `…NonSimpleIndex`:
`T storage sp = b; T ie = i; sp[ie] = mpath;`; the statement reads the
memory source first. -/
theorem sound_fromMemIndexUnfold (k : Nat) {R R' : RefTy} {kp : PrimTy}
    (it : IndexTy R kp (.ref R')) (b : SPath C Γ (.ref R)) (i : Val C Γ kp)
    (p : MPath C Γ (.ref R')) :
    Premise.Runs m (.assignFromMem (.index it b i) p)
      (.unfold (.cons (.declStorage R (fsp k) (some (.path b)))
        (.cons (.declLocal kp (fie k) (some i.up))
        (.cons (.assignFromMem (.index it (.alias (.there .here)) (.simple (.local .here))) p.up.up)
          .nil))) (.push (.push .refl))) σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [Prog.trunSt_declStorage_cons, TRes.map_bind']
  show TRes.Sim _ ((TRun.assignFromMem (.index it b i) p σ).map _)
  cases hb : b.resolveT σ with
  | error h' =>
    have hp : h' = .revert := SPath.resolveT_revert σ b hb
    simp only [TRun.assignFromMem, TRes.map_bind]
    refine TRes.Sim.err_bind (MPath.mvalT_noPanic σ p) hp fun _ _ => ?_
    simp only [Loc.resolveT, hb]
    exact TRes.Sim.refl _
  | ok q =>
    show TRes.Sim ((Prog.trunSt _ _).map _) _
    rw [Prog.trunSt_declLocal_cons, TRes.map_bind', Val.evalT_up]
    cases hi : i.evalT σ with
    | error h' =>
      have hp : h' = .revert := Val.evalT_revert σ i hi
      simp only [TRun.assignFromMem, TRes.map_bind]
      refine TRes.Sim.err_bind (MPath.mvalT_noPanic σ p) hp fun _ _ => ?_
      simp only [Loc.resolveT, hb, hi, ok_bind]
      exact TRes.Sim.refl _
    | ok n =>
      refine TRes.Sim.of_eq ?_
      show (Prog.trunSt _ (.cons _ .nil)).map _ = _
      rw [Prog.trunSt_single]
      have h₁ := TRun.assignFromMem_pushT (σ.push (t := .alias R) (some q)) (t := .val kp) n
        (.index it (.alias (.there .here)) (.simple (.local .here))) (.index it (.alias .here) i.up)
        p.up.up p.up (MPath.mvalT_up _ _ p.up)
        (by simp only [Loc.resolveT, Val.evalT_up, hi]; rfl)
      have h₂ := TRun.assignFromMem_pushT σ (t := .alias R) (some q) (.index it (.alias .here) i.up)
        (.index it b i) p.up p (MPath.mvalT_up σ _ p)
        (by simp only [Loc.resolveT, Val.evalT_up, hb]; rfl)
      show (((TRun.assignFromMem _ _ _).map (·.st)).map _) = _
      rw [h₁, h₂]
      exact pushedT2_drop σ (t := .alias R) (u := .val kp) (some q) n _

/-- **A storage location written from memory** (`assignFromMemStep`). -/
theorem assignFromMemStep_sound (k : Nat) {R : RefTy} (l : Loc C Γ (.ref R))
    (p : MPath C Γ (.ref R)) (q : Premise C Γ Γ)
    (hs : assignFromMemStep k l p = some q) : Premise.Runs m (.assignFromMem l p) q σ := by
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
theorem sound_deleteRecvCapture {R : RefTy} {T : Ty} (l' : Loc C (.alias R :: Γ) T)
    (b : SPath C Γ (.ref R)) (l : Loc C Γ T) (x : Var)
    (hl : ∀ q, b.resolveT σ = .ok q →
      l'.resolveT (σ.push (t := .alias R) (some q)) = l.resolveT σ)
    (herr : ∀ h, b.resolveT σ = .error h → l.resolveT σ = .error h) :
    Premise.Runs m (.delete l) (.captureSP x b (.delete l')) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .alias R) (some q)
      (TRun.delete_pushT σ (t := .alias R) (some q) l' l (hl q hq))
  · refine TRes.Sim.err_refl ?_
    show (TRun.delete l σ).map _ = _
    simp only [TRun.delete, herr h hh]; rfl

/-- `storageIndexDeleteNonSimpleIndexCapture`: the index captured; the
statement reads the receiver first. -/
theorem sound_deleteIndexCapture {R : RefTy} {kp : PrimTy} {T : Ty} (it : IndexTy R kp T)
    (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.Runs m (.delete (.index it b i))
      (.capture kp x i (.delete (.index it b.up (.simple (.local .here))))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine trunSt_pushed σ (t := .val kp) v (TRun.delete_pushT σ (t := .val kp) v
      (.index it b.up (.simple (.local .here))) (.index it b i) ?_)
    simp only [Loc.resolveT, SPath.resolveT_up, hv]; rfl
  · show TRes.Sim _ ((TRun.delete (.index it b i) σ).map _)
    simp only [TRun.delete, Loc.resolveT, bind_assoc, TRes.map_bind]
    refine TRes.Sim.err_bind (SPath.resolveT_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact TRes.Sim.refl _

/-- **`delete l;`** (`deleteStep`). -/
theorem deleteStep_sound (k : Nat) {T : Ty} (l : Loc C Γ T) (q : Premise C Γ Γ)
    (hs : deleteStep k l = some q) : Premise.Runs m (.delete l) q σ := by
  cases l with
  | root rn h => cases hs; exact sound_delAt σ _
  | field b f h =>
    simp only [deleteStep] at hs
    split at hs
    · cases hs; exact sound_delAt σ _
    · cases hs
      exact sound_deleteRecvCapture σ (.field (.alias .here) f h) b (.field b f h) _
        (fun q hq => by simp only [Loc.resolveT, hq]; rfl)
        (fun e he => by simp only [Loc.resolveT, he]; rfl)
  | index it b i =>
    simp only [deleteStep] at hs
    split at hs
    · cases i with
      | simple ie => cases hs; exact sound_delAt σ _
      | _ => cases hs; exact sound_deleteIndexCapture σ it b _ _
    · cases hs
      exact sound_deleteRecvCapture σ (.index it (.alias .here) i.up) b (.index it b i) _
        (fun q hq => by simp only [Loc.resolveT, Val.evalT_up, hq]; rfl)
        (fun e he => by simp only [Loc.resolveT, he]; rfl)

/-! ### Push and pop -/

/-- `storagePushValue_unfold_rightSndArgument`: the argument captured; the
statement reads the receiver first. -/
theorem sound_pushCapture {p : PrimTy} (b : SPath C Γ (.array (.prim p))) (e : Val C Γ p)
    (hd : ((some (Src.val e)).isSome || (Ty.prim p).defaultOkS) = true) (x : Var) :
    Premise.Runs m (.push b (some (.val e)) hd)
      (.capture p x e (.push b.up (some (.val (.simple (.local .here)))) rfl)) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine trunSt_pushed σ (t := .val p) v (TRun.push_some_pushT σ (t := .val p) v b.up b _
      (.val e) (SPath.resolveT_up σ _ b) ?_)
    simp only [Src.valueT, Val.evalT, hv]; rfl
  · show TRes.Sim _ ((TRun.push b (some (.val e)) σ).map _)
    simp only [TRun.push, TRes.map_bind]
    refine TRes.Sim.err_bind (SPath.resolveT_noPanic σ b) hp fun _ _ => ?_
    simp only [Src.valueT, hh]
    exact TRes.Sim.refl _

/-- `storagePush_unfold_leftFstReceiver`, `storagePushValue_unfold_leftFstReceiver`:
the receiver bound first. -/
theorem sound_pushRecvCapture {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true)
    (hd' : ((v.map Src.up).isSome || E.defaultOkS) = true) (x : Var) :
    Premise.Runs m (.push b v hd) (.captureSP x b (.push (.alias .here) (v.map Src.up) hd')) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ (t := .alias (.array E)) (some q) ?_
    cases v with
    | none =>
      exact TRun.push_none_pushT σ (t := .alias _) (some q) (.alias .here) b (by rw [hq]; rfl)
    | some r =>
      exact TRun.push_some_pushT σ (t := .alias _) (some q) (.alias .here) b r.up r
        (by rw [hq]; rfl) (Src.valueT_up σ _ r)
  · refine TRes.Sim.err_refl ?_
    show (TRun.push b v σ).map _ = _
    simp only [TRun.push, hh]; rfl

/-- **`b.push(v);`** (`pushStep`). -/
theorem pushStep_sound (k : Nat) {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (q : Premise C Γ Γ)
    (hs : pushStep k b v hd = some q) : Premise.Runs m (.push b v hd) q σ := by
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
    Premise.Runs m (.pop b) (.captureSP x b (.pop (.alias .here))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ (t := .alias (.array E)) (some q)
      (TRun.pop_pushT σ (t := .alias _) (some q) (.alias .here) b (by rw [hq]; rfl))
  · refine TRes.Sim.err_refl ?_
    show (TRun.pop b σ).map _ = _
    simp only [TRun.pop, hh]; rfl

/-- **`b.pop();`** (`popStep`). -/
theorem popStep_sound (k : Nat) {E : Ty} (b : SPath C Γ (.array E)) (q : Premise C Γ Γ)
    (hs : popStep k b = some q) : Premise.Runs m (.pop b) q σ := by
  simp only [popStep] at hs
  split at hs
  · have hp : Premise.Runs m (.pop b) (.upd1 (.storage (.app2
        (if E.isMapping then .shrink else .pop) .storage b.lower))) σ := sound_pop σ b
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
