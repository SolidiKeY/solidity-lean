import Solidity.Calculus.SoundStore
import Solidity.Semantics.NoPanic

/-!
# Soundness of the memory arms

`rebindMemStep`, `memRefStep`, `assignMemStep`, `deleteMemStep` and
`assignNewStep`, each `Premise.Sound`, as `Calculus/SoundStore.lean`
proves the storage arms.  A memory path's slot is a typed reference here,
so a captured receiver is the reference itself (no `asRef`).
-/

namespace Solidity
open Solidity (Modality Srt Op0 Op1 Op2 Op3)
open Semantics (Value Selector)

variable {C : Contract}

open Solidity (Modality Srt Op0 Op1 Op2 Op3)

section Mem

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

theorem MSrc.mvalT_noPanic {T : Ty} (r : MSrc C Γ T) : (r.mvalT σ).NoPanic := by
  cases r with
  | val v => exact Val.evalT_noPanic σ v
  | ref p => exact MPath.mvalT_noPanic σ p

theorem State.copyStToMG_push {t : LTy} (w : t.TDenote C σ.H) {T : Ty} (v : SVal T)
    (hm : T.mapFree = true) :
    (σ.push w).copyStToMG v hm = Grew.lift up (w, σ.env) (σ.copyStToMG v hm) :=
  State.copyStToMG_lift up σ (w, σ.env) v hm

/-! ### A memory local bound -/

/-- `memoryStorageCopyUnfold`: the storage path bound first. -/
theorem sound_memCopyCapture {R : RefTy} (i : Idx Γ (.mem R)) (sp : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (x : Var) :
    Premise.Runs m (.rebindMem i (.copy sp hm))
      (.captureSP x sp (.rebindMem i.there (.copy (.alias .here) hm))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .alias R) (some q)
      (TRun.rebindMem_pushT σ (t := .alias R) (some q) i _ (.copy sp hm) ?_)
    show (do
        let r ← (SPath.alias (C := C) (Γ := .alias R :: Γ) .here).resolveT (σ.push (some q))
        let sv ← TRes.ofOpt (σ.storage.find r)
        pure ((σ.push (t := .alias R) (some q)).copyStToMG sv hm)) = Except.map _ (do
        let r ← sp.resolveT σ
        let sv ← TRes.ofOpt (σ.storage.find r)
        pure (σ.copyStToMG sv hm))
    simp only [hq, TRes.map_bind, State.copyStToMG_push]
    rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.rebindMem i (.copy sp hm) σ).map _ = _
    simp only [TRun.rebindMem, MRhs.evalT, hh]; rfl

/-- **A memory local bound** (`rebindMemStep`). -/
theorem rebindMemStep_sound (k : Nat) {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R)
    (q : Premise C Γ Γ) (hs : rebindMemStep k i r = q) :
    Premise.Runs m (.rebindMem i r) q σ := by
  cases r with
  | alias p =>
    cases p with
    | var j hj => cases hs; exact sound_rebindMemAlias σ i (.var j hj)
    | loc l =>
      exact MHole.readStep_sound σ k (.rebind i)
        (fun mv hmv f hf _ hq => by
          cases hq; exact sound_rebindMemAlias (m := m) σ i (.loc (.field (.var mv hmv) f hf)))
        (fun a mv hmv ie _ hq => by
          cases hq
          exact sound_rebindMemAlias (m := m) σ i (.loc (.index a (.var mv hmv) (.simple ie))))
        l q hs
  | copy sp hm =>
    simp only [rebindMemStep] at hs
    split at hs
    · cases hs
      exact sound_allocCopy_copy σ i sp hm
    · cases hs; exact sound_memCopyCapture σ i sp hm _
  | newArr n h =>
    cases hs
    exact sound_allocCopy_newArr σ i n h

/-- **A memory reference written** (`memRefStep`). -/
theorem memRefStep_sound (k : Nat) {R : RefTy} (l : MLoc C Γ (.ref R))
    (src : MPath C Γ (.ref R)) (q : Premise C Γ Γ) (hs : memRefStep k l src = q) :
    Premise.Runs m (.assignMem l (.ref src)) q σ := by
  cases src with
  | var y hy => cases hs; exact sound_writeMem σ l _
  | loc sl =>
    exact MHole.readStep_sound σ k (.write l)
      (fun _ _ _ _ _ hq => by cases hq; exact sound_writeMem σ l _)
      (fun _ _ _ _ _ hq => by cases hq; exact sound_writeMem σ l _) sl q hs

/-! ### A memory location written -/

/-- `memoryFieldWrite_unfold_leftFst`: the receiver bound first; the
statement reads the source first. -/
theorem sound_memFieldWriteRecv {s : Name} {T : Ty} (b : MPath C Γ (.struct s))
    (hm : (Ty.ref (.struct s)).mapFree = true) (f : Name) (hf : C.fieldType s f = some T)
    (r : MSrc C Γ T) (x : Var) :
    Premise.Runs m (.assignMem (.field b f hf) r)
      (.captureMV x b (.assignMem (.field (.var .here hm) f hf) r.up)) σ := by
  refine Premise.sound_captureMVSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine runSt_pushed σ (t := .mem (.struct s)) (some v) (TRun.assignMem_pushT σ (t := .mem _) (some v)
      (.field (.var .here hm) f hf) (.field b f hf) r.up r ?_ (MSrc.mvalT_up σ _ r))
    simp only [MLoc.addrT, hv]; rfl
  · show TRes.Sim _ ((TRun.assignMem (.field b f hf) r σ).map _)
    simp only [TRun.assignMem, TRes.map_bind]
    refine TRes.Sim.err_bind (MSrc.mvalT_noPanic σ r) hp fun _ _ => ?_
    simp only [MLoc.addrT, hh]
    exact TRes.Sim.refl _

/-- `memoryIndexWriteCaptureAllNonSimpleIndex`: `T se = e; uint ie = i; mv[ie] = se;`. -/
theorem sound_memIndexWriteUnfold (k : Nat) {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p))
    (mv : Idx Γ (.mem R)) (hmv : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (e : Val C Γ p) :
    Premise.Runs m (.assignMem (.index a (.var mv hmv) i) (.val e))
      (.unfold (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declLocal .uint (fie k) (some i.up))
        (.cons (.assignMem (.index a (.var mv.there.there hmv) (.simple (.local .here)))
          (.val (.simple (.local (.there .here))))) .nil))) (.push (.push .refl))) σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [Prog.runSt_declLocal_cons, TRes.map_bind']
  show TRes.Sim _ ((TRun.assignMem (.index a (.var mv hmv) i) (.val e) σ).map _)
  cases he : e.evalT σ with
  | error h' => refine TRes.Sim.of_eq ?_; simp only [TRun.assignMem, MSrc.mvalT, he]; rfl
  | ok v =>
    show TRes.Sim ((Prog.runSt (σ.push (t := .val p) v) _).map _) _
    rw [Prog.runSt_declLocal_cons, TRes.map_bind', Val.evalT_up]
    cases hi : i.evalT σ with
    | error h' =>
      simp only [TRun.assignMem, MSrc.mvalT, he, MLoc.addrT, hi, ok_bind, TRes.map_bind,
        bind_assoc]
      exact TRes.Sim.err_bind (MPath.mvalT_noPanic σ _) (Val.evalT_revert σ i hi)
        fun _ _ => TRes.Sim.refl _
    | ok n =>
      refine TRes.Sim.of_eq ?_
      show (Prog.runSt _ (.cons _ .nil)).map _ = _
      rw [Prog.runSt_single]
      have h₁ := TRun.assignMem_pushT (σ.push (t := .val p) v) (t := .val .uint) n
        (.index a (.var mv.there.there hmv) (.simple (.local .here)))
        (.index a (.var mv.there hmv) i.up)
        (.val (.simple (.local (.there .here)))) (.val (.simple (.local .here)))
        (by
          simp only [MLoc.addrT, MPath.mvalT, Val.evalT_up, hi, State.get_push_there]
          cases (TEnv.get mv σ.env : Option (HRef σ.H R)) <;> rfl) rfl
      have h₂ := TRun.assignMem_pushT σ (t := .val p) v (.index a (.var mv.there hmv) i.up)
        (.index a (.var mv hmv) i) (.val (.simple (.local .here))) (.val e)
        (by
          simp only [MLoc.addrT, MPath.mvalT, Val.evalT_up, State.get_push_there]
          cases (TEnv.get mv σ.env : Option (HRef σ.H R)) <;> rfl)
        (by simp only [MSrc.mvalT, Val.evalT, he]; rfl)
      show (((TRun.assignMem _ _ _).map (·.st)).map _) = _
      rw [h₁, h₂]
      exact pushedT2_drop σ (t := .val p) (u := .val .uint) v n _

/-- `memoryIndexWriteMemRefCaptureAllNonSimpleIndex`: the index captured; the
statement reads the source first. -/
theorem sound_memIndexRefCapture {R R' : RefTy} (a : ArrTy R (.ref R')) (mv : Idx Γ (.mem R))
    (hmv : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (src : MPath C Γ (.ref R')) (x : Var) :
    Premise.Runs m (.assignMem (.index a (.var mv hmv) i) (.ref src))
      (.capture .uint x i (.assignMem (.index a (.var mv.there hmv) (.simple (.local .here)))
        (.ref src.up))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine runSt_pushed σ (t := .val .uint) v (TRun.assignMem_pushT σ (t := .val .uint) v
      (.index a (.var mv.there hmv) (.simple (.local .here))) (.index a (.var mv hmv) i)
      (.ref src.up) (.ref src) ?_ (MSrc.mvalT_up σ _ (.ref src)))
    simp only [MLoc.addrT, MPath.mvalT, hv, State.get_push_there]
    cases (TEnv.get mv σ.env : Option (HRef σ.H R)) <;> rfl
  · show TRes.Sim _ ((TRun.assignMem (.index a (.var mv hmv) i) (.ref src) σ).map _)
    simp only [TRun.assignMem, TRes.map_bind]
    refine TRes.Sim.err_bind (MSrc.mvalT_noPanic σ _) hp fun _ _ => ?_
    simp only [MLoc.addrT, hh, bind_assoc]
    exact TRes.Sim.err_bind (MPath.mvalT_noPanic σ _) hp fun _ _ => TRes.Sim.refl _

/-- `memoryIndexWriteCaptureAllComplexRecv`:
`T se = e; T memory mv = nmp; uint ie = i; mv[ie] = se;`. -/
theorem sound_memIndexWriteRecvUnfold (k : Nat) {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p))
    (l : MLoc C Γ (.ref R)) (i : Val C Γ .uint) (e : Val C Γ p) :
    Premise.Runs m (.assignMem (.index a (.loc l) i) (.val e))
      (.unfold (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declMem R (fmv k) (some (.alias (MPath.loc l).up)) rfl (MPath.loc l).mapFree)
        (.cons (.declLocal .uint (fie k) (some i.up.up))
        (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree)
          (.simple (.local .here))) (.val (.simple (.local (.there (.there .here)))))) .nil))))
        (.push (.push (.push .refl)))) σ := by
  refine Premise.sound_unfoldSim σ (TRes.Sim.of_eq ?_)
  rw [Prog.runSt_declLocal_cons, TRes.map_bind']
  show _ = (TRun.assignMem (.index a (.loc l) i) (.val e) σ).map _
  cases he : e.evalT σ with
  | error h' => simp only [TRun.assignMem, MSrc.mvalT, he]; rfl
  | ok v =>
    show (Prog.runSt (σ.push (t := .val p) v) _).map _ = _
    rw [Prog.runSt_declMem_cons, TRes.map_bind', MPath.mvalT_up]
    cases hb : (MPath.loc l).mvalT σ with
    | error h' =>
      simp only [TRun.assignMem, MSrc.mvalT, he, MLoc.addrT, hb, ok_bind]; rfl
    | ok r =>
      show (Prog.runSt _ _).map _ = _
      rw [Prog.runSt_declLocal_cons, TRes.map_bind', Val.evalT_up, Val.evalT_up]
      cases hi : i.evalT σ with
      | error h' =>
        simp only [TRun.assignMem, MSrc.mvalT, he, MLoc.addrT, hb, hi, ok_bind]; rfl
      | ok n =>
        show (Prog.runSt _ (.cons _ .nil)).map _ = _
        rw [Prog.runSt_single]
        have h₁ := TRun.assignMem_pushT ((σ.push (t := .val p) v).push (t := .mem R) (some r))
          (t := .val .uint) n
          (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
          (.index a (.var .here (MPath.loc l).mapFree) i.up.up)
          (.val (.simple (.local (.there (.there .here))))) (.val (.simple (.local (.there .here))))
          (by simp only [MLoc.addrT, MPath.mvalT, Val.evalT_up, hi]; rfl) rfl
        have h₂ := TRun.assignMem_pushT (σ.push (t := .val p) v) (t := .mem R) (some r)
          (.index a (.var .here (MPath.loc l).mapFree) i.up.up) (.index a (MPath.loc l).up i.up)
          (.val (.simple (.local (.there .here)))) (.val (.simple (.local .here)))
          (by simp only [MLoc.addrT, MPath.mvalT_up, Val.evalT_up, hb]; rfl) rfl
        have h₃ := TRun.assignMem_pushT σ (t := .val p) v (.index a (MPath.loc l).up i.up)
          (.index a (.loc l) i) (.val (.simple (.local .here))) (.val e)
          (by simp only [MLoc.addrT, MPath.mvalT_up, Val.evalT_up]; rfl)
          (by simp only [MSrc.mvalT, Val.evalT, he]; rfl)
        show (((TRun.assignMem _ _ _).map (·.st)).map _) = _
        rw [h₁, h₂, h₃]
        exact pushedT3_drop σ (t := .val p) (u := .mem R) (y := .val .uint) v (some r) n _

/-- `memoryIndexWriteMemRefCaptureAllComplexRecv`:
`T memory mv = nmp; uint ie = i; mv[ie] = src;`; the statement reads the
source first. -/
theorem sound_memIndexRefRecvUnfold (k : Nat) {R R' : RefTy} (a : ArrTy R (.ref R'))
    (l : MLoc C Γ (.ref R)) (i : Val C Γ .uint) (src : MPath C Γ (.ref R')) :
    Premise.Runs m (.assignMem (.index a (.loc l) i) (.ref src))
      (.unfold (.cons (.declMem R (fmv k) (some (.alias (.loc l))) rfl (MPath.loc l).mapFree)
        (.cons (.declLocal .uint (fie k) (some i.up))
        (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree)
          (.simple (.local .here))) (.ref src.up.up)) .nil))) (.push (.push .refl))) σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [Prog.runSt_declMem_cons, TRes.map_bind']
  show TRes.Sim _ ((TRun.assignMem (.index a (.loc l) i) (.ref src) σ).map _)
  cases hb : (MPath.loc l).mvalT σ with
  | error h' =>
    have hp : h' = .revert := MPath.mvalT_revert σ (.loc l) hb
    simp only [TRun.assignMem, TRes.map_bind]
    refine TRes.Sim.err_bind (MSrc.mvalT_noPanic σ _) hp fun _ _ => ?_
    simp only [MLoc.addrT, hb]
    exact TRes.Sim.refl _
  | ok r =>
    show TRes.Sim ((Prog.runSt _ _).map _) _
    rw [Prog.runSt_declLocal_cons, TRes.map_bind', Val.evalT_up]
    cases hi : i.evalT σ with
    | error h' =>
      have hp : h' = .revert := Val.evalT_revert σ i hi
      simp only [TRun.assignMem, TRes.map_bind]
      refine TRes.Sim.err_bind (MSrc.mvalT_noPanic σ _) hp fun _ _ => ?_
      simp only [MLoc.addrT, hb, hi, ok_bind]
      exact TRes.Sim.refl _
    | ok n =>
      refine TRes.Sim.of_eq ?_
      show (Prog.runSt _ (.cons _ .nil)).map _ = _
      rw [Prog.runSt_single]
      have h₁ := TRun.assignMem_pushT (σ.push (t := .mem R) (some r)) (t := .val .uint) n
        (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
        (.index a (.var .here (MPath.loc l).mapFree) i.up) (.ref src.up.up) (.ref src.up)
        (by simp only [MLoc.addrT, MPath.mvalT, Val.evalT_up, hi]; rfl)
        (MSrc.mvalT_up _ _ (.ref src.up))
      have h₂ := TRun.assignMem_pushT σ (t := .mem R) (some r)
        (.index a (.var .here (MPath.loc l).mapFree) i.up) (.index a (.loc l) i)
        (.ref src.up) (.ref src) (by simp only [MLoc.addrT, Val.evalT_up, hb]; rfl)
        (MSrc.mvalT_up σ _ (.ref src))
      show (((TRun.assignMem _ _ _).map (·.st)).map _) = _
      rw [h₁, h₂]
      exact pushedT2_drop σ (t := .mem R) (u := .val .uint) (some r) n _

/-- **A memory location written** (`assignMemStep`). -/
theorem assignMemStep_sound (k : Nat) {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T)
    (q : Premise C Γ Γ) (hs : assignMemStep k l r = q) :
    Premise.Runs m (.assignMem l r) q σ := by
  cases l with
  | field b f hf =>
    cases b with
    | var mv hmv =>
      cases r with
      | val e =>
        exact VHole.step_sound σ k (.mem (.field (.var mv hmv) f hf))
          (fun _ _ hq => by cases hq; exact sound_writeMem σ _ _) e q hs
      | ref src => exact memRefStep_sound σ k _ src q hs
    | loc l => cases r <;> (cases hs; exact sound_memFieldWriteRecv σ (.loc l) _ f hf _ _)
  | index a b i =>
    cases b with
    | var mv hmv =>
      cases i with
      | simple ie =>
        cases r with
        | val e =>
          exact VHole.step_sound σ k (.mem (.index a (.var mv hmv) (.simple ie)))
            (fun _ _ hq => by cases hq; exact sound_writeMem σ _ _) e q hs
        | ref src => exact memRefStep_sound σ k _ src q hs
      | _ =>
        cases r with
        | val e => cases hs; exact sound_memIndexWriteUnfold σ k a mv hmv _ e
        | ref src => cases hs; exact sound_memIndexRefCapture σ a mv hmv _ src _
    | loc l =>
      cases r with
      | val e => cases hs; exact sound_memIndexWriteRecvUnfold σ k a l i e
      | ref src => cases hs; exact sound_memIndexRefRecvUnfold σ k a l i src

/-! ### `delete` on memory, `new` -/

/-- `memoryFieldDelete_unfold_leftFst`: the receiver bound first. -/
theorem sound_deleteMemFieldRecv {s : Name} {T : Ty} (b : MPath C Γ (.struct s))
    (hm : (Ty.ref (.struct s)).mapFree = true) (f : Name) (hf : C.fieldType s f = some T)
    (hd : T.defaultOkS = true) (x : Var) :
    Premise.Runs m (.deleteMem (.loc (.field b f hf)) hd)
      (.captureMV x b (.deleteMem (.loc (.field (.var .here hm) f hf)) hd)) σ := by
  refine Premise.sound_captureMVSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .mem (.struct s)) (some v) (TRun.deleteMem_pushT σ (t := .mem _) (some v)
      (.field (.var .here hm) f hf) (.field b f hf) ?_)
    simp only [MLoc.addrT, hv]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.deleteMem (.loc (.field b f hf)) σ).map _ = _
    simp only [TRun.deleteMem, MLoc.addrT, hh]; rfl

/-- `memoryIndexDeleteNonSimpleIndexCapture`: the index captured. -/
theorem sound_deleteMemIndexCapture {R : RefTy} {T : Ty} (a : ArrTy R T) (mv : Idx Γ (.mem R))
    (hmv : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (hd : T.defaultOkS = true) (x : Var) :
    Premise.Runs m (.deleteMem (.loc (.index a (.var mv hmv) i)) hd)
      (.capture .uint x i
        (.deleteMem (.loc (.index a (.var mv.there hmv) (.simple (.local .here)))) hd)) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .val .uint) v (TRun.deleteMem_pushT σ (t := .val .uint) v
      (.index a (.var mv.there hmv) (.simple (.local .here))) (.index a (.var mv hmv) i) ?_)
    simp only [MLoc.addrT, MPath.mvalT, hv, State.get_push_there]
    cases (TEnv.get mv σ.env : Option (HRef σ.H R)) <;> rfl
  · show TRes.Sim _ ((TRun.deleteMem (.loc (.index a (.var mv hmv) i)) σ).map _)
    simp only [TRun.deleteMem, MLoc.addrT, hh, bind_assoc, TRes.map_bind]
    exact TRes.Sim.err_bind (MPath.mvalT_noPanic σ _) (Val.evalT_revert σ i hh)
      fun _ _ => TRes.Sim.refl _

/-- `memoryIndexDelete_unfold_leftFst`: the receiver bound first. -/
theorem sound_deleteMemIndexRecv {R : RefTy} {T : Ty} (a : ArrTy R T) (b : MPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (hd : T.defaultOkS = true) (x : Var) :
    Premise.Runs m (.deleteMem (.loc (.index a b i)) hd)
      (.captureMV x b (.deleteMem (.loc (.index a (.var .here hm) i.up)) hd)) σ := by
  refine Premise.sound_captureMVSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ (t := .mem R) (some v) (TRun.deleteMem_pushT σ (t := .mem _) (some v)
      (.index a (.var .here hm) i.up) (.index a b i) ?_)
    simp only [MLoc.addrT, Val.evalT_up, hv]; rfl
  · refine TRes.Sim.err_refl ?_
    show (TRun.deleteMem (.loc (.index a b i)) σ).map _ = _
    simp only [TRun.deleteMem, MLoc.addrT, hh]; rfl

/-- **`delete p;` on memory** (`deleteMemStep`). -/
theorem deleteMemStep_sound (k : Nat) {T : Ty} (p : MPath C Γ T) (hd : T.defaultOkS = true)
    (q : Premise C Γ Γ) (hs : deleteMemStep k p hd = q) :
    Premise.Runs m (.deleteMem p hd) q σ := by
  cases p with
  | var i hm => cases hs; exact sound_deleteMemVar σ i hm hd
  | loc l =>
    cases l with
    | field b f hf =>
      cases b with
      | var mv hmv => cases hs; exact sound_clearMem σ _ hd
      | loc l => cases hs; exact sound_deleteMemFieldRecv σ (.loc l) _ f hf hd _
    | index a b i =>
      cases b with
      | var mv hmv =>
        cases i with
        | simple ie => cases hs; exact sound_clearMem σ _ hd
        | _ => cases hs; exact sound_deleteMemIndexCapture σ a mv hmv _ hd _
      | loc l => cases hs; exact sound_deleteMemIndexRecv σ a (.loc l) _ i hd _

/-- `newArrayCapture`: `T memory mv = new T(se); tgt = mv;`. -/
theorem sound_assignNew (k : Nat) {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) :
    Premise.Runs m (.assignNew l n h)
      (.unfold (.cons (.declMem R (fmv k) (some (.newArr n h)) rfl
          (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)
        (.cons (l.up.fill (.var .here (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)) .nil))
        (.push .refl)) σ := by
  refine Premise.sound_unfold σ ?_
  rw [Prog.runSt_cons]
  show (Except.bind (Stmt.runSt σ _) _).map _ = (TRun.assignNew l n h σ).map (·.st)
  rw [TRun.assignNew_eq]
  have hd : Stmt.runSt σ (.declMem R (fmv k) (some (.newArr n h)) rfl
      (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree) =
      .ok ((σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)).st.push
        (t := .mem R)
        (some (σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)).val)) :=
    rfl
  rw [hd]
  show (Prog.runSt _ (.cons _ .nil)).map _ = _
  rw [Prog.runSt_single]
  generalize σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h) = g
  cases l with
  | store l =>
    show ((TRun.assignFromMem l.up (.var .here _) (g.st.push (t := .mem R) (some g.val))).map (·.st)).map _ = _
    simp only [TRun.assignFromMem, TRun.newWrite, MPath.mvalT, State.get_push_here, ok_bind,
      Loc.resolveT_up]
    cases l.resolveT g.st with
    | error => rfl
    | ok ref =>
      simp only [ok_bind]
      have hw : (g.st.push (t := .mem R) (some g.val)).storage.write ref (MVal.copyMToSt
          (g.st.push (t := .mem R) (some g.val)).heap g.val) =
          g.st.storage.write ref (MVal.copyMToSt g.st.heap g.val) := rfl
      rw [hw]
      cases g.st.storage.write ref (MVal.copyMToSt g.st.heap g.val) <;> rfl
  | mem l =>
    show ((TRun.assignMem l.up (.ref (.var .here _)) (g.st.push (t := .mem R) (some g.val))).map
      (·.st)).map _ = _
    simp only [TRun.assignMem, TRun.newWrite, MSrc.mvalT, MPath.mvalT, State.get_push_here,
      ok_bind, MLoc.addrT_up]
    cases l.addrT g.st with
    | error => rfl
    | ok a =>
      simp only [ok_bind]
      have hw : (g.st.push (t := .mem R) (some g.val)).heap.writeAddr a g.val =
          g.st.heap.writeAddr a g.val := rfl
      rw [hw]
      cases g.st.heap.writeAddr a g.val <;> rfl

end Mem

end Solidity
