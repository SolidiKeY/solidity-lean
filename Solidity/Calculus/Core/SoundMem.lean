import Solidity.Calculus.Core.SoundStore

/-!
# Soundness of the memory arms

`Calculus/Core/Arms.lean`'s `rebindMemStep`, `memRefStep`, `assignMemStep`,
`deleteMemStep` and `assignNewStep`, each sound in the shape of
`Calculus/Core/SoundKit.lean`, as `Calculus/Core/SoundStore.lean` proves the
storage arms: a read unfolded into a memory hole is
`Calculus/Core/SoundCapture.lean`'s, a block of captures is run one push at
a time, and where a rule binds the target before the source the two halt
alike (`Res.Sim`).
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

section Mem

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

theorem MSrc.mval_noPanic {T : Ty} (r : MSrc C Γ T) : NoPanic (r.mval σ) := by
  cases r with
  | val v => exact NoPanic.bind (Val.eval_noPanic σ v) fun _ _ => NoPanic.pure _
  | ref p =>
    simp only [MSrc.mval]
    exact NoPanic.bind (MPath.mval_noPanic σ p) fun _ _ =>
      NoPanic.bind (Solidity.MVal.asRef_noPanic _) fun _ _ => NoPanic.pure _

/-- A run that reads a memory path's object first halts alike to `h` when
what follows does: the read does not panic (an unset local reverts). -/
theorem MPath.sim_err_ref {β : Type} {T : Ty} (b : MPath C Γ T) {h : Halt} (hh : h ≠ .panic)
    {f : Nat → Res β} (hf : ∀ id, Res.Sim (.error h) (f id)) :
    Res.Sim (.error h) (b.mval σ >>= fun x => x.asRef >>= f) :=
  Res.Sim.err_bind (MPath.mval_noPanic σ b) hh fun _ _ =>
    Res.Sim.err_bind (Solidity.MVal.asRef_noPanic _) hh fun id _ => hf id

/-- A memory path whose object is `id` holds the reference to `id`. -/
theorem MPath.mval_of_ref {T : Ty} (b : MPath C Γ T) {id : Nat}
    (h : (do (← b.mval σ).asRef) = .ok id) : b.mval σ = .ok (.ref id) := by
  obtain ⟨mv, hmv, hr⟩ := Res.bind_eq_ok.1 h
  rw [hmv]
  cases mv <;> first | (cases hr; rfl) | (simp only [MVal.asRef] at hr; cases hr)

/-! ### A memory local bound -/

/-- `memoryStorageCopyUnfold`: the storage path bound first. -/
theorem sound_memCopyCapture {R : RefTy} (i : Idx Γ (.mem R)) (sp : SPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (x : Var) :
    Premise.Sound m (.rebindMem i (.copy sp hm))
      (.captureSP x sp (.rebindMem i.there (.copy (.alias .here) hm))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_rebindMem, Stmt.run_rebindMem,
      Run.rebindMem_push σ (t := .alias R) (some q) i _ (.copy sp hm)
        (MRhs.eval_copy_push σ _ (.alias .here) sp hm (by rw [hq]; rfl)), pushed_drop]
  · rw [Stmt.run_rebindMem]
    simp only [Run.rebindMem, MRhs.eval, hh]
    exact Res.Sim.refl _

/-- **A memory local bound** (`rebindMemStep`). -/
theorem rebindMemStep_sound (k : Nat) {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R)
    (q : Premise C Γ Γ) (hs : rebindMemStep k i r = some q) : Premise.Sound m (.rebindMem i r) q σ := by
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
      refine sound_allocCopy σ i _ _ ?_
      simp only [MRhs.eval, Tm.eval, Op2.eval, Op0.eval, SPath.eval_lower, bind_assoc, pure_bind]
    · cases hs; exact sound_memCopyCapture σ i sp hm _
  | newArr n h =>
    cases hs
    refine sound_allocCopy σ i _ _ ?_
    simp only [MRhs.eval, Tm.eval, Op1.eval, Simple.eval_lower, bind_assoc, pure_bind]

/-- **A memory reference written** (`memRefStep`). -/
theorem memRefStep_sound (k : Nat) {R : RefTy} (l : MLoc C Γ (.ref R)) (src : MPath C Γ (.ref R))
    (q : Premise C Γ Γ) (hs : memRefStep k l src = some q) :
    Premise.Sound m (.assignMem l (.ref src)) q σ := by
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
    Premise.Sound m (.assignMem (.field b f hf) r)
      (.captureMV x b (.assignMem (.field (.var .here hm) f hf) r.up)) σ := by
  refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun h hh hp => ?_)
  · rw [Stmt.run_assignMem, Stmt.run_assignMem,
      Run.assignMem_push σ (t := .mem _) id
        (.field (b' := .var .here hm) (b := b) f hf (MPath.mval_of_ref σ b hid).symm) r.up r
        (MSrc.mval_up σ _ r), pushed_drop]
  · rw [Stmt.run_assignMem]
    simp only [Run.assignMem]
    refine Res.Sim.err_bind (MSrc.mval_noPanic σ r) hp fun _ _ => ?_
    simp only [MLoc.write]
    rw [← bind_assoc, hh]
    exact Res.Sim.refl _

/-- `memoryIndexWriteCaptureAllNonSimpleIndex`: `T se = e; uint ie = i; mv[ie] = se;`. -/
theorem sound_memIndexWriteUnfold (k : Nat) {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p))
    (mv : Idx Γ (.mem R)) (hmv : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (e : Val C Γ p) :
    Premise.Sound m (.assignMem (.index a (.var mv hmv) i) (.val e))
      (.unfold (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declLocal .uint (fie k) (some i.up))
        (.cons (.assignMem (.index a (.var mv.there.there hmv) (.simple (.local .here)))
          (.val (.simple (.local (.there .here))))) .nil))) (.push (.push .refl))) σ := by
  refine Premise.Sound.unfoldSim ?_
  rw [Prog.run_declLocal_cons, Res.map_bind', Stmt.run_assignMem]
  cases he : e.eval σ with
  | error h' => refine Res.Sim.of_eq ?_; simp only [Run.assignMem, MSrc.mval, he]; rfl
  | ok v =>
    simp only [Res.bind_ok]
    rw [Prog.run_declLocal_cons, Res.map_bind', Val.eval_up]
    cases hi : i.eval σ with
    | error h' =>
      simp only [Run.assignMem, MSrc.mval, he, MLoc.write, hi, Res.bind_ok, pure_bind]
      exact MPath.sim_err_ref σ (.var mv hmv) (Val.eval_err_ne σ hi) fun _ => Res.Sim.refl _
    | ok n =>
      refine Res.Sim.of_eq ?_
      simp only [Res.bind_ok]
      rw [Prog.run_single, Stmt.run_assignMem,
        Run.assignMem_push (σ.push (t := .val p) v) (t := .val .uint) n
          (.index a (b' := .var mv.there.there hmv) (b := .var mv.there hmv)
            (i' := .simple (.local .here)) (i := i.up) rfl (by rw [Val.eval_up, hi]; rfl))
          (.val (.simple (.local (.there .here)))) (.val (.simple (.local .here))) rfl,
        Run.assignMem_push σ (t := .val p) v
          (.index a (b' := .var mv.there hmv) (b := .var mv hmv) rfl (Val.eval_up (t := .val p) σ v i))
          (.val (.simple (.local .here))) (.val e)
          (by simp only [MSrc.mval, Val.eval, Simple.eval_here, he, Res.bind_ok, pure_bind]),
        pushed2_drop]

/-- `memoryIndexWriteMemRefCaptureAllNonSimpleIndex`: the index captured; the
statement reads the source first. -/
theorem sound_memIndexRefCapture {R R' : RefTy} (a : ArrTy R (.ref R')) (mv : Idx Γ (.mem R))
    (hmv : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (src : MPath C Γ (.ref R')) (x : Var) :
    Premise.Sound m (.assignMem (.index a (.var mv hmv) i) (.ref src))
      (.capture .uint x i (.assignMem (.index a (.var mv.there hmv) (.simple (.local .here)))
        (.ref src.up))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · rw [Stmt.run_assignMem, Stmt.run_assignMem,
      Run.assignMem_push σ (t := .val .uint) v
        (.index a (b' := .var mv.there hmv) (b := .var mv hmv) (i' := .simple (.local .here)) (i := i)
          rfl (by rw [hv]; rfl)) (.ref src.up) (.ref src)
        (MSrc.mval_up σ _ (.ref src)), pushed_drop]
  · rw [Stmt.run_assignMem]
    simp only [Run.assignMem]
    refine Res.Sim.err_bind (MSrc.mval_noPanic σ _) hp fun _ _ => ?_
    simp only [MLoc.write, hh]
    exact MPath.sim_err_ref σ (.var mv hmv) hp fun _ => Res.Sim.refl _

/-- `memoryIndexWriteCaptureAllComplexRecv`:
`T se = e; T memory mv = nmp; uint ie = i; mv[ie] = se;`. -/
theorem sound_memIndexWriteRecvUnfold (k : Nat) {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p))
    (l : MLoc C Γ (.ref R)) (i : Val C Γ .uint) (e : Val C Γ p) :
    Premise.Sound m (.assignMem (.index a (.loc l) i) (.val e))
      (.unfold (.cons (.declLocal _ (fse k) (some e))
        (.cons (.declMem R (fmv k) (some (.alias (MPath.loc l).up)) rfl (MPath.loc l).mapFree)
        (.cons (.declLocal .uint (fie k) (some i.up.up))
        (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
          (.val (.simple (.local (.there (.there .here)))))) .nil))))
        (.push (.push (.push .refl)))) σ := by
  refine Premise.Sound.unfoldSim (Res.Sim.of_eq ?_)
  rw [Prog.run_declLocal_cons, Res.map_bind', Stmt.run_assignMem]
  cases he : e.eval σ with
  | error h' => simp only [Run.assignMem, MSrc.mval, he]; rfl
  | ok v =>
    simp only [Res.bind_ok]
    rw [Prog.run_declMem_cons, Res.map_bind', MPath.mval_up]
    cases hb : (do (← (MPath.loc l).mval σ).asRef : Res Nat) with
    | error h' =>
      simp only [Run.assignMem, MSrc.mval, he, MLoc.write, Res.bind_ok, pure_bind]
      rw [← bind_assoc, hb]; rfl
    | ok id =>
      simp only [Res.bind_ok]
      rw [Prog.run_declLocal_cons, Res.map_bind', Val.eval_up, Val.eval_up]
      cases hi : i.eval σ with
      | error h' =>
        simp only [Run.assignMem, MSrc.mval, he, MLoc.write, Res.bind_ok, pure_bind]
        rw [← bind_assoc, hb]
        simp only [Res.bind_ok, hi]; rfl
      | ok n =>
        simp only [Res.bind_ok]
        have hr : (MPath.loc l).mval σ = .ok (.ref id) := MPath.mval_of_ref σ _ hb
        rw [Prog.run_single, Stmt.run_assignMem,
          Run.assignMem_push ((σ.push (t := .val p) v).push (t := .mem R) id) (t := .val .uint) n
            (.index a (b' := .var (.there .here) (MPath.loc l).mapFree)
              (b := .var .here (MPath.loc l).mapFree) (i' := .simple (.local .here)) (i := i.up.up) rfl
              (by rw [Val.eval_up, Val.eval_up, hi]; rfl))
            (.val (.simple (.local (.there (.there .here))))) (.val (.simple (.local (.there .here)))) rfl,
          Run.assignMem_push (σ.push (t := .val p) v) (t := .mem R) id
            (.index a (b' := .var .here (MPath.loc l).mapFree) (b := (MPath.loc l).up) (i' := i.up.up)
              (i := i.up) (by rw [MPath.mval_up, hr]; rfl) (Val.eval_up _ _ i.up))
            (.val (.simple (.local (.there .here)))) (.val (.simple (.local .here))) rfl,
          Run.assignMem_push σ (t := .val p) v
            (.index a (b' := (MPath.loc l).up) (b := .loc l) (i' := i.up) (i := i)
              (MPath.mval_up σ _ (.loc l)) (Val.eval_up σ _ i))
            (.val (.simple (.local .here))) (.val e)
            (by simp only [MSrc.mval, Val.eval, Simple.eval_here, he, Res.bind_ok, pure_bind]),
          pushed3_drop]

/-- `memoryIndexWriteMemRefCaptureAllComplexRecv`:
`T memory mv = nmp; uint ie = i; mv[ie] = src;`; the statement reads the
source first. -/
theorem sound_memIndexRefRecvUnfold (k : Nat) {R R' : RefTy} (a : ArrTy R (.ref R'))
    (l : MLoc C Γ (.ref R)) (i : Val C Γ .uint) (src : MPath C Γ (.ref R')) :
    Premise.Sound m (.assignMem (.index a (.loc l) i) (.ref src))
      (.unfold (.cons (.declMem R (fmv k) (some (.alias (.loc l))) rfl (MPath.loc l).mapFree)
        (.cons (.declLocal .uint (fie k) (some i.up))
        (.cons (.assignMem (.index a (.var (.there .here) (MPath.loc l).mapFree) (.simple (.local .here)))
          (.ref src.up.up)) .nil))) (.push (.push .refl))) σ := by
  refine Premise.Sound.unfoldSim ?_
  rw [Prog.run_declMem_cons, Res.map_bind', Stmt.run_assignMem]
  cases hb : (do (← (MPath.loc l).mval σ).asRef : Res Nat) with
  | error h' =>
    have hp : h' ≠ .panic := fun e => MPath.ref_noPanic σ (.loc l) (e ▸ hb)
    simp only [Run.assignMem]
    refine Res.Sim.err_bind (MSrc.mval_noPanic σ _) hp fun _ _ => ?_
    simp only [MLoc.write]
    rw [← bind_assoc, hb]
    exact Res.Sim.refl _
  | ok id =>
    simp only [Res.bind_ok]
    rw [Prog.run_declLocal_cons, Res.map_bind', Val.eval_up]
    cases hi : i.eval σ with
    | error h' =>
      have hp := Val.eval_err_ne σ hi
      simp only [Run.assignMem]
      refine Res.Sim.err_bind (MSrc.mval_noPanic σ _) hp fun _ _ => ?_
      simp only [MLoc.write]
      rw [← bind_assoc, hb]
      simp only [Res.bind_ok, hi]
      exact Res.Sim.refl _
    | ok n =>
      simp only [Res.bind_ok]
      refine Res.Sim.of_eq ?_
      have hr : (MPath.loc l).mval σ = .ok (.ref id) := MPath.mval_of_ref σ _ hb
      rw [Prog.run_single, Stmt.run_assignMem,
        Run.assignMem_push (σ.push (t := .mem R) id) (t := .val .uint) n
          (.index a (b' := .var (.there .here) (MPath.loc l).mapFree)
            (b := .var .here (MPath.loc l).mapFree) (i' := .simple (.local .here)) (i := i.up) rfl
            (by rw [Val.eval_up, hi]; rfl))
          (.ref src.up.up) (.ref src.up) (MSrc.mval_up _ _ (.ref src.up)),
        Run.assignMem_push σ (t := .mem R) id
          (.index a (b' := .var .here (MPath.loc l).mapFree) (b := .loc l) (i' := i.up) (i := i)
            (by rw [hr]; rfl) (Val.eval_up σ _ i))
          (.ref src.up) (.ref src) (MSrc.mval_up σ _ (.ref src)),
        pushed2_drop]

/-- **A memory location written** (`assignMemStep`). -/
theorem assignMemStep_sound (k : Nat) {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) (q : Premise C Γ Γ)
    (hs : assignMemStep k l r = some q) : Premise.Sound m (.assignMem l r) q σ := by
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
    Premise.Sound m (.deleteMem (.loc (.field b f hf)) hd)
      (.captureMV x b (.deleteMem (.loc (.field (.var .here hm) f hf)) hd)) σ := by
  refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_deleteMem, Stmt.run_deleteMem,
      Run.deleteMem_push σ (t := .mem _) id
        (.field (b' := .var .here hm) (b := b) f hf (MPath.mval_of_ref σ b hid).symm),
      pushed_drop]
  · rw [Stmt.run_deleteMem]
    simp only [Run.deleteMem, MLoc.addr]
    rw [← bind_assoc, hh]
    exact Res.Sim.refl _

/-- `memoryIndexDeleteNonSimpleIndexCapture`: the index captured. -/
theorem sound_deleteMemIndexCapture {R : RefTy} {T : Ty} (a : ArrTy R T) (mv : Idx Γ (.mem R))
    (hmv : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (hd : T.defaultOkS = true) (x : Var) :
    Premise.Sound m (.deleteMem (.loc (.index a (.var mv hmv) i)) hd)
      (.capture .uint x i (.deleteMem (.loc (.index a (.var mv.there hmv) (.simple (.local .here)))) hd)) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_deleteMem, Stmt.run_deleteMem,
      Run.deleteMem_push σ (t := .val .uint) v
        (.index a (b' := .var mv.there hmv) (b := .var mv hmv) (i' := .simple (.local .here)) (i := i)
          rfl (by rw [hv]; rfl)),
      pushed_drop]
  · rw [Stmt.run_deleteMem]
    simp only [Run.deleteMem, MLoc.addr, hh, bind_assoc]
    exact MPath.sim_err_ref σ (.var mv hmv) (Val.eval_err_ne σ hh) fun _ => Res.Sim.refl _

/-- `memoryIndexDelete_unfold_leftFst`: the receiver bound first. -/
theorem sound_deleteMemIndexRecv {R : RefTy} {T : Ty} (a : ArrTy R T) (b : MPath C Γ (.ref R))
    (hm : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (hd : T.defaultOkS = true) (x : Var) :
    Premise.Sound m (.deleteMem (.loc (.index a b i)) hd)
      (.captureMV x b (.deleteMem (.loc (.index a (.var .here hm) i.up)) hd)) σ := by
  refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun h hh _ => ?_)
  · rw [Stmt.run_deleteMem, Stmt.run_deleteMem,
      Run.deleteMem_push σ (t := .mem _) id
        (.index a (b' := .var .here hm) (b := b) (i' := i.up) (i := i) (MPath.mval_of_ref σ b hid).symm
          (Val.eval_up σ _ i)),
      pushed_drop]
  · rw [Stmt.run_deleteMem]
    simp only [Run.deleteMem, MLoc.addr]
    rw [← bind_assoc, hh]
    exact Res.Sim.refl _

/-- **`delete p;` on memory** (`deleteMemStep`). -/
theorem deleteMemStep_sound (k : Nat) {T : Ty} (p : MPath C Γ T) (hd : T.defaultOkS = true)
    (q : Premise C Γ Γ) (hs : deleteMemStep k p hd = some q) : Premise.Sound m (.deleteMem p hd) q σ := by
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
    Premise.Sound m (.assignNew l n h)
      (.unfold (.cons (.declMem R (fmv k) (some (.newArr n h)) rfl (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)
        (.cons (l.up.fill (.var .here (MRhs.newArr (C := C) (Γ := Γ) n h).mapFree)) .nil)) (.push .refl)) σ := by
  refine Premise.Sound.unfold ?_
  obtain ⟨v, hv⟩ := Simple.eval_ok σ n
  rw [Prog.run_cons, Stmt.run_declMem, Stmt.run_assignNew]
  simp only [Run.declMem, Run.assignNew, MRhs.eval, hv, Res.bind_ok, Solidity.copyStToM_eq, bind_assoc,
    pure_bind]
  cases v.asInt with
  | error => rfl
  | ok z =>
    simp only [Res.bind_ok]
    cases Solidity.copyHN σ.glob (newArrVal R z) with
    | error => rfl
    | ok q =>
      simp only [Res.bind_ok]
      cases hr : q.2.2.asRef with
      | error => rfl
      | ok id =>
        simp only [Res.bind_ok]
        show Except.map _ (Prog.run _ (.cons _ .nil)) = _
        rw [Prog.run_single]
        cases l with
        | store l =>
          show Except.map _ (Run.assignFromMem l.up (.var .here _) _) = _
          simp only [Run.assignFromMem, MPath.mval, pure_bind, State.glob_push,
            Loc.resolve_up, withGlob_map_push]
          simp only [Res.map_bind', State.get_push_here, MVal.asRef, pushed_drop]
          rfl
        | mem l =>
          show Except.map _ (Run.assignMem l.up (.ref (.var .here _)) _) = _
          simp only [Run.assignMem, MSrc.mval, MPath.mval, memRef, State.get_push_here, MVal.asRef,
            pure_bind, (MLoc.Agree.of_up (t := .mem R) _ (some id) l).write, pushed_drop]

end Mem

end Solidity.Core
