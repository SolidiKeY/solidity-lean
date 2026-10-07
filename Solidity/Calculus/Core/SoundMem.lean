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
  refine Premise.Sound.unfoldSim (Res.Sim.of_eq ?_)
  rw [Prog.run_declLocal_cons, Res.map_bind', Stmt.run_assignMem]
  cases he : e.eval σ with
  | error h' => simp only [Run.assignMem, MSrc.mval, he]; rfl
  | ok v =>
    simp only [Res.bind_ok]
    rw [Prog.run_declLocal_cons, Res.map_bind', Val.eval_up]
    cases hi : i.eval σ with
    | error h' =>
      simp only [Run.assignMem, MSrc.mval, he, MLoc.write, MPath.mval, hi, Res.bind_ok, pure_bind]
      rfl
    | ok n =>
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
    simp only [MLoc.write, MPath.mval, hh, Res.bind_ok, pure_bind]
    exact Res.Sim.refl _

end Mem

end Solidity.Core
