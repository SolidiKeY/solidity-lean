import Solidity.Calculus.SoundArms
import Solidity.Semantics.NoPanic

/-!
# Soundness of captures, and the holes a read lands in

A rule that captures a part (`T se = nse; s'`, `T storage sp = nsp; s'`,
`T memory mv = nmp; s'`) is sound when `s'`, read with the part's value on
top, runs as the statement it replaces, and the statement halts alike where
the part halts (`Premise.sound_captureSim` and its kin,
`Calculus/SoundKit.lean`).

A statement read with a local pushed runs as before, its outcome lifted
along `up` (`liftedT`, `Semantics/RunWk.lean`): a hole filled is
the read and then what the hole does with it (`SHole.contT`, `MHole.contT`,
`VHole.contT`), and the hole shifted under a local does the same, lifted
(`*.contT_up`), so a rule that unfolds a read is sound for every hole at
once.
-/

namespace Solidity
open Solidity (Modality Srt Op0 Op1 Op2 Op3)
open Semantics (Selector)

variable {C : Contract}


open Solidity (Modality)

/-! ## A statement run with a local pushed -/

section Pushed

variable {Γ : Ctx} {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H)

/-- A statement that runs, from `σ` with `w` pushed, as `s` from `σ` lifted
runs as `s` once the local is popped. -/
theorem runSt_pushed {s' : Stmt C (t :: Γ) (t :: Γ)} {s : Stmt C Γ Γ}
    (h : s'.run (σ.push w) = liftedT up (w, σ.env) (s.run σ)) :
    (Stmt.runSt (σ.push w) s').map (State.drop (.push .refl)) = Stmt.runSt σ s := by
  show ((s'.run (σ.push w)).map (·.st)).map _ = (s.run σ).map (·.st)
  rw [h]
  exact liftedT_up_drop σ w _

end Pushed

/-! ## Holes: the read, then what the hole does with it -/

section Holes

variable {Γ : Ctx}

/-- What a storage hole does with the reference it is given: `v = find(…)`,
`lsv = p`, `loc = copy(…)`. -/
def SHole.contT : {T : Ty} → SHole C Γ T → (σ : State C Γ) → SRef C T → TRes (Out C σ.H Γ)
  | _, .local i, σ, r => do
    let v ← TRes.ofOpt (σ.storage.find r)
    pure ⟨σ.setLocal i v.view, List.prefix_refl _⟩
  | _, .rebind i, σ, r => pure ⟨σ.setLocal i (some r), List.prefix_refl _⟩
  | _, .copy l _, σ, r => do
    let sv ← TRes.ofOpt (σ.storage.find r)
    let ref ← l.resolveT σ
    let st ← TRes.ofOpt (σ.storage.write ref sv)
    pure ⟨σ.withStorage st, List.prefix_refl _⟩

theorem SHole.fill_run (σ : State C Γ) {T : Ty} (lhs : SHole C Γ T) (l : Loc C Γ T) :
    (lhs.fill (.loc l)).run σ = l.resolveT σ >>= lhs.contT σ := by
  cases lhs with
  | «local» i =>
    show TRun.assignLocal i (.read l) σ = _
    simp only [TRun.assignLocal, Val.evalT, bind_assoc, pure_bind]; rfl
  | rebind i =>
    show TRun.rebind i (.path (.loc l)) σ = _
    simp only [TRun.rebind, ARhs.evalT, SPath.resolveT, bind_assoc, pure_bind]; rfl
  | copy l' h =>
    show TRun.assign l' (.copy (.loc l) h) σ = _
    simp only [TRun.assign, Src.valueT, SPath.resolveT, bind_assoc]; rfl

theorem SHole.contT_up {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : SHole C Γ T) (r : SRef C T) :
    lhs.up.contT (σ.push w) r = liftedT Solidity.up (w, σ.env) (lhs.contT σ r) := by
  cases lhs with
  | «local» i =>
    simp only [SHole.up, SHole.contT, liftedT_bind]
    lift_fin
  | rebind i =>
    simp only [SHole.up, SHole.contT]
    lift_fin
  | copy l h =>
    simp only [SHole.up, SHole.contT, liftedT_bind, Loc.resolveT_up]
    lift_fin

theorem SHole.fill_pushT {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : SHole C Γ T) (l' : Loc C (t :: Γ) T) (l : Loc C Γ T)
    (hl : l'.resolveT (σ.push w) = l.resolveT σ) :
    (lhs.up.fill (.loc l')).run (σ.push w) =
      liftedT Solidity.up (w, σ.env) ((lhs.fill (.loc l)).run σ) := by
  rw [SHole.fill_run, SHole.fill_run, hl, liftedT_bind]
  congr 1; funext q; exact SHole.contT_up σ w lhs q

/-- What a memory hole does with the address it is given: `v = read(…)`,
`mv = r`, `mloc = r`. -/
def MHole.contT : {T : Ty} → MHole C Γ T → (σ : State C Γ) → MAddr σ.H T → TRes (Out C σ.H Γ)
  | _, .local i, σ, a => do
    let v ← TRes.ofOpt (σ.heap.readAddr a)
    pure ⟨σ.setLocal i v, List.prefix_refl _⟩
  | _, .rebind i, σ, a => do
    let r ← TRes.ofOpt (σ.heap.readAddr a)
    pure ⟨σ.setLocal i (some r), List.prefix_refl _⟩
  | _, .write l, σ, a => do
    let mv ← TRes.ofOpt (σ.heap.readAddr a)
    let a' ← l.addrT σ
    let hp ← TRes.ofOpt (σ.heap.writeAddr a' mv)
    pure ⟨σ.withHeap hp, List.prefix_refl _⟩

theorem MHole.fill_run (σ : State C Γ) {T : Ty} (lhs : MHole C Γ T) (l : MLoc C Γ T) :
    (lhs.fill l).run σ = l.addrT σ >>= lhs.contT σ := by
  cases lhs with
  | «local» i =>
    show TRun.assignLocal i (.readMem l) σ = _
    simp only [TRun.assignLocal, Val.evalT, bind_assoc]; rfl
  | rebind i =>
    show TRun.rebindMem i (.alias (.loc l)) σ = _
    simp only [TRun.rebindMem, MRhs.evalT, MPath.mvalT, bind_assoc, pure_bind]; rfl
  | write l' =>
    show TRun.assignMem l' (.ref (.loc l)) σ = _
    simp only [TRun.assignMem, MSrc.mvalT, MPath.mvalT, bind_assoc]; rfl

theorem MHole.contT_up {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : MHole C Γ T) (a : MAddr σ.H T) :
    lhs.up.contT (σ.push w) a = liftedT Solidity.up (w, σ.env) (lhs.contT σ a) := by
  cases lhs with
  | «local» i =>
    simp only [MHole.up, MHole.contT, liftedT_bind]
    lift_fin
  | rebind i =>
    simp only [MHole.up, MHole.contT, liftedT_bind]
    lift_fin
  | write l =>
    simp only [MHole.up, MHole.contT, liftedT_bind, MLoc.addrT_up]
    lift_fin

theorem MHole.fill_pushT {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : MHole C Γ T) (l' : MLoc C (t :: Γ) T) (l : MLoc C Γ T)
    (hl : l'.addrT (σ.push w) = l.addrT σ) :
    (lhs.up.fill l').run (σ.push w) = liftedT Solidity.up (w, σ.env) ((lhs.fill l).run σ) := by
  rw [MHole.fill_run, MHole.fill_run, hl, liftedT_bind]
  congr 1; funext q; exact MHole.contT_up σ w lhs q

/-- What a value hole does with the value it is given: `v = e`, `loc = e`,
`mloc = e`. -/
def VHole.contT {p : PrimTy} : VHole C Γ p → (σ : State C Γ) → p.Denote → TRes (Out C σ.H Γ)
  | .local i, σ, v => pure ⟨σ.setLocal i v, List.prefix_refl _⟩
  | .store l, σ, v => do
    let ref ← l.resolveT σ
    let st ← TRes.ofOpt (σ.storage.write ref (.prim v))
    pure ⟨σ.withStorage st, List.prefix_refl _⟩
  | .mem l, σ, v => do
    let a ← l.addrT σ
    let hp ← TRes.ofOpt (σ.heap.writeAddr a v)
    pure ⟨σ.withHeap hp, List.prefix_refl _⟩

theorem VHole.fill_run (σ : State C Γ) {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) :
    (lhs.fill e).run σ = e.evalT σ >>= lhs.contT σ := by
  cases lhs with
  | «local» i => rfl
  | store l =>
    show TRun.assign l (.val e) σ = _
    simp only [TRun.assign, Src.valueT, bind_assoc, pure_bind]; rfl
  | mem l =>
    show TRun.assignMem l (.val e) σ = _
    simp only [TRun.assignMem, MSrc.mvalT]; rfl

theorem VHole.contT_up {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H) {p : PrimTy}
    (lhs : VHole C Γ p) (v : p.Denote) :
    lhs.up.contT (σ.push w) v = liftedT Solidity.up (w, σ.env) (lhs.contT σ v) := by
  cases lhs with
  | «local» i =>
    simp only [VHole.up, VHole.contT]
    lift_fin
  | store l =>
    simp only [VHole.up, VHole.contT, liftedT_bind, Loc.resolveT_up]
    lift_fin
  | mem l =>
    simp only [VHole.up, VHole.contT, liftedT_bind, MLoc.addrT_up]
    lift_fin

theorem VHole.fill_pushT {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H) {p : PrimTy}
    (lhs : VHole C Γ p) (e' : Val C (t :: Γ) p) (e : Val C Γ p)
    (he : e'.evalT (σ.push w) = e.evalT σ) :
    (lhs.up.fill e').run (σ.push w) = liftedT Solidity.up (w, σ.env) ((lhs.fill e).run σ) := by
  rw [VHole.fill_run, VHole.fill_run, he, liftedT_bind]
  congr 1; funext q; exact VHole.contT_up σ w lhs q

end Holes

/-! ## A read unfolded into a hole -/

section ReadSteps

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- `storageFieldRead_unfold_rightFst`: the receiver bound first. -/
theorem SHole.sound_fieldCapture {T : Ty} (lhs : SHole C Γ T) {s : Name}
    (b : SPath C Γ (.struct s)) (f : Name) (hf : C.fieldType s f = some T) (x : Var) :
    Premise.Runs m (lhs.fill (.loc (.field b f hf)))
      (.captureSP x b (lhs.up.fill (.loc (.field (.alias .here) f hf)))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ _ (SHole.fill_pushT σ (t := .alias (.struct s)) (some q) lhs _ (.field b f hf) ?_)
    simp only [Loc.resolveT, hq]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.loc (.field b f hf))).run σ).map _ = _
    rw [SHole.fill_run]
    simp only [Loc.resolveT, hh]; rfl

/-- `storageIndexRead_unfold_rightFst`: the receiver bound first. -/
theorem SHole.sound_indexRecvCapture {T : Ty} (lhs : SHole C Γ T) {R : RefTy} {kp : PrimTy}
    (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.Runs m (lhs.fill (.loc (.index it b i)))
      (.captureSP x b (lhs.up.fill (.loc (.index it (.alias .here) i.up)))) σ := by
  refine Premise.sound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ _ (SHole.fill_pushT σ (t := .alias R) (some q) lhs _ (.index it b i) ?_)
    simp only [Loc.resolveT, Val.evalT_up, hq]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.loc (.index it b i))).run σ).map _ = _
    rw [SHole.fill_run]
    simp only [Loc.resolveT, hh]; rfl

/-- `storageIndexRead_unfold_rightSndIndex`: the index captured, the receiver
(simple) read after it. -/
theorem SHole.sound_indexCapture {T : Ty} (lhs : SHole C Γ T) {R : RefTy} {kp : PrimTy}
    (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.Runs m (lhs.fill (.loc (.index it b i)))
      (.capture kp x i (lhs.up.fill (.loc (.index it b.up (.simple (.local .here)))))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine runSt_pushed σ _ (SHole.fill_pushT σ (t := .val kp) v lhs _ (.index it b i) ?_)
    simp only [Loc.resolveT, SPath.resolveT_up, hv]; rfl
  · show TRes.Sim _ (((lhs.fill (.loc (.index it b i))).run σ).map _)
    rw [SHole.fill_run]
    simp only [Loc.resolveT, bind_assoc, TRes.map_bind]
    refine TRes.Sim.err_bind (SPath.resolveT_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact TRes.Sim.refl _

/-- **A storage read unfolded into a hole** (`SHole.readStep`) is sound
when the hole's own rules are. -/
theorem SHole.readStep_sound (k : Nat) {T : Ty} (lhs : SHole C Γ T)
    {root : (r : Name) → C.rootType r = some T → Premise C Γ Γ}
    {field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Premise C Γ Γ}
    {index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) → Simple C Γ kp →
      Premise C Γ Γ}
    (l : Loc C Γ T)
    (hroot : ∀ r h p, l = .root r h → root r h = p →
      Premise.Runs m (lhs.fill (.loc (.root r h))) p σ)
    (hfield : ∀ {s : Name} (b : SPath C Γ (.struct s)) f hf p, l = .field b f hf →
      field b f hf = p → Premise.Runs m (lhs.fill (.loc (.field b f hf))) p σ)
    (hindex : ∀ {R : RefTy} {kp : PrimTy} (it : IndexTy R kp T) b (ie : Simple C Γ kp) p,
      l = .index it b (.simple ie) → index it b ie = p →
      Premise.Runs m (lhs.fill (.loc (.index it b (.simple ie)))) p σ)
    (p : Premise C Γ Γ) (hp : lhs.readStep k root field index l = p) :
    Premise.Runs m (lhs.fill (.loc l)) p σ := by
  cases l with
  | root r h => exact hroot r h p rfl hp
  | field b f hf =>
    simp only [SHole.readStep] at hp
    split at hp
    · exact hfield b f hf p rfl hp
    · cases hp; exact SHole.sound_fieldCapture σ lhs b f hf _
  | index it b i =>
    simp only [SHole.readStep] at hp
    split at hp
    · split at hp
      · exact hindex it b _ p rfl hp
      · cases hp; exact SHole.sound_indexCapture σ lhs it b _ _
    · cases hp; exact SHole.sound_indexRecvCapture σ lhs it b i _

/-- `memoryFieldRead_unfold_rightFst`: the receiver bound first. -/
theorem MHole.sound_fieldCapture {T : Ty} (lhs : MHole C Γ T) {s : Name}
    (b : MPath C Γ (.struct s)) (hm : (Ty.ref (.struct s)).mapFree = true) (f : Name)
    (hf : C.fieldType s f = some T) (x : Var) :
    Premise.Runs m (lhs.fill (.field b f hf))
      (.captureMV x b (lhs.up.fill (.field (.var .here hm) f hf))) σ := by
  refine Premise.sound_captureMVSim σ (fun r hr => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ _ (MHole.fill_pushT σ (t := .mem (.struct s)) (some r) lhs _
      (.field b f hf) ?_)
    simp only [MLoc.addrT, hr]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.field b f hf)).run σ).map _ = _
    rw [MHole.fill_run]
    simp only [MLoc.addrT, hh]; rfl

/-- `memoryIndexRead_unfold_rightFst`: the receiver bound first. -/
theorem MHole.sound_indexRecvCapture {T : Ty} (lhs : MHole C Γ T) {R : RefTy} (a : ArrTy R T)
    (b : MPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (x : Var) :
    Premise.Runs m (lhs.fill (.index a b i))
      (.captureMV x b (lhs.up.fill (.index a (.var .here hm) i.up))) σ := by
  refine Premise.sound_captureMVSim σ (fun r hr => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ _ (MHole.fill_pushT σ (t := .mem R) (some r) lhs _ (.index a b i) ?_)
    simp only [MLoc.addrT, Val.evalT_up, hr]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.index a b i)).run σ).map _ = _
    rw [MHole.fill_run]
    simp only [MLoc.addrT, hh]; rfl

/-- `memoryIndexRead_unfold_rightSndIndex`: the index captured. -/
theorem MHole.sound_indexCapture {T : Ty} (lhs : MHole C Γ T) {R : RefTy} (a : ArrTy R T)
    (b : MPath C Γ (.ref R)) (i : Val C Γ .uint) (x : Var) :
    Premise.Runs m (lhs.fill (.index a b i))
      (.capture .uint x i (lhs.up.fill (.index a b.up (.simple (.local .here))))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine runSt_pushed σ _ (MHole.fill_pushT σ (t := .val .uint) v lhs _ (.index a b i) ?_)
    simp only [MLoc.addrT, MPath.mvalT_up, hv]; rfl
  · show TRes.Sim _ (((lhs.fill (.index a b i)).run σ).map _)
    rw [MHole.fill_run]
    simp only [MLoc.addrT, bind_assoc, TRes.map_bind]
    refine TRes.Sim.err_bind (MPath.mvalT_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact TRes.Sim.refl _

/-- **A memory read unfolded into a hole** (`MHole.readStep`) is sound when
the hole's own rules are. -/
theorem MHole.readStep_sound (k : Nat) {T : Ty} (lhs : MHole C Γ T)
    {field : {s : Name} → (mv : Idx Γ (.mem (.struct s))) → (Ty.ref (.struct s)).mapFree = true →
      (f : Name) → C.fieldType s f = some T → Premise C Γ Γ}
    {index : {R : RefTy} → ArrTy R T → (mv : Idx Γ (.mem R)) → (Ty.ref R).mapFree = true →
      Simple C Γ .uint → Premise C Γ Γ}
    (hfield : ∀ {s : Name} (mv : Idx Γ (.mem (.struct s))) hmv f hf p, field mv hmv f hf = p →
      Premise.Runs m (lhs.fill (.field (.var mv hmv) f hf)) p σ)
    (hindex : ∀ {R : RefTy} (a : ArrTy R T) (mv : Idx Γ (.mem R)) hmv (ie : Simple C Γ .uint) p,
      index a mv hmv ie = p →
        Premise.Runs m (lhs.fill (.index a (.var mv hmv) (.simple ie))) p σ)
    (l : MLoc C Γ T) (p : Premise C Γ Γ) (hp : lhs.readStep k field index l = p) :
    Premise.Runs m (lhs.fill l) p σ := by
  cases l with
  | field b f hf =>
    cases b with
    | var mv hmv => exact hfield mv hmv f hf p hp
    | loc l => cases hp; exact MHole.sound_fieldCapture σ lhs _ _ f hf _
  | index a b i =>
    cases b with
    | var mv hmv =>
      cases i with
      | simple ie => exact hindex a mv hmv ie p hp
      | _ => cases hp; exact MHole.sound_indexCapture σ lhs a (.var mv hmv) _ _
    | loc l => cases hp; exact MHole.sound_indexRecvCapture σ lhs a _ _ _ _

/-- `…ValueRhsCapture`, `…UnfoldSource`: `T se = nse; lhs = se;`. -/
theorem VHole.sound_capture {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) (x : Var) :
    Premise.Runs m (lhs.fill e) (.capture p x e (lhs.up.fill (.simple (.local .here)))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact runSt_pushed σ _ (VHole.fill_pushT σ (t := .val p) v lhs _ e (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill e).run σ).map _ = _
    rw [VHole.fill_run, hh]; rfl

/-- `ternaryCaptureCond`: the condition captured first. -/
theorem VHole.sound_ternaryCapture {p : PrimTy} (lhs : VHole C Γ p) (c : Val C Γ .bool)
    (a b : Val C Γ p) (x : Var) :
    Premise.Runs m (lhs.fill (.ternary c a b))
      (.capture .bool x c (lhs.up.fill (.ternary (.simple (.local .here)) a.up b.up))) σ := by
  refine Premise.sound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine runSt_pushed σ _ (VHole.fill_pushT σ (t := .val .bool) v lhs _ (.ternary c a b) ?_)
    simp only [Val.evalT, Val.evalT_up, hv]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.ternary c a b)).run σ).map _ = _
    rw [VHole.fill_run]
    simp only [Val.evalT, hh]; rfl

/-- An `if` on a simple condition, typed: the branch it picks, its locals
popped. -/
theorem Stmt.runSt_ite_simple {Γ₁ Γ₂ : Ctx} (se : Simple C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) :
    Stmt.runSt σ (.ite (.simple se) thn els) =
      if boolT (se.evalT σ) then (Prog.runSt σ thn).map (State.drop thn.ext)
      else (Prog.runSt σ els).map (State.drop els.ext) := by
  show ((TRun.ite (.simple se) thn.ext thn.runR els.ext els.runR σ).map (·.st)) = _
  simp only [TRun.ite, Val.evalT, ok_bind, Prog.runSt]
  split
  · show _ = ((thn.runR σ).map _).map _
    cases thn.runR σ <;> rfl
  · show _ = ((els.runR σ).map _).map _
    cases els.runR σ <;> rfl

/-- A value hole filled runs as the value, then what the hole does with it. -/
theorem VHole.runSt_fill {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) :
    Stmt.runSt σ (lhs.fill e) = (e.evalT σ >>= lhs.contT σ).map (·.st) := by
  show ((lhs.fill e).run σ).map _ = _
  rw [VHole.fill_run]

/-- `ternaryToIf`: `lhs = se ? a : b;` is `if (se) lhs = a; else lhs = b;`. -/
theorem VHole.sound_ternaryToIf {p : PrimTy} (lhs : VHole C Γ p) (se : Simple C Γ .bool)
    (a b : Val C Γ p) :
    Premise.Runs m (lhs.fill (.ternary (.simple se) a b))
      (.unfold (.cons (.ite (.simple se) (.cons (lhs.fill a) .nil) (.cons (lhs.fill b) .nil)) .nil)
        .refl) σ := by
  refine Premise.sound_unfold σ ?_
  rw [Prog.runSt_single, Stmt.runSt_ite_simple, VHole.runSt_fill, Prog.runSt_single,
    Prog.runSt_single, VHole.runSt_fill, VHole.runSt_fill]
  simp only [Val.evalT, ok_bind, TRes.map_drop_self]
  cases boolT (se.evalT σ) <;> rfl

/-- **A conditional into a hole** (`ternaryStep`). -/
theorem ternaryStep_sound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p) (c : Val C Γ .bool)
    (a b : Val C Γ p) (q : Premise C Γ Γ) (hq : ternaryStep k lhs c a b = q) :
    Premise.Runs m (lhs.fill (.ternary c a b)) q σ := by
  cases c with
  | simple se => cases hq; exact VHole.sound_ternaryToIf σ lhs se a b
  | _ => cases hq; exact VHole.sound_ternaryCapture σ lhs _ a b _

/-- **A value into a hole** (`VHole.step`): sound when the hole's own rule is. -/
theorem VHole.step_sound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p)
    {simple : Simple C Γ p → Premise C Γ Γ}
    (hsimple : ∀ se q, simple se = q → Premise.Runs m (lhs.fill (.simple se)) q σ)
    (e : Val C Γ p) (q : Premise C Γ Γ) (hq : lhs.step k simple e = q) :
    Premise.Runs m (lhs.fill e) q σ := by
  cases e with
  | simple se => exact hsimple se q hq
  | ternary c a b => exact ternaryStep_sound σ k lhs c a b q hq
  | _ => cases hq; exact VHole.sound_capture σ lhs _ _

/-- **A value into a hole, lowered first** (`VHole.lower`). -/
theorem VHole.lower_sound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p)
    {other : Premise C Γ Γ} (e : Val C Γ p)
    (hother : ∀ q, other = q → Premise.Runs m (lhs.fill e) q σ)
    (q : Premise C Γ Γ) (hq : lhs.lower k other e = q) :
    Premise.Runs m (lhs.fill e) q σ := by
  cases e with
  | ternary c a b => exact ternaryStep_sound σ k lhs c a b q hq
  | _ => exact hother q hq

end ReadSteps

/-! ## A statement read with a local pushed runs as before

`Calculus/SoundArms.lean`'s push lemmas over the typed run: a
capture's statement, read from the state with the fresh local pushed, runs
as the statement it replaces, its outcome lifted along `up` (`pushedT`),
given that its parts read as the replaced statement's do. -/

section PushT

variable {Γ : Ctx} {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H)

/-- The outcome of a run from `σ`, the local `w` pushed on its state (over
the heap it grew, `w` weakened along). -/
abbrev pushedT (r : TRes (Out C σ.H Γ)) : TRes (Out C σ.H (t :: Γ)) :=
  liftedT up (w, σ.env) r

/-- An outcome with a value, the local pushed. -/
abbrev pushedT₂ {α : Type} (r : TRes (Out C σ.H Γ × α)) : TRes (Out C σ.H (t :: Γ) × α) :=
  liftedT₂ up (w, σ.env) r

theorem opStoreT_push (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    opStoreT (σ.push w) op r v = pushedT σ w (opStoreT σ op r v) :=
  opStoreT_lift up σ (w, σ.env) op r v

theorem opMemT_push (op : BinOp) {p : PrimTy} (a : MAddr σ.H (.prim p)) (v : p.Denote) :
    opMemT (σ.push w) op a v = pushedT σ w (opMemT σ op a v) :=
  opMemT_lift up σ (w, σ.env) op a v

theorem bumpStoreT_push (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    bumpStoreT (σ.push w) op r = pushedT₂ σ w (bumpStoreT σ op r) :=
  bumpStoreT_lift up σ (w, σ.env) op r

theorem bumpMemT_push (op : IncDec) {p : PrimTy} (a : MAddr σ.H (.prim p)) :
    bumpMemT (σ.push w) op a = pushedT₂ σ w (bumpMemT σ op a) :=
  bumpMemT_lift up σ (w, σ.env) op a

theorem clearT_push {T : Ty} (a : MAddr σ.H T) (hm : T.mapFree = true) :
    TRun.clearT (σ.push w) a hm = pushedT σ w (TRun.clearT σ a hm) :=
  clearT_lift up σ (w, σ.env) a hm

theorem sendT_push (pv : Idx Γ (.val .bool)) (addr amt : PrimTy.uint.Denote) :
    sendT (σ.push w) pv.there addr amt = Out.lift up (w, σ.env) (sendT σ pv addr amt) := by
  rw [← Idx.up_eq pv]
  exact sendT_lift up σ (w, σ.env) pv addr amt

theorem MRhs.evalT_up {R : RefTy} (r : MRhs C Γ R) :
    (r.up (t := t)).evalT (σ.push w) = (r.evalT σ).map (Grew.lift Solidity.up (w, σ.env)) := by
  rw [MRhs.up_eq]; exact MRhs.evalT_wk Solidity.up σ (w, σ.env) r

/-- A compound target read with a local pushed as `l` reads (`OpLoc.Agree`,
typed). -/
inductive OpLoc.AgreeT : {p : PrimTy} → OpLoc C (t :: Γ) p → OpLoc C Γ p → Prop
  | «local» {p : PrimTy} (i : Idx Γ (.val p)) : OpLoc.AgreeT (.local i.there) (.local i)
  | root {p : PrimTy} (r : Name) (h : C.rootType r = some (.prim p)) :
      OpLoc.AgreeT (.root r h) (.root r h)
  | field {s : Name} {p : PrimTy} {b' : SPath C (t :: Γ) (.struct s)} {b : SPath C Γ (.struct s)}
      (f : Name) (h : C.fieldType s f = some (.prim p))
      (hb : b'.resolveT (σ.push w) = b.resolveT σ) :
      OpLoc.AgreeT (.field b' f h) (.field b f h)
  | index {R : RefTy} {k p : PrimTy} (it : IndexTy R k (.prim p)) {b' : SPath C (t :: Γ) (.ref R)}
      {b : SPath C Γ (.ref R)} {i' : Simple C (t :: Γ) k} {i : Simple C Γ k}
      (hb : b'.resolveT (σ.push w) = b.resolveT σ) (hi : i'.evalT (σ.push w) = i.evalT σ) :
      OpLoc.AgreeT (.index it b' i') (.index it b i)
  | mfield {s : Name} {p : PrimTy} {b' : MPath C (t :: Γ) (.struct s)} {b : MPath C Γ (.struct s)}
      (f : Name) (h : C.fieldType s f = some (.prim p)) (hb : b'.mvalT (σ.push w) = b.mvalT σ) :
      OpLoc.AgreeT (.mfield b' f h) (.mfield b f h)
  | mindex {R : RefTy} {p : PrimTy} (a : ArrTy R (.prim p)) {b' : MPath C (t :: Γ) (.ref R)}
      {b : MPath C Γ (.ref R)} {i' : Simple C (t :: Γ) .uint} {i : Simple C Γ .uint}
      (hb : b'.mvalT (σ.push w) = b.mvalT σ) (hi : i'.evalT (σ.push w) = i.evalT σ) :
      OpLoc.AgreeT (.mindex a b' i') (.mindex a b i)

theorem OpLoc.AgreeT.of_up {p : PrimTy} (l : OpLoc C Γ p) : OpLoc.AgreeT σ w l.up l := by
  cases l with
  | «local» i => exact .local i
  | root r h => exact .root r h
  | field b f h => exact .field f h (SPath.resolveT_up σ w b)
  | index it b i => exact .index it (SPath.resolveT_up σ w b) (Simple.evalT_up σ w i)
  | mfield b f h => exact .mfield f h (MPath.mvalT_up σ w b)
  | mindex a b i => exact .mindex a (MPath.mvalT_up σ w b) (Simple.evalT_up σ w i)

variable {σ w} in
theorem OpLoc.AgreeT.storeT {p : PrimTy} {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (h : OpLoc.AgreeT σ w l' l) (op : BinOp) (v : p.Denote) :
    l'.storeT (σ.push w) op v = pushedT σ w (l.storeT σ op v) := by
  cases h with
  | «local» i =>
    simp only [OpLoc.storeT, liftedT_bind]
    lift_fin
  | root r h => exact opStoreT_push σ w op _ v
  | field f h hb =>
    simp only [OpLoc.storeT, Loc.resolveT, hb, liftedT_bind, opStoreT_push, bind_assoc] <;> rfl
  | index it hb hi =>
    simp only [OpLoc.storeT, Loc.resolveT, Val.evalT, hb, hi, liftedT_bind, opStoreT_push,
      bind_assoc] <;> rfl
  | mfield f h hb =>
    simp only [OpLoc.storeT, MLoc.addrT, hb, liftedT_bind, opMemT_push, bind_assoc] <;> rfl
  | mindex a hb hi =>
    simp only [OpLoc.storeT, MLoc.addrT, Val.evalT, hb, hi, liftedT_bind, opMemT_push, bind_assoc] <;> rfl

variable {σ w} in
theorem OpLoc.AgreeT.bumpT {p : PrimTy} {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (h : OpLoc.AgreeT σ w l' l) (op : IncDec) :
    l'.bumpT (σ.push w) op = pushedT₂ σ w (l.bumpT σ op) := by
  cases h with
  | «local» i =>
    simp only [OpLoc.bumpT, liftedT₂_bind]
    lift_fin
  | root r h => exact bumpStoreT_push σ w op _
  | field f h hb =>
    simp only [OpLoc.bumpT, Loc.resolveT, hb, liftedT₂_bind, bumpStoreT_push, bind_assoc] <;> rfl
  | index it hb hi =>
    simp only [OpLoc.bumpT, Loc.resolveT, Val.evalT, hb, hi, liftedT₂_bind, bumpStoreT_push,
      bind_assoc] <;> rfl
  | mfield f h hb =>
    simp only [OpLoc.bumpT, MLoc.addrT, hb, liftedT₂_bind, bumpMemT_push, bind_assoc] <;> rfl
  | mindex a hb hi =>
    simp only [OpLoc.bumpT, MLoc.addrT, Val.evalT, hb, hi, liftedT₂_bind, bumpMemT_push,
      bind_assoc] <;> rfl

theorem TRun.assignLocal_pushT {p : PrimTy} (i : Idx Γ (.val p)) (v' : Val C (t :: Γ) p)
    (v : Val C Γ p) (hv : v'.evalT (σ.push w) = v.evalT σ) :
    TRun.assignLocal i.there v' (σ.push w) = pushedT σ w (TRun.assignLocal i v σ) := by
  simp only [TRun.assignLocal, hv, liftedT_bind]
  lift_fin

theorem TRun.assign_pushT {T : Ty} (l' : Loc C (t :: Γ) T) (r' : Src C (t :: Γ) T)
    (l : Loc C Γ T) (r : Src C Γ T) (hr : r'.valueT (σ.push w) = r.valueT σ)
    (hl : l'.resolveT (σ.push w) = l.resolveT σ) :
    TRun.assign l' r' (σ.push w) = pushedT σ w (TRun.assign l r σ) := by
  simp only [TRun.assign, hr, hl, liftedT_bind]
  lift_fin

theorem TRun.rebind_pushT {R : RefTy} (i : Idx Γ (.alias R)) (r' : ARhs C (t :: Γ) R)
    (r : ARhs C Γ R) (hr : r'.evalT (σ.push w) = r.evalT σ) :
    TRun.rebind i.there r' (σ.push w) = pushedT σ w (TRun.rebind i r σ) := by
  simp only [TRun.rebind, hr, liftedT_bind]
  lift_fin

theorem TRun.opAssign_pushT {p : PrimTy} (op : BinOp) {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (hl : OpLoc.AgreeT σ w l' l) (v' : Val C (t :: Γ) p) (v : Val C Γ p)
    (hv : v'.evalT (σ.push w) = v.evalT σ) :
    TRun.opAssign op l' v' (σ.push w) = pushedT σ w (TRun.opAssign op l v σ) := by
  simp only [TRun.opAssign, hv, hl.storeT, liftedT_bind]

theorem TRun.incDec_pushT {p : PrimTy} (op : IncDec) {l' : OpLoc C (t :: Γ) p} {l : OpLoc C Γ p}
    (hl : OpLoc.AgreeT σ w l' l) :
    TRun.incDec op l' (σ.push w) = pushedT σ w (TRun.incDec op l σ) := by
  simp only [TRun.incDec, hl.bumpT]
  cases l.bumpT σ op <;> rfl

theorem TRun.push_none_pushT {E : Ty} (b' : SPath C (t :: Γ) (.array E)) (b : SPath C Γ (.array E))
    (hb : b'.resolveT (σ.push w) = b.resolveT σ) :
    TRun.push b' none (σ.push w) = pushedT σ w (TRun.push b none σ) := by
  simp only [TRun.push, hb, liftedT_bind, liftedT_ite, liftedT_error]
  lift_fin

theorem TRun.push_some_pushT {E : Ty} (b' : SPath C (t :: Γ) (.array E)) (b : SPath C Γ (.array E))
    (r' : Src C (t :: Γ) E) (r : Src C Γ E) (hb : b'.resolveT (σ.push w) = b.resolveT σ)
    (hr : r'.valueT (σ.push w) = r.valueT σ) :
    TRun.push b' (some r') (σ.push w) = pushedT σ w (TRun.push b (some r) σ) := by
  simp only [TRun.push, hb, hr, liftedT_bind, liftedT_ite, liftedT_error]
  lift_fin

theorem TRun.pop_pushT {E : Ty} (b' : SPath C (t :: Γ) (.array E)) (b : SPath C Γ (.array E))
    (hb : b'.resolveT (σ.push w) = b.resolveT σ) :
    TRun.pop b' (σ.push w) = pushedT σ w (TRun.pop b σ) := by
  simp only [TRun.pop, hb, liftedT_bind]
  lift_fin

theorem TRun.transfer_pushT (r' a' : Val C (t :: Γ) .uint) (r a : Val C Γ .uint)
    (hr : r'.evalT (σ.push w) = r.evalT σ) (ha : a'.evalT (σ.push w) = a.evalT σ) :
    TRun.transfer r' a' (σ.push w) = pushedT σ w (TRun.transfer r a σ) := by
  simp only [TRun.transfer, hr, ha, liftedT_bind]
  lift_fin

theorem TRun.send_pushT (pv : Idx Γ (.val .bool)) (r' a' : Val C (t :: Γ) .uint)
    (r a : Val C Γ .uint) (hr : r'.evalT (σ.push w) = r.evalT σ)
    (ha : a'.evalT (σ.push w) = a.evalT σ) :
    TRun.send pv.there r' a' (σ.push w) = pushedT σ w (TRun.send pv r a σ) := by
  simp only [TRun.send, hr, ha, liftedT_bind, sendT_push, liftedT_pure]

theorem TRun.rebindMem_pushT {R : RefTy} (i : Idx Γ (.mem R)) (r' : MRhs C (t :: Γ) R)
    (r : MRhs C Γ R) (hr : r'.evalT (σ.push w) = (r.evalT σ).map (Grew.lift up (w, σ.env))) :
    TRun.rebindMem i.there r' (σ.push w) = pushedT σ w (TRun.rebindMem i r σ) := by
  simp only [TRun.rebindMem, hr]
  cases r.evalT σ with
  | error => rfl
  | ok g =>
    show Except.ok (⟨(g.st.lift up (TEnv.wk g.ext _ (w, σ.env))).setLocal i.there
        (some g.val), g.ext⟩ : Out C σ.H (t :: Γ)) =
      Except.ok ⟨(g.st.setLocal i (some g.val)).lift up (TEnv.wk g.ext _ (w, σ.env)), g.ext⟩
    rw [← Idx.up_eq i]
    simp only [State.lift_setLocal]

theorem TRun.assignFromMem_pushT {R : RefTy} (l' : Loc C (t :: Γ) (.ref R)) (l : Loc C Γ (.ref R))
    (p' : MPath C (t :: Γ) (.ref R)) (p : MPath C Γ (.ref R))
    (hp : p'.mvalT (σ.push w) = p.mvalT σ) (hl : l'.resolveT (σ.push w) = l.resolveT σ) :
    TRun.assignFromMem l' p' (σ.push w) = pushedT σ w (TRun.assignFromMem l p σ) := by
  simp only [TRun.assignFromMem, hp, hl, liftedT_bind]
  lift_fin

theorem TRun.assignMem_pushT {T : Ty} (l' : MLoc C (t :: Γ) T) (l : MLoc C Γ T)
    (r' : MSrc C (t :: Γ) T) (r : MSrc C Γ T) (hl : l'.addrT (σ.push w) = l.addrT σ)
    (hr : r'.mvalT (σ.push w) = r.mvalT σ) :
    TRun.assignMem l' r' (σ.push w) = pushedT σ w (TRun.assignMem l r σ) := by
  simp only [TRun.assignMem, hr, hl, liftedT_bind]
  lift_fin

theorem TRun.delete_pushT {T : Ty} (l' : Loc C (t :: Γ) T) (l : Loc C Γ T)
    (hl : l'.resolveT (σ.push w) = l.resolveT σ) :
    TRun.delete l' (σ.push w) = pushedT σ w (TRun.delete l σ) := by
  simp only [TRun.delete, hl, liftedT_bind]
  lift_fin

theorem TRun.deleteMem_pushT {T : Ty} (l' : MLoc C (t :: Γ) T) (l : MLoc C Γ T)
    (hl : l'.addrT (σ.push w) = l.addrT σ) :
    TRun.deleteMem (.loc l') (σ.push w) = pushedT σ w (TRun.deleteMem (.loc l) σ) := by
  simp only [TRun.deleteMem, hl, liftedT_bind]
  congr 1; funext a
  exact clearT_push σ w a _

theorem TRun.require_pushT (c' : Val C (t :: Γ) .bool) (c : Val C Γ .bool)
    (hc : c'.evalT (σ.push w) = c.evalT σ) :
    TRun.require c' (σ.push w) = pushedT σ w (TRun.require c σ) := by
  simp only [TRun.require, hc, liftedT_bind, liftedT_ite, liftedT_pure, liftedT_error]
  lift_fin

theorem TRun.assert_pushT (c' : Val C (t :: Γ) .bool) (c : Val C Γ .bool)
    (hc : c'.evalT (σ.push w) = c.evalT σ) :
    TRun.assert c' (σ.push w) = pushedT σ w (TRun.assert c σ) := by
  simp only [TRun.assert, hc, liftedT_bind, liftedT_ite, liftedT_pure, liftedT_error]
  lift_fin

end PushT

end Solidity
