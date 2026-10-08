import Solidity.Calculus.Core.TSoundArms

/-!
# Soundness over the typed state: captures, and the holes a read lands in

`Calculus/Core/SoundCapture.lean` over the typed run.  A rule that captures a
part (`T se = nse; s'`, `T storage sp = nsp; s'`, `T memory mv = nmp; s'`)
is sound when `s'`, read with the part's value on top, runs as the statement
it replaces, and the statement halts alike where the part halts
(`Premise.tsound_captureSim` and its kin, `Calculus/Core/TSoundKit.lean`).

A statement read with a local pushed runs as before, its outcome lifted
along `up` (`liftedT`, `Semantics/Core/TypedRunWk.lean`): a hole filled is
the read and then what the hole does with it (`SHole.contT`, `MHole.contT`,
`VHole.contT`), and the hole shifted under a local does the same, lifted
(`*.contT_up`), so a rule that unfolds a read is sound for every hole at
once.
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-! ## A statement run with a local pushed -/

section Pushed

variable {Γ : Ctx} {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H)

/-- A statement that runs, from `σ` with `w` pushed, as `s` from `σ` lifted
runs as `s` once the local is popped. -/
theorem trunSt_pushed {s' : Stmt C (t :: Γ) (t :: Γ)} {s : Stmt C Γ Γ}
    (h : s'.trun (σ.push w) = liftedT Core.up (w, σ.env) (s.trun σ)) :
    (Stmt.trunSt (σ.push w) s').map (TState.drop (.push .refl)) = Stmt.trunSt σ s := by
  show ((s'.trun (σ.push w)).map (·.st)).map _ = (s.trun σ).map (·.st)
  rw [h]
  exact liftedT_up_drop σ w _

end Pushed

/-! ## Holes: the read, then what the hole does with it -/

section Holes

variable {Γ : Ctx}

/-- What a storage hole does with the reference it is given: `v = find(…)`,
`lsv = p`, `loc = copy(…)`. -/
def SHole.contT : {T : Ty} → SHole C Γ T → (σ : TState C Γ) → SRef C T → TRes (Out C σ.H Γ)
  | _, .local i, σ, r => do
    let v ← TRes.ofOpt (σ.storage.find r)
    pure ⟨σ.setLocal i v.view, List.prefix_refl _⟩
  | _, .rebind i, σ, r => pure ⟨σ.setLocal i (some r), List.prefix_refl _⟩
  | _, .copy l _, σ, r => do
    let sv ← TRes.ofOpt (σ.storage.find r)
    let ref ← l.resolveT σ
    let st ← TRes.ofOpt (σ.storage.write ref sv)
    pure ⟨σ.withStorage st, List.prefix_refl _⟩

theorem SHole.fill_trun (σ : TState C Γ) {T : Ty} (lhs : SHole C Γ T) (l : Loc C Γ T) :
    (lhs.fill (.loc l)).trun σ = l.resolveT σ >>= lhs.contT σ := by
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

theorem SHole.contT_up {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : SHole C Γ T) (r : SRef C T) :
    lhs.up.contT (σ.push w) r = liftedT Core.up (w, σ.env) (lhs.contT σ r) := by
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

theorem SHole.fill_pushT {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : SHole C Γ T) (l' : Loc C (t :: Γ) T) (l : Loc C Γ T)
    (hl : l'.resolveT (σ.push w) = l.resolveT σ) :
    (lhs.up.fill (.loc l')).trun (σ.push w) =
      liftedT Core.up (w, σ.env) ((lhs.fill (.loc l)).trun σ) := by
  rw [SHole.fill_trun, SHole.fill_trun, hl, liftedT_bind]
  congr 1; funext q; exact SHole.contT_up σ w lhs q

/-- What a memory hole does with the address it is given: `v = read(…)`,
`mv = r`, `mloc = r`. -/
def MHole.contT : {T : Ty} → MHole C Γ T → (σ : TState C Γ) → MAddr σ.H T → TRes (Out C σ.H Γ)
  | _, .local i, σ, a => do
    let v ← TRes.ofOpt (σ.heap.readAddr a)
    pure ⟨σ.setLocal i v, List.prefix_refl _⟩
  | _, .rebind i, σ, a => do
    let r ← TRes.ofOpt (σ.heap.readAddr a)
    pure ⟨σ.setLocal i r, List.prefix_refl _⟩
  | _, .write l, σ, a => do
    let mv ← TRes.ofOpt (σ.heap.readAddr a)
    let a' ← l.addrT σ
    let hp ← TRes.ofOpt (σ.heap.writeAddr a' mv)
    pure ⟨σ.withHeap hp, List.prefix_refl _⟩

theorem MHole.fill_trun (σ : TState C Γ) {T : Ty} (lhs : MHole C Γ T) (l : MLoc C Γ T) :
    (lhs.fill l).trun σ = l.addrT σ >>= lhs.contT σ := by
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

theorem MHole.contT_up {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : MHole C Γ T) (a : MAddr σ.H T) :
    lhs.up.contT (σ.push w) a = liftedT Core.up (w, σ.env) (lhs.contT σ a) := by
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

theorem MHole.fill_pushT {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H) {T : Ty}
    (lhs : MHole C Γ T) (l' : MLoc C (t :: Γ) T) (l : MLoc C Γ T)
    (hl : l'.addrT (σ.push w) = l.addrT σ) :
    (lhs.up.fill l').trun (σ.push w) = liftedT Core.up (w, σ.env) ((lhs.fill l).trun σ) := by
  rw [MHole.fill_trun, MHole.fill_trun, hl, liftedT_bind]
  congr 1; funext q; exact MHole.contT_up σ w lhs q

/-- What a value hole does with the value it is given: `v = e`, `loc = e`,
`mloc = e`. -/
def VHole.contT {p : PrimTy} : VHole C Γ p → (σ : TState C Γ) → p.Denote → TRes (Out C σ.H Γ)
  | .local i, σ, v => pure ⟨σ.setLocal i v, List.prefix_refl _⟩
  | .store l, σ, v => do
    let ref ← l.resolveT σ
    let st ← TRes.ofOpt (σ.storage.write ref (.prim v))
    pure ⟨σ.withStorage st, List.prefix_refl _⟩
  | .mem l, σ, v => do
    let a ← l.addrT σ
    let hp ← TRes.ofOpt (σ.heap.writeAddr a v)
    pure ⟨σ.withHeap hp, List.prefix_refl _⟩

theorem VHole.fill_trun (σ : TState C Γ) {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) :
    (lhs.fill e).trun σ = e.evalT σ >>= lhs.contT σ := by
  cases lhs with
  | «local» i => rfl
  | store l =>
    show TRun.assign l (.val e) σ = _
    simp only [TRun.assign, Src.valueT, bind_assoc, pure_bind]; rfl
  | mem l =>
    show TRun.assignMem l (.val e) σ = _
    simp only [TRun.assignMem, MSrc.mvalT]; rfl

theorem VHole.contT_up {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H) {p : PrimTy}
    (lhs : VHole C Γ p) (v : p.Denote) :
    lhs.up.contT (σ.push w) v = liftedT Core.up (w, σ.env) (lhs.contT σ v) := by
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

theorem VHole.fill_pushT {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H) {p : PrimTy}
    (lhs : VHole C Γ p) (e' : Val C (t :: Γ) p) (e : Val C Γ p)
    (he : e'.evalT (σ.push w) = e.evalT σ) :
    (lhs.up.fill e').trun (σ.push w) = liftedT Core.up (w, σ.env) ((lhs.fill e).trun σ) := by
  rw [VHole.fill_trun, VHole.fill_trun, he, liftedT_bind]
  congr 1; funext q; exact VHole.contT_up σ w lhs q

end Holes

/-! ## A read unfolded into a hole -/

section ReadSteps

variable {Γ : Ctx} {m : Modality} (σ : TState C Γ)

/-- `storageFieldRead_unfold_rightFst`: the receiver bound first. -/
theorem SHole.tsound_fieldCapture {T : Ty} (lhs : SHole C Γ T) {s : Name}
    (b : SPath C Γ (.struct s)) (f : Name) (hf : C.fieldType s f = some T) (x : Var) :
    Premise.TSound m (lhs.fill (.loc (.field b f hf)))
      (.captureSP x b (lhs.up.fill (.loc (.field (.alias .here) f hf)))) σ := by
  refine Premise.tsound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ _ (SHole.fill_pushT σ (t := .alias (.struct s)) (some q) lhs _ (.field b f hf) ?_)
    simp only [Loc.resolveT, hq]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.loc (.field b f hf))).trun σ).map _ = _
    rw [SHole.fill_trun]
    simp only [Loc.resolveT, hh]; rfl

/-- `storageIndexRead_unfold_rightFst`: the receiver bound first. -/
theorem SHole.tsound_indexRecvCapture {T : Ty} (lhs : SHole C Γ T) {R : RefTy} {kp : PrimTy}
    (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.TSound m (lhs.fill (.loc (.index it b i)))
      (.captureSP x b (lhs.up.fill (.loc (.index it (.alias .here) i.up)))) σ := by
  refine Premise.tsound_captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ _ (SHole.fill_pushT σ (t := .alias R) (some q) lhs _ (.index it b i) ?_)
    simp only [Loc.resolveT, Val.evalT_up, hq]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.loc (.index it b i))).trun σ).map _ = _
    rw [SHole.fill_trun]
    simp only [Loc.resolveT, hh]; rfl

/-- `storageIndexRead_unfold_rightSndIndex`: the index captured, the receiver
(simple) read after it. -/
theorem SHole.tsound_indexCapture {T : Ty} (lhs : SHole C Γ T) {R : RefTy} {kp : PrimTy}
    (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.TSound m (lhs.fill (.loc (.index it b i)))
      (.capture kp x i (lhs.up.fill (.loc (.index it b.up (.simple (.local .here)))))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine trunSt_pushed σ _ (SHole.fill_pushT σ (t := .val kp) v lhs _ (.index it b i) ?_)
    simp only [Loc.resolveT, SPath.resolveT_up, hv]; rfl
  · show TRes.Sim _ (((lhs.fill (.loc (.index it b i))).trun σ).map _)
    rw [SHole.fill_trun]
    simp only [Loc.resolveT, bind_assoc, TRes.map_bind]
    refine TRes.Sim.err_bind (SPath.resolveT_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact TRes.Sim.refl _

/-- **A storage read unfolded into a hole** (`SHole.readStep`) is sound
when the hole's own rules are. -/
theorem SHole.readStep_tsound (k : Nat) {T : Ty} (lhs : SHole C Γ T)
    {root : (r : Name) → C.rootType r = some T → Option (Premise C Γ Γ)}
    {field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Option (Premise C Γ Γ)}
    {index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) → Simple C Γ kp →
      Option (Premise C Γ Γ)}
    (l : Loc C Γ T)
    (hroot : ∀ r h p, l = .root r h → root r h = some p →
      Premise.TSound m (lhs.fill (.loc (.root r h))) p σ)
    (hfield : ∀ {s : Name} (b : SPath C Γ (.struct s)) f hf p, l = .field b f hf →
      field b f hf = some p → Premise.TSound m (lhs.fill (.loc (.field b f hf))) p σ)
    (hindex : ∀ {R : RefTy} {kp : PrimTy} (it : IndexTy R kp T) b (ie : Simple C Γ kp) p,
      l = .index it b (.simple ie) → index it b ie = some p →
      Premise.TSound m (lhs.fill (.loc (.index it b (.simple ie)))) p σ)
    (p : Premise C Γ Γ) (hp : lhs.readStep k root field index l = some p) :
    Premise.TSound m (lhs.fill (.loc l)) p σ := by
  cases l with
  | root r h => exact hroot r h p rfl hp
  | field b f hf =>
    simp only [SHole.readStep] at hp
    split at hp
    · exact hfield b f hf p rfl hp
    · cases hp; exact SHole.tsound_fieldCapture σ lhs b f hf _
  | index it b i =>
    simp only [SHole.readStep] at hp
    split at hp
    · split at hp
      · exact hindex it b _ p rfl hp
      · cases hp; exact SHole.tsound_indexCapture σ lhs it b _ _
    · cases hp; exact SHole.tsound_indexRecvCapture σ lhs it b i _

/-- `memoryFieldRead_unfold_rightFst`: the receiver bound first. -/
theorem MHole.tsound_fieldCapture {T : Ty} (lhs : MHole C Γ T) {s : Name}
    (b : MPath C Γ (.struct s)) (hm : (Ty.ref (.struct s)).mapFree = true) (f : Name)
    (hf : C.fieldType s f = some T) (x : Var) :
    Premise.TSound m (lhs.fill (.field b f hf))
      (.captureMV x b (lhs.up.fill (.field (.var .here hm) f hf))) σ := by
  refine Premise.tsound_captureMVSim σ (fun r hr => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ _ (MHole.fill_pushT σ (t := .mem (.struct s)) r lhs _ (.field b f hf) ?_)
    simp only [MLoc.addrT, hr]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.field b f hf)).trun σ).map _ = _
    rw [MHole.fill_trun]
    simp only [MLoc.addrT, hh]; rfl

/-- `memoryIndexRead_unfold_rightFst`: the receiver bound first. -/
theorem MHole.tsound_indexRecvCapture {T : Ty} (lhs : MHole C Γ T) {R : RefTy} (a : ArrTy R T)
    (b : MPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (x : Var) :
    Premise.TSound m (lhs.fill (.index a b i))
      (.captureMV x b (lhs.up.fill (.index a (.var .here hm) i.up))) σ := by
  refine Premise.tsound_captureMVSim σ (fun r hr => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ _ (MHole.fill_pushT σ (t := .mem R) r lhs _ (.index a b i) ?_)
    simp only [MLoc.addrT, Val.evalT_up, hr]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.index a b i)).trun σ).map _ = _
    rw [MHole.fill_trun]
    simp only [MLoc.addrT, hh]; rfl

/-- `memoryIndexRead_unfold_rightSndIndex`: the index captured. -/
theorem MHole.tsound_indexCapture {T : Ty} (lhs : MHole C Γ T) {R : RefTy} (a : ArrTy R T)
    (b : MPath C Γ (.ref R)) (i : Val C Γ .uint) (x : Var) :
    Premise.TSound m (lhs.fill (.index a b i))
      (.capture .uint x i (lhs.up.fill (.index a b.up (.simple (.local .here))))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · refine trunSt_pushed σ _ (MHole.fill_pushT σ (t := .val .uint) v lhs _ (.index a b i) ?_)
    simp only [MLoc.addrT, MPath.mvalT_up, hv]; rfl
  · show TRes.Sim _ (((lhs.fill (.index a b i)).trun σ).map _)
    rw [MHole.fill_trun]
    simp only [MLoc.addrT, bind_assoc, TRes.map_bind]
    refine TRes.Sim.err_bind (MPath.mvalT_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact TRes.Sim.refl _

/-- **A memory read unfolded into a hole** (`MHole.readStep`) is sound when
the hole's own rules are. -/
theorem MHole.readStep_tsound (k : Nat) {T : Ty} (lhs : MHole C Γ T)
    {field : {s : Name} → (mv : Idx Γ (.mem (.struct s))) → (Ty.ref (.struct s)).mapFree = true →
      (f : Name) → C.fieldType s f = some T → Option (Premise C Γ Γ)}
    {index : {R : RefTy} → ArrTy R T → (mv : Idx Γ (.mem R)) → (Ty.ref R).mapFree = true →
      Simple C Γ .uint → Option (Premise C Γ Γ)}
    (hfield : ∀ {s : Name} (mv : Idx Γ (.mem (.struct s))) hmv f hf p, field mv hmv f hf = some p →
      Premise.TSound m (lhs.fill (.field (.var mv hmv) f hf)) p σ)
    (hindex : ∀ {R : RefTy} (a : ArrTy R T) (mv : Idx Γ (.mem R)) hmv (ie : Simple C Γ .uint) p,
      index a mv hmv ie = some p →
        Premise.TSound m (lhs.fill (.index a (.var mv hmv) (.simple ie))) p σ)
    (l : MLoc C Γ T) (p : Premise C Γ Γ) (hp : lhs.readStep k field index l = some p) :
    Premise.TSound m (lhs.fill l) p σ := by
  cases l with
  | field b f hf =>
    cases b with
    | var mv hmv => exact hfield mv hmv f hf p hp
    | loc l => cases hp; exact MHole.tsound_fieldCapture σ lhs _ _ f hf _
  | index a b i =>
    cases b with
    | var mv hmv =>
      cases i with
      | simple ie => exact hindex a mv hmv ie p hp
      | _ => cases hp; exact MHole.tsound_indexCapture σ lhs a (.var mv hmv) _ _
    | loc l => cases hp; exact MHole.tsound_indexRecvCapture σ lhs a _ _ _ _

/-- `…ValueRhsCapture`, `…UnfoldSource`: `T se = nse; lhs = se;`. -/
theorem VHole.tsound_capture {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) (x : Var) :
    Premise.TSound m (lhs.fill e) (.capture p x e (lhs.up.fill (.simple (.local .here)))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · exact trunSt_pushed σ _ (VHole.fill_pushT σ (t := .val p) v lhs _ e (by rw [hv]; rfl))
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill e).trun σ).map _ = _
    rw [VHole.fill_trun, hh]; rfl

/-- `ternaryCaptureCond`: the condition captured first. -/
theorem VHole.tsound_ternaryCapture {p : PrimTy} (lhs : VHole C Γ p) (c : Val C Γ .bool)
    (a b : Val C Γ p) (x : Var) :
    Premise.TSound m (lhs.fill (.ternary c a b))
      (.capture .bool x c (lhs.up.fill (.ternary (.simple (.local .here)) a.up b.up))) σ := by
  refine Premise.tsound_captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine trunSt_pushed σ _ (VHole.fill_pushT σ (t := .val .bool) v lhs _ (.ternary c a b) ?_)
    simp only [Val.evalT, Val.evalT_up, hv]; rfl
  · refine TRes.Sim.err_refl ?_
    show ((lhs.fill (.ternary c a b)).trun σ).map _ = _
    rw [VHole.fill_trun]
    simp only [Val.evalT, hh]; rfl

/-- An `if` on a simple condition, typed: the branch it picks, its locals
popped. -/
theorem Stmt.trunSt_ite_simple {Γ₁ Γ₂ : Ctx} (se : Simple C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) :
    Stmt.trunSt σ (.ite (.simple se) thn els) =
      if boolT (se.evalT σ) then (Prog.trunSt σ thn).map (TState.drop thn.ext)
      else (Prog.trunSt σ els).map (TState.drop els.ext) := by
  show ((TRun.ite (.simple se) thn.ext thn.trunR els.ext els.trunR σ).map (·.st)) = _
  simp only [TRun.ite, Val.evalT, ok_bind, Prog.trunSt]
  split
  · show _ = ((thn.trunR σ).map _).map _
    cases thn.trunR σ <;> rfl
  · show _ = ((els.trunR σ).map _).map _
    cases els.trunR σ <;> rfl

/-- A value hole filled runs as the value, then what the hole does with it. -/
theorem VHole.trunSt_fill {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) :
    Stmt.trunSt σ (lhs.fill e) = (e.evalT σ >>= lhs.contT σ).map (·.st) := by
  show ((lhs.fill e).trun σ).map _ = _
  rw [VHole.fill_trun]

/-- `ternaryToIf`: `lhs = se ? a : b;` is `if (se) lhs = a; else lhs = b;`. -/
theorem VHole.tsound_ternaryToIf {p : PrimTy} (lhs : VHole C Γ p) (se : Simple C Γ .bool)
    (a b : Val C Γ p) :
    Premise.TSound m (lhs.fill (.ternary (.simple se) a b))
      (.unfold (.cons (.ite (.simple se) (.cons (lhs.fill a) .nil) (.cons (lhs.fill b) .nil)) .nil)
        .refl) σ := by
  refine Premise.tsound_unfold σ ?_
  rw [Prog.trunSt_single, Stmt.trunSt_ite_simple, VHole.trunSt_fill, Prog.trunSt_single,
    Prog.trunSt_single, VHole.trunSt_fill, VHole.trunSt_fill]
  simp only [Val.evalT, ok_bind, TRes.map_drop_self]
  cases boolT (se.evalT σ) <;> rfl

/-- **A conditional into a hole** (`ternaryStep`). -/
theorem ternaryStep_tsound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p) (c : Val C Γ .bool)
    (a b : Val C Γ p) (q : Premise C Γ Γ) (hq : ternaryStep k lhs c a b = some q) :
    Premise.TSound m (lhs.fill (.ternary c a b)) q σ := by
  cases c with
  | simple se => cases hq; exact VHole.tsound_ternaryToIf σ lhs se a b
  | _ => cases hq; exact VHole.tsound_ternaryCapture σ lhs _ a b _

/-- **A value into a hole** (`VHole.step`): sound when the hole's own rule is. -/
theorem VHole.step_tsound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p)
    {simple : Simple C Γ p → Option (Premise C Γ Γ)}
    (hsimple : ∀ se q, simple se = some q → Premise.TSound m (lhs.fill (.simple se)) q σ)
    (e : Val C Γ p) (q : Premise C Γ Γ) (hq : lhs.step k simple e = some q) :
    Premise.TSound m (lhs.fill e) q σ := by
  cases e with
  | simple se => exact hsimple se q hq
  | ternary c a b => exact ternaryStep_tsound σ k lhs c a b q hq
  | _ => cases hq; exact VHole.tsound_capture σ lhs _ _

/-- **A value into a hole, lowered first** (`VHole.lower`). -/
theorem VHole.lower_tsound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p)
    {other : Option (Premise C Γ Γ)} (e : Val C Γ p)
    (hother : ∀ q, other = some q → Premise.TSound m (lhs.fill e) q σ)
    (q : Premise C Γ Γ) (hq : lhs.lower k other e = some q) :
    Premise.TSound m (lhs.fill e) q σ := by
  cases e with
  | ternary c a b => exact ternaryStep_tsound σ k lhs c a b q hq
  | _ => exact hother q hq

end ReadSteps

end Solidity.Core
