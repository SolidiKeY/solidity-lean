import Solidity.Calculus.Core.SoundUpdates

/-!
# Soundness of a capture, and of the holes a read lands in

A rule that captures a part (`T se = nse; s'`, `T storage sp = nsp; s'`,
`T memory mv = nmp; s'`) is sound when `s'`, read with the part's value on
top, runs as the statement it replaces (the push lemmas of
`Calculus/Core/SoundArms.lean`), and, the part halting, the statement halts
alike (`Res.Sim`): with the same halt where the statement reads the part
first, with some other halt that is not a panic where it reads another part
first (`Res.Sim.err_bind`; no expression panics, `Val.eval_noPanic`).

The holes of `Calculus/Core/Arms.lean` (`SHole`, `MHole`, `VHole`) are read
once here: a statement with a hole filled is the read and then what the
hole does with it (`SHole.cont`, `MHole.cont`, `VHole.cont`), so a rule
that unfolds a read (`SHole.readStep`, `MHole.readStep`, `VHole.step`) is
sound for every hole at once.
-/

namespace Solidity.Core

open Solidity (Modality Srt Op0 Op1 Op2 Op3 NoPanic)
open Semantics (Value SVal MVal Seg Halt Res)

variable {C : Contract}

/-! ## Captures, up to the halt -/

section Capture

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- A run that reads a part that does not panic first halts alike to `h`
when what follows does. -/
theorem Res.Sim.err_bind {α β : Type} {X : Res α} (hX : NoPanic X) {h : Halt} (hh : h ≠ .panic)
    {f : α → Res β} (hf : ∀ a, X = .ok a → Res.Sim (.error h) (f a)) :
    Res.Sim (.error h) (X >>= f) := by
  cases hx : X with
  | ok a => exact hf a hx
  | error h' =>
    rw [hx] at hX
    exact ⟨fun e => absurd e hh, fun e => absurd (congrArg Except.error e) hX⟩

theorem Res.bind_error {α β : Type} (h : Halt) (f : α → Res β) :
    ((Except.error h : Res α) >>= f) = .error h := rfl

theorem Res.Sim.err_refl {α : Type} {h : Halt} {r : Res α} (hr : r = .error h) :
    Res.Sim (.error h) r := hr ▸ Res.Sim.refl _

theorem Val.eval_err_ne {p : PrimTy} {e : Val C Γ p} {h : Halt} (he : e.eval σ = .error h) :
    h ≠ .panic := fun hp => Val.eval_noPanic σ e (hp ▸ he)

/-- **A value captured**: `T se = nse; s'` gives `s`, `s'` running as `s`
with the value on top, and `s` halting alike where `nse` halts. -/
theorem Premise.Sound.captureSim {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ}
    (hok : ∀ v, e.eval σ = .ok v → (s'.run (σ.push v)).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, e.eval σ = .error h → h ≠ .panic → Res.Sim (.error h) (s.run σ)) :
    Premise.Sound m s (.capture p x e s') σ := by
  refine Premise.Sound.captureK (fun v => (s'.run (σ.push v)).map (State.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases he : e.eval σ with
  | ok v => exact Res.Sim.of_eq (hok v he)
  | error h => exact herr h he (Val.eval_err_ne σ he)

/-- **A storage path captured**: `T storage sp = nsp; s'`. -/
theorem Premise.Sound.captureSPSim {R : RefTy} {x : Var} {b : SPath C Γ (.ref R)}
    {s' : Stmt C (.alias R :: Γ) (.alias R :: Γ)} {s : Stmt C Γ Γ}
    (hok : ∀ q, b.resolve σ = .ok q →
      (s'.run (σ.push (t := .alias R) (some q))).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, b.resolve σ = .error h → h ≠ .panic → Res.Sim (.error h) (s.run σ)) :
    Premise.Sound m s (.captureSP x b s') σ := by
  refine Premise.Sound.captureSPK
    (fun q => (s'.run (σ.push (t := .alias R) (some q))).map (State.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases hb : b.resolve σ with
  | ok q => exact Res.Sim.of_eq (hok q hb)
  | error h =>
    exact herr h hb fun hp => SPath.resolve_noPanic σ b (hp ▸ hb)

/-- **A memory path captured**: `T memory mv = nmp; s'`. -/
theorem Premise.Sound.captureMVSim {R : RefTy} {x : Var} {b : MPath C Γ (.ref R)}
    {s' : Stmt C (.mem R :: Γ) (.mem R :: Γ)} {s : Stmt C Γ Γ}
    (hok : ∀ id, (do (← b.mval σ).asRef) = .ok id →
      (s'.run (σ.push (t := .mem R) (some id))).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, (do (← b.mval σ).asRef) = .error h → h ≠ .panic →
      Res.Sim (.error h) (s.run σ)) :
    Premise.Sound m s (.captureMV x b s') σ := by
  refine Premise.Sound.captureMVK
    (fun id => (s'.run (σ.push (t := .mem R) (some id))).map (State.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases hb : (do (← b.mval σ).asRef : Res Nat) with
  | ok id => exact Res.Sim.of_eq (hok id hb)
  | error h =>
    exact herr h hb fun hp => MPath.ref_noPanic σ b (hp ▸ hb)

/-- The captured local, read on top, is the value captured. -/
theorem Simple.eval_here {p : PrimTy} (v : Value) :
    (Simple.local (C := C) (p := p) (Γ := .val p :: Γ) .here).eval (σ.push (t := .val p) v) = pure v := rfl

theorem SPath.resolve_here {R : RefTy} (q : Name × List Seg) :
    (SPath.alias (C := C) (Γ := .alias R :: Γ) (R := R) .here).resolve (σ.push (t := .alias R) (some q)) =
      pure q := rfl

theorem MPath.mval_here {R : RefTy} (id : Nat) (hm : (Ty.ref R).mapFree = true) :
    (MPath.var (C := C) (Γ := .mem R :: Γ) .here hm).mval (σ.push (t := .mem R) (some id)) =
      pure (.ref id) := rfl

end Capture

/-! ## Each statement's run, by name -/

section RunEq

variable {Γ : Ctx} (σ : State C Γ)

theorem Stmt.run_assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    Stmt.run σ (.assign l r) = Run.assign l r σ := rfl
theorem Stmt.run_rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    Stmt.run σ (.rebind i r) = Run.rebind i r σ := rfl
theorem Stmt.run_assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p) :
    Stmt.run σ (.assignLocal i v) = Run.assignLocal i v σ := rfl
theorem Stmt.run_declLocal (p : PrimTy) (x : Var) (init : Option (Val C Γ p)) :
    Stmt.run σ (.declLocal p x init) = Run.declLocal p init σ := rfl
theorem Stmt.run_declStorage (R : RefTy) (x : Var) (init : Option (ARhs C Γ R)) :
    Stmt.run σ (.declStorage R x init) = Run.declStorage R init σ := rfl
theorem Stmt.run_opAssign {p : PrimTy} (op : BinOp) (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (l : OpLoc C Γ p) (r : Val C Γ p) :
    Stmt.run σ (.opAssign op hop hp l r) = Run.opAssign op l r σ := rfl
theorem Stmt.run_incDec {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (l : OpLoc C Γ p) :
    Stmt.run σ (.incDec op hp l) = Run.incDec op l σ := rfl
theorem Stmt.run_push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) : Stmt.run σ (.push b v hd) = Run.push b v σ := rfl
theorem Stmt.run_pop {E : Ty} (b : SPath C Γ (.array E)) : Stmt.run σ (.pop b) = Run.pop b σ := rfl
theorem Stmt.run_transfer (r a : Val C Γ .uint) : Stmt.run σ (.transfer r a) = Run.transfer r a σ :=
  rfl
theorem Stmt.run_send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    Stmt.run σ (.send pv r a) = Run.send pv r a σ := rfl
theorem Stmt.run_declMem (R : RefTy) (x : Var) (init : Option (MRhs C Γ R))
    (hd : (init.isSome || (Ty.ref R).defaultOkS) = true) (hm : (Ty.ref R).mapFree = true) :
    Stmt.run σ (.declMem R x init hd hm) = Run.declMem R init σ := rfl
theorem Stmt.run_rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    Stmt.run σ (.rebindMem i r) = Run.rebindMem i r σ := rfl
theorem Stmt.run_assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Stmt.run σ (.assignFromMem l p) = Run.assignFromMem l p σ := rfl
theorem Stmt.run_assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    Stmt.run σ (.assignMem l r) = Run.assignMem l r σ := rfl
theorem Stmt.run_delete {T : Ty} (l : Loc C Γ T) : Stmt.run σ (.delete l) = Run.delete l σ := rfl
theorem Stmt.run_deleteMem {T : Ty} (p : MPath C Γ T) (hd : T.defaultOkS = true) :
    Stmt.run σ (.deleteMem p hd) = Run.deleteMem p σ := rfl
theorem Stmt.run_assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) : Stmt.run σ (.assignNew l n h) = Run.assignNew l n σ := rfl
theorem Stmt.run_require (c : Val C Γ .bool) :
    Stmt.run σ (.require c) = (do guardOk (← c.eval σ) σ) := rfl
theorem Stmt.run_assert (c : Val C Γ .bool) :
    Stmt.run σ (.assert c) = (do assertOk (← c.eval σ) σ) := rfl

end RunEq

/-! ## Holes: the read, then what the hole does with it -/

section Holes

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- What a storage hole does with the path it is given: `v = find(…)`,
`lsv = p`, `loc = copy(…)`. -/
def SHole.cont : {T : Ty} → SHole C Γ T → State C Γ → Name × List Seg → Res (State C Γ)
  | _, .local i, σ, q => do pure (σ.setLocal i (← (← σ.glob.findStorage q.1 q.2).asValue))
  | _, .rebind i, σ, q => pure (σ.setLocal i (some q))
  | _, .copy l _, σ, q => do
    let sv ← σ.glob.findStorage q.1 q.2
    let (root, segs) ← l.resolve σ
    σ.withGlob <$> σ.glob.writeStorage root segs sv

theorem SHole.fill_run {T : Ty} (lhs : SHole C Γ T) (l : Loc C Γ T) :
    (lhs.fill (.loc l)).run σ = l.resolve σ >>= lhs.cont σ := by
  cases lhs with
  | «local» i =>
    show Run.assignLocal i (.read l) σ = _
    simp only [Run.assignLocal, Val.eval, bind_assoc]; rfl
  | rebind i =>
    show Run.rebind i (.path (.loc l)) σ = _
    simp only [Run.rebind, ARhs.eval, SPath.resolve, bind_assoc, pure_bind]; rfl
  | copy l' h =>
    show Run.assign l' (.copy (.loc l) h) σ = _
    simp only [Run.assign, Src.value, SPath.resolve, bind_assoc]; rfl

theorem SHole.cont_up {t : LTy} (w : t.Denote C) {T : Ty} (lhs : SHole C Γ T) (q : Name × List Seg) :
    lhs.up.cont (σ.push w) q = pushed w (lhs.cont σ q) := by
  cases lhs with
  | «local» i => push_run [SHole.up, SHole.cont]
  | rebind i => rfl
  | copy l h => push_run [SHole.up, SHole.cont, Loc.resolve_up]

theorem SHole.fill_push {t : LTy} (w : t.Denote C) {T : Ty} (lhs : SHole C Γ T)
    (l' : Loc C (t :: Γ) T) (l : Loc C Γ T) (hl : l'.resolve (σ.push w) = l.resolve σ) :
    (lhs.up.fill (.loc l')).run (σ.push w) = pushed w ((lhs.fill (.loc l)).run σ) := by
  rw [SHole.fill_run, SHole.fill_run, hl, pushed_bind]
  congr 1; funext q; exact SHole.cont_up σ w lhs q

/-- What a memory hole does with the slot it is given: `v = read(…)`,
`mv = i`, `mloc = i`. -/
def MHole.cont : {T : Ty} → MHole C Γ T → State C Γ → MVal → Res (State C Γ)
  | _, .local i, σ, mv => do pure (σ.setLocal i (← mv.asValue))
  | _, .rebind i, σ, mv => do pure (σ.setLocal i (← mv.asRef))
  | _, .write l, σ, mv => do l.write σ (.ref (← mv.asRef))

theorem MHole.fill_run {T : Ty} (lhs : MHole C Γ T) (l : MLoc C Γ T) :
    (lhs.fill l).run σ = l.read σ >>= lhs.cont σ := by
  cases lhs with
  | «local» i =>
    show Run.assignLocal i (.readMem l) σ = _
    simp only [Run.assignLocal, Val.eval, bind_assoc]; rfl
  | rebind i =>
    show Run.rebindMem i (.alias (.loc l)) σ = _
    simp only [Run.rebindMem, MRhs.eval, MPath.mval, bind_assoc, pure_bind]; rfl
  | write l' =>
    show Run.assignMem l' (.ref (.loc l)) σ = _
    simp only [Run.assignMem, MSrc.mval, MPath.mval, bind_assoc, pure_bind]; rfl

theorem MHole.cont_up {t : LTy} (w : t.Denote C) {T : Ty} (lhs : MHole C Γ T) (mv : MVal) :
    lhs.up.cont (σ.push w) mv = pushed w (lhs.cont σ mv) := by
  cases lhs with
  | «local» i => push_run [MHole.up, MHole.cont]
  | rebind i => push_run [MHole.up, MHole.cont]
  | write l => push_run [MHole.up, MHole.cont, (MLoc.Agree.of_up σ w l).write]

theorem MHole.fill_push {t : LTy} (w : t.Denote C) {T : Ty} (lhs : MHole C Γ T)
    (l' : MLoc C (t :: Γ) T) (l : MLoc C Γ T) (hl : l'.read (σ.push w) = l.read σ) :
    (lhs.up.fill l').run (σ.push w) = pushed w ((lhs.fill l).run σ) := by
  rw [MHole.fill_run, MHole.fill_run, hl, pushed_bind]
  congr 1; funext q; exact MHole.cont_up σ w lhs q

/-- What a value hole does with the value it is given: `v = e`,
`loc = e`, `mloc = e`. -/
def VHole.cont {p : PrimTy} : VHole C Γ p → State C Γ → Value → Res (State C Γ)
  | .local i, σ, v => pure (σ.setLocal i v)
  | .store l, σ, v => do
    let (root, segs) ← l.resolve σ
    σ.withGlob <$> σ.glob.writeStorage root segs v.toSVal
  | .mem l, σ, v => l.write σ v.toMVal

theorem VHole.fill_run {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) :
    (lhs.fill e).run σ = e.eval σ >>= lhs.cont σ := by
  cases lhs with
  | «local» i => rfl
  | store l =>
    show Run.assign l (.val e) σ = _
    simp only [Run.assign, Src.value, bind_assoc, pure_bind]; rfl
  | mem l =>
    show Run.assignMem l (.val e) σ = _
    simp only [Run.assignMem, MSrc.mval, bind_assoc, pure_bind]; rfl

theorem VHole.cont_up {t : LTy} (w : t.Denote C) {p : PrimTy} (lhs : VHole C Γ p) (v : Value) :
    lhs.up.cont (σ.push w) v = pushed w (lhs.cont σ v) := by
  cases lhs with
  | «local» i => rfl
  | store l => push_run [VHole.up, VHole.cont, Loc.resolve_up]
  | mem l => push_run [VHole.up, VHole.cont, (MLoc.Agree.of_up σ w l).write]

theorem VHole.fill_push {t : LTy} (w : t.Denote C) {p : PrimTy} (lhs : VHole C Γ p)
    (e' : Val C (t :: Γ) p) (e : Val C Γ p) (he : e'.eval (σ.push w) = e.eval σ) :
    (lhs.up.fill e').run (σ.push w) = pushed w ((lhs.fill e).run σ) := by
  rw [VHole.fill_run, VHole.fill_run, he, pushed_bind]
  congr 1; funext q; exact VHole.cont_up σ w lhs q

end Holes

/-! ## A read unfolded into a hole -/

section ReadSteps

variable {Γ : Ctx} {m : Modality} (σ : State C Γ)

/-- `storageFieldRead_unfold_rightFst`: the receiver bound first. -/
theorem SHole.sound_fieldCapture {T : Ty} (lhs : SHole C Γ T) {s : Name} (b : SPath C Γ (.struct s))
    (f : Name) (hf : C.fieldType s f = some T) (x : Var) :
    Premise.Sound m (lhs.fill (.loc (.field b f hf)))
      (.captureSP x b (lhs.up.fill (.loc (.field (.alias .here) f hf)))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [SHole.fill_push σ (t := .alias (.struct s)) (some q) lhs _ (.field b f hf), pushed_drop]
    simp only [Loc.resolve, SPath.resolve_here, hq, pure_bind, Res.bind_ok]
  · rw [SHole.fill_run]
    simp only [Loc.resolve, hh]
    exact Res.Sim.refl _

/-- `storageIndexRead_unfold_rightFst`: the receiver bound first. -/
theorem SHole.sound_indexRecvCapture {T : Ty} (lhs : SHole C Γ T) {R : RefTy} {kp : PrimTy}
    (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.Sound m (lhs.fill (.loc (.index it b i)))
      (.captureSP x b (lhs.up.fill (.loc (.index it (.alias .here) i.up)))) σ := by
  refine Premise.Sound.captureSPSim σ (fun q hq => ?_) (fun h hh _ => ?_)
  · rw [SHole.fill_push σ (t := .alias R) (some q) lhs _ (.index it b i), pushed_drop]
    simp only [Loc.resolve, SPath.resolve_here, hq, Val.eval_up, State.glob_push, pure_bind,
      Res.bind_ok]
  · rw [SHole.fill_run]
    simp only [Loc.resolve, hh]
    exact Res.Sim.refl _

/-- `storageIndexRead_unfold_rightSndIndex`: the index captured, the receiver
(simple) read after it. -/
theorem SHole.sound_indexCapture {T : Ty} (lhs : SHole C Γ T) {R : RefTy} {kp : PrimTy}
    (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) (i : Val C Γ kp) (x : Var) :
    Premise.Sound m (lhs.fill (.loc (.index it b i)))
      (.capture kp x i (lhs.up.fill (.loc (.index it b.up (.simple (.local .here)))))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · rw [SHole.fill_push σ (t := .val kp) v lhs _ (.index it b i), pushed_drop]
    simp only [Loc.resolve, SPath.resolve_up, Val.eval, Simple.eval_here, hv, State.glob_push]
    rfl
  · rw [SHole.fill_run]
    simp only [Loc.resolve, bind_assoc]
    refine Res.Sim.err_bind (SPath.resolve_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact Res.Sim.refl _

/-- **A storage read unfolded into a hole** (`SHole.readStep`) is sound
when the hole's own rules are. -/
theorem SHole.readStep_sound (k : Nat) {T : Ty} (lhs : SHole C Γ T)
    {root : (r : Name) → C.rootType r = some T → Option (Premise C Γ Γ)}
    {field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Option (Premise C Γ Γ)}
    {index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) → Simple C Γ kp →
      Option (Premise C Γ Γ)}
    (l : Loc C Γ T)
    (hroot : ∀ r h p, l = .root r h → root r h = some p →
      Premise.Sound m (lhs.fill (.loc (.root r h))) p σ)
    (hfield : ∀ {s : Name} (b : SPath C Γ (.struct s)) f hf p, l = .field b f hf →
      field b f hf = some p → Premise.Sound m (lhs.fill (.loc (.field b f hf))) p σ)
    (hindex : ∀ {R : RefTy} {kp : PrimTy} (it : IndexTy R kp T) b (ie : Simple C Γ kp) p,
      l = .index it b (.simple ie) → index it b ie = some p →
      Premise.Sound m (lhs.fill (.loc (.index it b (.simple ie)))) p σ)
    (p : Premise C Γ Γ) (hp : lhs.readStep k root field index l = some p) :
    Premise.Sound m (lhs.fill (.loc l)) p σ := by
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
theorem MHole.sound_fieldCapture {T : Ty} (lhs : MHole C Γ T) {s : Name} (b : MPath C Γ (.struct s))
    (hm : (Ty.ref (.struct s)).mapFree = true) (f : Name) (hf : C.fieldType s f = some T) (x : Var) :
    Premise.Sound m (lhs.fill (.field b f hf))
      (.captureMV x b (lhs.up.fill (.field (.var .here hm) f hf))) σ := by
  refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun h hh _ => ?_)
  · obtain ⟨mv, hmv, hr⟩ := Res.bind_eq_ok.1 hid
    rw [MHole.fill_push σ (t := .mem (.struct s)) id lhs _ (.field b f hf), pushed_drop]
    simp only [MLoc.read, MPath.mval_here, hmv, hr, State.glob_push, Res.bind_ok, pure_bind]
    rfl
  · rw [MHole.fill_run]
    simp only [MLoc.read]
    rw [← bind_assoc, hh]
    exact Res.Sim.refl _

/-- `memoryIndexRead_unfold_rightFst`: the receiver bound first. -/
theorem MHole.sound_indexRecvCapture {T : Ty} (lhs : MHole C Γ T) {R : RefTy} (a : ArrTy R T)
    (b : MPath C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true) (i : Val C Γ .uint) (x : Var) :
    Premise.Sound m (lhs.fill (.index a b i))
      (.captureMV x b (lhs.up.fill (.index a (.var .here hm) i.up))) σ := by
  refine Premise.Sound.captureMVSim σ (fun id hid => ?_) (fun h hh _ => ?_)
  · obtain ⟨mv, hmv, hr⟩ := Res.bind_eq_ok.1 hid
    rw [MHole.fill_push σ (t := .mem R) id lhs _ (.index a b i), pushed_drop]
    simp only [MLoc.read, MPath.mval_here, hmv, hr, Val.eval_up, State.glob_push, Res.bind_ok,
      pure_bind]
    rfl
  · rw [MHole.fill_run]
    simp only [MLoc.read]
    rw [← bind_assoc, hh]
    exact Res.Sim.refl _

/-- `memoryIndexRead_unfold_rightSndIndex`: the index captured. -/
theorem MHole.sound_indexCapture {T : Ty} (lhs : MHole C Γ T) {R : RefTy} (a : ArrTy R T)
    (b : MPath C Γ (.ref R)) (i : Val C Γ .uint) (x : Var) :
    Premise.Sound m (lhs.fill (.index a b i))
      (.capture .uint x i (lhs.up.fill (.index a b.up (.simple (.local .here))))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh hp => ?_)
  · rw [MHole.fill_push σ (t := .val .uint) v lhs _ (.index a b i), pushed_drop]
    simp only [MLoc.read, MPath.mval_up, Val.eval, Simple.eval_here, hv, State.glob_push]
    rfl
  · rw [MHole.fill_run]
    simp only [MLoc.read, bind_assoc]
    rw [← bind_assoc]
    refine Res.Sim.err_bind (MPath.ref_noPanic σ b) hp fun _ _ => ?_
    simp only [hh]
    exact Res.Sim.refl _

/-- **A memory read unfolded into a hole** (`MHole.readStep`) is sound when
the hole's own rules are. -/
theorem MHole.readStep_sound (k : Nat) {T : Ty} (lhs : MHole C Γ T)
    {field : {s : Name} → (mv : Idx Γ (.mem (.struct s))) → (Ty.ref (.struct s)).mapFree = true →
      (f : Name) → C.fieldType s f = some T → Option (Premise C Γ Γ)}
    {index : {R : RefTy} → ArrTy R T → (mv : Idx Γ (.mem R)) → (Ty.ref R).mapFree = true →
      Simple C Γ .uint → Option (Premise C Γ Γ)}
    (hfield : ∀ {s : Name} (mv : Idx Γ (.mem (.struct s))) hmv f hf p, field mv hmv f hf = some p →
      Premise.Sound m (lhs.fill (.field (.var mv hmv) f hf)) p σ)
    (hindex : ∀ {R : RefTy} (a : ArrTy R T) (mv : Idx Γ (.mem R)) hmv (ie : Simple C Γ .uint) p,
      index a mv hmv ie = some p → Premise.Sound m (lhs.fill (.index a (.var mv hmv) (.simple ie))) p σ)
    (l : MLoc C Γ T) (p : Premise C Γ Γ) (hp : lhs.readStep k field index l = some p) :
    Premise.Sound m (lhs.fill l) p σ := by
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

theorem Prog.run_single {Γ' : Ctx} (s : Stmt C Γ Γ') : Prog.run σ (.cons s .nil) = s.run σ := by
  rw [Prog.run_cons]; cases s.run σ <;> rfl

theorem Res.map_drop_refl (r : Res (State C Γ)) : r.map (State.drop .refl) = r := by
  cases r <;> rfl

theorem VHole.fill_ext {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) : (lhs.fill e).ext = .refl := by
  cases lhs <;> rfl

/-- `…ValueRhsCapture`, `…UnfoldSource`: `T se = nse; lhs = se;`. -/
theorem VHole.sound_capture {p : PrimTy} (lhs : VHole C Γ p) (e : Val C Γ p) (x : Var) :
    Premise.Sound m (lhs.fill e) (.capture p x e (lhs.up.fill (.simple (.local .here)))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · rw [VHole.fill_push σ (t := .val p) v lhs _ e (by rw [hv]; rfl), pushed_drop]
  · rw [VHole.fill_run, hh]
    exact Res.Sim.refl _

/-- `ternaryCaptureCond`: the condition captured first. -/
theorem VHole.sound_ternaryCapture {p : PrimTy} (lhs : VHole C Γ p) (c : Val C Γ .bool)
    (a b : Val C Γ p) (x : Var) :
    Premise.Sound m (lhs.fill (.ternary c a b))
      (.capture .bool x c (lhs.up.fill (.ternary (.simple (.local .here)) a.up b.up))) σ := by
  refine Premise.Sound.captureSim σ (fun v hv => ?_) (fun h hh _ => ?_)
  · refine (congrArg _ (VHole.fill_push σ (t := .val .bool) v lhs _ (.ternary c a b) ?_)).trans
      (pushed_drop _ _)
    simp only [Val.eval, Simple.eval_here, Val.eval_up, hv, pure_bind, Res.bind_ok]
  · rw [VHole.fill_run]
    simp only [Val.eval, hh]
    exact Res.Sim.refl _

/-- `ternaryToIf`: `lhs = se ? a : b;` is `if (se) lhs = a; else lhs = b;`. -/
theorem VHole.sound_ternaryToIf {p : PrimTy} (lhs : VHole C Γ p) (se : Simple C Γ .bool)
    (a b : Val C Γ p) :
    Premise.Sound m (lhs.fill (.ternary (.simple se) a b))
      (.unfold (.cons (.ite (.simple se) (.cons (lhs.fill a) .nil) (.cons (lhs.fill b) .nil)) .nil)
        .refl) σ := by
  refine Premise.Sound.unfold ?_
  obtain ⟨v, hv⟩ := Simple.eval_ok σ se
  rw [Res.map_drop_refl, Prog.run_single, Stmt.run_ite]
  show Run.ite _ ((lhs.fill a).ext.trans .refl) (Prog.run · (.cons (lhs.fill a) .nil))
    ((lhs.fill b).ext.trans .refl) (Prog.run · (.cons (lhs.fill b) .nil)) σ = _
  simp only [Run.ite, Val.eval, hv, Res.bind_ok, VHole.fill_ext, Ext.trans_refl, Prog.run_single,
    Res.map_drop_refl, VHole.fill_run]
  cases v with
  | bool bv => cases bv <;> rfl
  | int => rfl

/-- **A conditional into a hole** (`ternaryStep`). -/
theorem ternaryStep_sound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p) (c : Val C Γ .bool)
    (a b : Val C Γ p) (q : Premise C Γ Γ) (hq : ternaryStep k lhs c a b = some q) :
    Premise.Sound m (lhs.fill (.ternary c a b)) q σ := by
  cases c with
  | simple se => cases hq; exact VHole.sound_ternaryToIf σ lhs se a b
  | _ => cases hq; exact VHole.sound_ternaryCapture σ lhs _ a b _

/-- **A value into a hole** (`VHole.step`): sound when the hole's own rule is. -/
theorem VHole.step_sound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p)
    {simple : Simple C Γ p → Option (Premise C Γ Γ)}
    (hsimple : ∀ se q, simple se = some q → Premise.Sound m (lhs.fill (.simple se)) q σ)
    (e : Val C Γ p) (q : Premise C Γ Γ) (hq : lhs.step k simple e = some q) :
    Premise.Sound m (lhs.fill e) q σ := by
  cases e with
  | simple se => exact hsimple se q hq
  | ternary c a b => exact ternaryStep_sound σ k lhs c a b q hq
  | _ => cases hq; exact VHole.sound_capture σ lhs _ _

/-- **A value into a hole, lowered first** (`VHole.lower`). -/
theorem VHole.lower_sound (k : Nat) {p : PrimTy} (lhs : VHole C Γ p) {other : Option (Premise C Γ Γ)}
    (e : Val C Γ p) (hother : ∀ q, other = some q → Premise.Sound m (lhs.fill e) q σ)
    (q : Premise C Γ Γ) (hq : lhs.lower k other e = some q) :
    Premise.Sound m (lhs.fill e) q σ := by
  cases e with
  | ternary c a b => exact ternaryStep_sound σ k lhs c a b q hq
  | _ => exact hother q hq

end ReadSteps

end Solidity.Core
