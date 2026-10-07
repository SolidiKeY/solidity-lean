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
      (s'.run (σ.push (t := .mem R) id)).map (State.drop (.push .refl)) = s.run σ)
    (herr : ∀ h, (do (← b.mval σ).asRef) = .error h → h ≠ .panic →
      Res.Sim (.error h) (s.run σ)) :
    Premise.Sound m s (.captureMV x b s') σ := by
  refine Premise.Sound.captureMVK
    (fun id => (s'.run (σ.push (t := .mem R) id)).map (State.drop (.push .refl)))
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
    (MPath.var (C := C) (Γ := .mem R :: Γ) .here hm).mval (σ.push (t := .mem R) id) = pure (.ref id) := rfl

end Capture

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

end Solidity.Core
