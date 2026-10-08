import Solidity.Calculus.Core.TProvesSound
import Solidity.Typing.StraightRun

/-!
# Premise shapes over the typed state

`Calculus/Core/Logic.lean`'s "Premise shapes" over the typed state
(`tholds`, `Calculus/Core/TLogic.lean`): what each kind of premise needs of
the statement it replaces, as an equation between typed runs, for
`Premise.TSound` (`Calculus/Core/TProvesSound.lean`).  The runs are read at
the states they end in (`Stmt.trunSt`, `Prog.trunSt`, `Frames.trunSt`), so
that a block and the statement it replaces compare as M3's do; the heap
extension an outcome carries (`Out.ext`) plays no part in what a formula
says.

An update rule needs that its update, applied to the erasure, ends in the
erasure of the state the typed run ends in, and halts where the run halts
under the diamond (`Premise.tsound_update`).
-/

namespace Solidity.Core

open Solidity (Modality)

variable {C : Contract}

/-! ## Runs read at the states they end in -/

section Runs

variable {Γ Γ' Γ₁ Γ₀ : Ctx}

/-- The state a statement's typed run ends in. -/
def Stmt.trunSt (σ : TState C Γ) (s : Stmt C Γ Γ') : TRes (TState C Γ') := (s.trun σ).map (·.st)

/-- The state a sequence's typed run ends in. -/
def Prog.trunSt (σ : TState C Γ) (P : Prog C Γ Γ') : TRes (TState C Γ') :=
  (Prog.trun σ P).map (·.st)

/-- The state the frames' typed run ends in. -/
def Frames.trunSt (σ : TState C Γ) (κ : Frames C Γ Γ₀) : TRes (TState C Γ₀) :=
  (Frames.trun σ κ).map (·.st)

theorem Prog.trunFrames_eq (σ : TState C Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    Prog.trunFrames σ P κ = (Prog.trunSt σ P).bind (Frames.trunSt · κ) := by
  simp only [Prog.trunFrames, Prog.trunSt, Frames.trunSt, bind, Except.bind, Except.map]
  cases Prog.trun σ P with
  | error => rfl
  | ok o => cases Frames.trun o.st κ <;> rfl

theorem Prog.trunSt_nil (σ : TState C Γ) : Prog.trunSt σ (.nil : Prog C Γ Γ) = .ok σ := rfl

theorem Prog.trunSt_cons (σ : TState C Γ) (s : Stmt C Γ Γ') (P : Prog C Γ' Γ₁) :
    Prog.trunSt σ (.cons s P) = (Stmt.trunSt σ s).bind (Prog.trunSt · P) := by
  simp only [Prog.trunSt, Stmt.trunSt]
  cases h : s.trun σ with
  | error e =>
    show (TRun.seq s.trunR P.trunR σ).map _ = _
    simp only [TRun.seq, Stmt.trun] at h ⊢
    rw [h]
    rfl
  | ok o =>
    rw [Prog.trun_cons_ok h]
    show ((Prog.trun o.st P).map _).map _ = (Prog.trun o.st P).map _
    cases Prog.trun o.st P <;> rfl

theorem Frames.trunSt_nil (σ : TState C Γ) : Frames.trunSt σ (.nil : Frames C Γ Γ) = .ok σ := rfl

theorem Frames.trunSt_seq (σ : TState C Γ) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    Frames.trunSt σ (.seq ω κ) = (Prog.trunSt σ ω).bind (Frames.trunSt · κ) := by
  simp only [Frames.trunSt, Frames.trun, TRun.seq, Prog.trunSt, Except.map, Except.bind]
  cases Prog.trun σ ω with
  | error => rfl
  | ok o =>
    dsimp only
    cases Frames.trun o.st κ <;> rfl

theorem Frames.trunSt_pop {Γ'' : Ctx} (σ : TState C Γ'') (b : BlockKind) (h : Ext Γ Γ'')
    (κ : Frames C Γ Γ₀) : Frames.trunSt σ (.pop b h κ) = Frames.trunSt (σ.drop h) κ := rfl

theorem Frames.trunSt_drop {Γ'' : Ctx} (σ : TState C Γ'') (h : Thin Γ Γ'') (κ : Frames C Γ Γ₀) :
    Frames.trunSt σ (.drop h κ) = Frames.trunSt (σ.thin h) κ := rfl

/-- What a modality says, through the states its runs end in. -/
theorem tholds_modal_iff {m : Modality} (σ : TState C Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) :
    tholds σ (.modal m P κ φ) ↔
      m.afterRunTR (tholds · φ) ((Prog.trunSt σ P).bind (Frames.trunSt · κ)) := by
  show m.afterRunTR _ (Prog.trunFrames σ P κ) ↔ _
  rw [Prog.trunFrames_eq]

/-- The rest of the program, gone into the frames when it is empty, gives
the modality over it. -/
theorem tholds_modalK {m : Modality} (σ : TState C Γ) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (h : tholds σ (Fml.modalK m ω κ φ)) : tholds σ (.modal m ω κ φ) := by
  cases ω with
  | nil => exact tholds_exit m κ φ σ h
  | cons s ω => exact h

/-- The outcome of `s` and then the rest, through the frames. -/
theorem trunSt_cons_frames (s : Stmt C Γ Γ') (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀)
    (σ : TState C Γ) :
    (Prog.trunSt σ (.cons s ω)).bind (Frames.trunSt · κ) =
      (Stmt.trunSt σ s).bind fun τ => (Prog.trunSt τ ω).bind (Frames.trunSt · κ) := by
  rw [Prog.trunSt_cons]
  cases Stmt.trunSt σ s <;> rfl

end Runs

/-! ## Premise shapes -/

section Shapes

variable {Γ Γ' Γ₁ Γ₀ : Ctx} {m : Modality}

/-- **An update**: `{U} ⟨ ω κ ⟩ φ` gives `⟨ s; ω κ ⟩ φ` when `U`, applied to
the erasure, ends in the erasure of the state `s` ends in, and `s` halts
only where `U` does under the diamond, never in a panic. -/
theorem Premise.tsound_update {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : TState C Γ)
    (hs : ∀ τ, Stmt.trunSt σ s = .ok τ → U.apply σ.erase = .ok τ.erase)
    (hh : ∀ e, Stmt.trunSt σ s = .error e →
      e ≠ .panic ∧ (m = .diamond → ∃ e', U.apply σ.erase = .error e')) :
    Premise.TSound m s (.update U) σ := by
  intro _ _ ω κ φ h
  have h' : m.afterC (fun τ => ∀ σ' : TState C Γ', σ'.erase = τ → tholds σ' (Fml.modalK m ω κ φ))
      (U.apply σ.erase) := h
  rw [tholds_modal_iff, trunSt_cons_frames]
  cases hτ : Stmt.trunSt σ s with
  | ok τ =>
    rw [hs τ hτ] at h'
    exact (tholds_modal_iff τ ω κ φ).1 (tholds_modalK τ ω κ φ (h' τ rfl))
  | error e =>
    obtain ⟨hp, hd⟩ := hh e hτ
    refine ⟨?_, fun he => hp (Except.error.inj he)⟩
    cases m with
    | box => trivial
    | diamond =>
      obtain ⟨e', he'⟩ := hd rfl
      rw [he'] at h'
      exact h'

/-- **A block**: `⟨ P (pop) ω κ ⟩ φ` gives `⟨ s; ω κ ⟩ φ` when `P`, its
fresh locals popped, runs as `s`. -/
theorem Premise.tsound_unfold {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''} {s : Stmt C Γ Γ'}
    (σ : TState C Γ) (hs : (Prog.trunSt σ P).map (TState.drop h) = Stmt.trunSt σ s) :
    Premise.TSound m s (.unfold P h) σ := by
  intro _ _ ω κ φ hp
  have h' := (tholds_modal_iff σ P (.pop .capture h (.seq ω κ)) φ).1 hp
  rw [tholds_modal_iff, trunSt_cons_frames, ← hs]
  revert h'
  cases Prog.trunSt σ P with
  | error => exact id
  | ok τ =>
    intro h'
    change m.afterRunTR _ (Frames.trunSt τ (.pop .capture h (.seq ω κ))) at h'
    rw [Frames.trunSt_pop, Frames.trunSt_seq] at h'
    exact h'

/-- **A block dropping a frame from under what it keeps**
(`Premise.inline`). -/
theorem Premise.tsound_inline {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Thin Γ' Γ''} {s : Stmt C Γ Γ'}
    (σ : TState C Γ) (hs : (Prog.trunSt σ P).map (TState.thin h) = Stmt.trunSt σ s) :
    Premise.TSound m s (.inline P h) σ := by
  intro _ _ ω κ φ hp
  have h' := (tholds_modal_iff σ P (.drop h (.seq ω κ)) φ).1 hp
  rw [tholds_modal_iff, trunSt_cons_frames, ← hs]
  revert h'
  cases Prog.trunSt σ P with
  | error => exact id
  | ok τ =>
    intro h'
    change m.afterRunTR _ (Frames.trunSt τ (.drop h (.seq ω κ))) at h'
    rw [Frames.trunSt_drop, Frames.trunSt_seq] at h'
    exact h'

/-- **A hidden binder**: `∀ v. ⟨ P ω κ ⟩ φ` from `σ` with `v` pushed gives
`⟨ s; ω κ ⟩ φ` when, for some `v` of its type, `P` runs from there as `s`
from `σ`. -/
theorem Premise.tsound_bind {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    (σ : TState C Γ) (hs : ∃ v : t.TDenote C σ.H, Prog.trunSt (σ.push v) P = Stmt.trunSt σ s) :
    Premise.TSound m s (.bind x t P) σ := by
  intro _ _ ω κ φ h
  obtain ⟨v, hv⟩ := hs
  have h' := (tholds_modal_iff (σ.push v) P (.seq ω κ) φ).1 (Modality.forallB_all h v)
  rw [tholds_modal_iff, trunSt_cons_frames, ← hv]
  revert h'
  cases Prog.trunSt (σ.push v) P with
  | error => exact id
  | ok τ =>
    intro h'
    change m.afterRunTR _ (Frames.trunSt τ (.seq ω κ)) at h'
    rw [Frames.trunSt_seq] at h'
    exact h'

/-- **A hidden binder, every value**: a statement that runs as `P` from
`σ` with any value of its type pushed.  Under the diamond the premise gives
the value; under the box the type must have one. -/
theorem Premise.tsound_bind_all {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    (σ : TState C Γ) (hs : ∀ v : t.TDenote C σ.H, Prog.trunSt (σ.push v) P = Stmt.trunSt σ s)
    (hbox : m = .box → Nonempty (t.TDenote C σ.H)) :
    Premise.TSound m s (.bind x t P) σ := by
  intro _ _ ω κ φ h
  have hne : Nonempty (t.TDenote C σ.H) := by
    cases m
    · exact h.1
    · exact hbox rfl
  obtain ⟨v⟩ := hne
  exact Premise.tsound_bind σ ⟨v, hs v⟩ ω κ φ h

/-- A block's run, its locals popped, then the rest and the frames: the
frame a branch ends with (`pop b P.ext`). -/
theorem trunSt_block_frames {Δ : Ctx} (b : BlockKind) (P : Prog C Γ Δ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (σ : TState C Γ) :
    (Prog.trunSt σ P).bind (Frames.trunSt · (.pop b P.ext (.seq ω κ))) =
      ((Prog.trunSt σ P).map (TState.drop P.ext)).bind fun τ =>
        (Prog.trunSt τ ω).bind (Frames.trunSt · κ) := by
  cases Prog.trunSt σ P with
  | error => rfl
  | ok τ =>
    show Frames.trunSt τ (.pop b P.ext (.seq ω κ)) = _
    rw [Frames.trunSt_pop, Frames.trunSt_seq]
    rfl

/-- **Two goals**: `(c → ⟨ P } ω κ ⟩ φ) ∧ (c' → ⟨ Q } ω κ ⟩ φ)` gives
`⟨ s; ω κ ⟩ φ` when one of `c`, `c'` holds, and the branch it guards, its
locals popped, runs as `s`. -/
theorem Premise.tsound_split {b : BlockKind} {Δ₁ Δ₂ : Ctx} {c c' : Fml C Γ} {P : Prog C Γ Δ₁}
    {Q : Prog C Γ Δ₂} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (hc : tholds σ c → (Prog.trunSt σ P).map (TState.drop P.ext) = Stmt.trunSt σ s)
    (hc' : tholds σ c' → (Prog.trunSt σ Q).map (TState.drop Q.ext) = Stmt.trunSt σ s)
    (hcov : tholds σ c ∨ tholds σ c') : Premise.TSound m s (.split b c c' P Q) σ := by
  rintro _ _ ω κ φ ⟨h₁, h₂⟩
  rw [tholds_modal_iff, trunSt_cons_frames]
  rcases hcov with h | h
  · have := (tholds_modal_iff σ P _ φ).1 (tholds_modalK σ P _ φ (h₁ h))
    rw [trunSt_block_frames, hc h] at this
    exact this
  · have := (tholds_modal_iff σ Q _ φ).1 (tholds_modalK σ Q _ φ (h₂ h))
    rw [trunSt_block_frames, hc' h] at this
    exact this

/-- **A check**: `(c → ⟨ ω κ ⟩ φ) ∧ c` gives `⟨ s; ω κ ⟩ φ` when, `c`
holding, `s` does nothing. -/
theorem Premise.tsound_check {c : Fml C Γ} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (hc : tholds σ c → Stmt.trunSt σ s = .ok σ) : Premise.TSound m s (.check c) σ := by
  rintro _ _ ω κ φ ⟨h₁, h₂⟩
  rw [tholds_modal_iff, trunSt_cons_frames, hc h₂]
  exact (tholds_modal_iff σ ω κ φ).1 (tholds_modalK σ ω κ φ (h₁ h₂))

/-- **A closed goal**: `true` gives a box over a statement that halts, not in
a panic. -/
theorem Premise.tsound_done {s : Stmt C Γ Γ'} (σ : TState C Γ) (b : Bool)
    (hs : b = true → m = .box ∧ ∃ e, Stmt.trunSt σ s = .error e ∧ e ≠ .panic) :
    Premise.TSound m s (.done b) σ := by
  intro _ _ ω κ φ h
  cases b with
  | false => exact absurd trivial h
  | true =>
    obtain ⟨rfl, e, he, hp⟩ := hs rfl
    rw [tholds_modal_iff, trunSt_cons_frames, he]
    exact ⟨trivial, fun h => hp (Except.error.inj h)⟩

end Shapes

/-! ## The per-arm statement

Each arm of `Stmt.step` proves, for its statement, that the premise it
gives is sound in a typed state `σ` (`Premise.TSound`): its theorem is named
as M3's with `tsound` for `sound` (`localStep_sound` → `localStep_tsound`)
and takes `σ` first, then the arm's arguments, the premise `q` and
`hq : …Step k … = some q`.  An arm that is sound only under a condition (a
push at the bound under the diamond) takes it as a hypothesis. -/

/-- **The rule of `s` is sound over the typed state**, in every typed state
(`Stmt.StepSound`, over `TState`). -/
def Stmt.TStepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ σ : TState C Γ, ∀ p, s.step k m = some p → Premise.TSound m s p σ

/-! ## Runs that halt alike

A rule that captures a part evaluates it first, where the statement may read
another part first; the two runs then halt alike but maybe not with the same
halt, which a modality does not tell apart but for a panic
(`Modality.afterRunTR`): `Res.Sim`, over the typed run. -/

section Sim

variable {α β : Type}

/-- The same state, or two halts that are both panics or both not. -/
def TRes.Sim : TRes α → TRes α → Prop
  | .ok a, .ok b => a = b
  | .error e, .error e' => (e = .panic ↔ e' = .panic)
  | _, _ => False

theorem TRes.Sim.refl (r : TRes α) : TRes.Sim r r := by
  cases r <;> simp only [TRes.Sim, iff_self]

theorem TRes.Sim.of_eq {r r' : TRes α} (h : r = r') : TRes.Sim r r' := h ▸ TRes.Sim.refl r

theorem TRes.Sim.bind {r r' : TRes α} (h : TRes.Sim r r') (f : α → TRes β) :
    TRes.Sim (r.bind f) (r'.bind f) := by
  match r, r', h with
  | .ok a, .ok b, h => cases h; exact TRes.Sim.refl _
  | .error _, .error _, h => exact h

theorem TRes.Sim.afterRunTR {m : Modality} {p : α → Prop} {r r' : TRes α} (h : TRes.Sim r r') :
    m.afterRunTR p r → m.afterRunTR p r' := by
  match r, r', h with
  | .ok a, .ok b, h => cases h; exact id
  | .error e, .error e', h =>
    rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun he => h₂ (by rw [h.2 (Except.error.inj he)])⟩

/-- An error, its halt not a panic, against a run that does not panic and
does not end. -/
theorem TRes.Sim.err {r : TRes α} {e : THalt} (he : e ≠ .panic) (hr : r ≠ .error .panic)
    (hok : ∀ a, r ≠ .ok a) : TRes.Sim (.error e) r := by
  match r with
  | .ok a => exact absurd rfl (hok a)
  | .error e' => exact ⟨fun h => absurd h he, fun h => absurd (h ▸ rfl) hr⟩

end Sim

/-! ## The premise shapes, up to the halt -/

section ShapesSim

variable {Γ Γ' : Ctx} {m : Modality}

/-- **A block** is sound when it runs as the statement up to the halt, its
fresh locals popped. -/
theorem Premise.tsound_unfoldSim {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''}
    {s : Stmt C Γ Γ'} (σ : TState C Γ)
    (hs : TRes.Sim ((Prog.trunSt σ P).map (TState.drop h)) (Stmt.trunSt σ s)) :
    Premise.TSound m s (.unfold P h) σ := by
  intro _ _ ω κ φ hp
  have h' := (tholds_modal_iff σ P (.pop .capture h (.seq ω κ)) φ).1 hp
  rw [tholds_modal_iff, trunSt_cons_frames]
  have e : (Prog.trunSt σ P).bind (Frames.trunSt · (.pop .capture h (.seq ω κ))) =
      ((Prog.trunSt σ P).map (TState.drop h)).bind fun τ =>
        (Prog.trunSt τ ω).bind (Frames.trunSt · κ) := by
    cases Prog.trunSt σ P with
    | error => rfl
    | ok τ =>
      show Frames.trunSt τ (.pop .capture h (.seq ω κ)) = _
      rw [Frames.trunSt_pop, Frames.trunSt_seq]
      rfl
  rw [e] at h'
  exact (hs.bind _).afterRunTR h'

/-- A one-statement sequence runs as its statement. -/
theorem Prog.trunSt_single {Γ' : Ctx} (σ : TState C Γ) (s : Stmt C Γ Γ') :
    Prog.trunSt σ (.cons s .nil) = Stmt.trunSt σ s := by
  rw [Prog.trunSt_cons]
  cases Stmt.trunSt σ s <;> rfl

/-- `T se = nse;`, typed: the value read, then pushed. -/
theorem Stmt.trunSt_declLocal (σ : TState C Γ) (p : PrimTy) (x : Var) (e : Val C Γ p) :
    Stmt.trunSt σ (.declLocal p x (some e)) = (e.evalT σ).map fun v => σ.push (t := .val p) v := by
  show (TRun.declLocal p (some e) σ).map _ = _
  simp only [TRun.declLocal]
  cases e.evalT σ <;> rfl

/-- `T storage sp = nsp;`, typed: the path resolved, then pushed. -/
theorem Stmt.trunSt_declStorage (σ : TState C Γ) (R : RefTy) (x : Var) (b : SPath C Γ (.ref R)) :
    Stmt.trunSt σ (.declStorage R x (some (.path b))) =
      (b.resolveT σ).map fun q => σ.push (t := .alias R) (some q) := by
  show (TRun.declStorage R (some (.path b)) σ).map _ = _
  simp only [TRun.declStorage, ARhs.evalT]
  cases b.resolveT σ <;> rfl

/-- `T memory mv = nmp;`, typed: the object read, then pushed. -/
theorem Stmt.trunSt_declMem (σ : TState C Γ) (R : RefTy) (x : Var) (b : MPath C Γ (.ref R)) :
    Stmt.trunSt σ (.declMem R x (some (.alias b)) rfl b.mapFree) =
      (b.mvalT σ).map fun r => σ.push (t := .mem R) r := by
  show (TRun.declMem R (some (.alias b)) b.mapFree σ).map _ = _
  simp only [TRun.declMem, MRhs.evalT]
  cases b.mvalT σ <;> rfl

/-- A declaration, then a statement on top of it, its local popped: the
declaration's outcome, then the statement's. -/
theorem trunSt_declThen {t : LTy} (σ : TState C Γ) (d : Stmt C Γ (t :: Γ))
    (s' : Stmt C (t :: Γ) (t :: Γ)) :
    (Prog.trunSt σ (.cons d (.cons s' .nil))).map (TState.drop (.push .refl)) =
      (Stmt.trunSt σ d).bind fun τ => (Stmt.trunSt τ s').map (TState.drop (.push .refl)) := by
  rw [Prog.trunSt_cons]
  cases Stmt.trunSt σ d with
  | error => rfl
  | ok τ =>
    show (Prog.trunSt τ (.cons s' .nil)).map _ = _
    rw [Prog.trunSt_single]
    rfl

/-- **A value captured**, by what the statement does with the value (`G`):
the statement on top of the local runs as `G`, and the statement is the value
read, then `G`, up to the halt. -/
theorem Premise.tsound_captureK {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (G : p.Denote → TRes (TState C Γ))
    (hs' : ∀ v, (Stmt.trunSt (σ.push (t := .val p) v) s').map (TState.drop (.push .refl)) = G v)
    (hs : TRes.Sim ((e.evalT σ).bind G) (Stmt.trunSt σ s)) :
    Premise.TSound m s (.capture p x e s') σ := by
  refine Premise.tsound_unfoldSim σ ?_
  rw [trunSt_declThen, Stmt.trunSt_declLocal]
  have : ((e.evalT σ).map fun v => σ.push (t := .val p) v).bind
      (fun τ => (Stmt.trunSt τ s').map (TState.drop (.push .refl))) = (e.evalT σ).bind G := by
    cases e.evalT σ with
    | error => rfl
    | ok v => exact hs' v
  rw [this]; exact hs

/-- **A storage path captured**, by what the statement does with the
reference. -/
theorem Premise.tsound_captureSPK {R : RefTy} {x : Var} {b : SPath C Γ (.ref R)}
    {s' : Stmt C (.alias R :: Γ) (.alias R :: Γ)} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (G : SRef C (.ref R) → TRes (TState C Γ))
    (hs' : ∀ q, (Stmt.trunSt (σ.push (t := .alias R) (some q)) s').map
      (TState.drop (.push .refl)) = G q)
    (hs : TRes.Sim ((b.resolveT σ).bind G) (Stmt.trunSt σ s)) :
    Premise.TSound m s (.captureSP x b s') σ := by
  refine Premise.tsound_unfoldSim σ ?_
  rw [trunSt_declThen, Stmt.trunSt_declStorage]
  have : ((b.resolveT σ).map fun q => σ.push (t := .alias R) (some q)).bind
      (fun τ => (Stmt.trunSt τ s').map (TState.drop (.push .refl))) = (b.resolveT σ).bind G := by
    cases b.resolveT σ with
    | error => rfl
    | ok q => exact hs' q
  rw [this]; exact hs

/-- **A memory path captured**, by what the statement does with the
object. -/
theorem Premise.tsound_captureMVK {R : RefTy} {x : Var} {b : MPath C Γ (.ref R)}
    {s' : Stmt C (.mem R :: Γ) (.mem R :: Γ)} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (G : MVal σ.H (.ref R) → TRes (TState C Γ))
    (hs' : ∀ r, (Stmt.trunSt (σ.push (t := .mem R) r) s').map
      (TState.drop (.push .refl)) = G r)
    (hs : TRes.Sim ((b.mvalT σ).bind G) (Stmt.trunSt σ s)) :
    Premise.TSound m s (.captureMV x b s') σ := by
  refine Premise.tsound_unfoldSim σ ?_
  rw [trunSt_declThen, Stmt.trunSt_declMem]
  have : ((b.mvalT σ).map fun r => σ.push (t := .mem R) r).bind
      (fun τ => (Stmt.trunSt τ s').map (TState.drop (.push .refl))) = (b.mvalT σ).bind G := by
    cases b.mvalT σ with
    | error => rfl
    | ok r => exact hs' r
  rw [this]; exact hs

end ShapesSim

/-! ## An update, through the bridge

An update rule's update is a term of `Update.lean`, read on the erasure, so
what it needs of the typed run (`Premise.tsound_update`) follows from M3's
equation with the scoped run (`Premise.Sound.update`'s `U.apply σ = s.run σ`)
by the bridge (`Stmt.trun_erase`), where the typed run does not diverge: a
typed `diverge` agrees with any untyped outcome, so under the diamond the
arm asks that it does not happen (a push at the bound). -/

section Bridge

variable {Γ Γ' : Ctx} {m : Modality}

/-- **An update, through the bridge**: an update that ends as the scoped run
of the statement does from the erasure is sound over the typed state, on the
bridge (`Stmt.bridgeOk`), where the typed run does not diverge under the
diamond. -/
theorem Premise.tsound_update_run {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : TState C Γ)
    (hb : s.bridgeOk = true) (hs : U.apply σ.erase = s.run σ.erase)
    (hd : m = .diamond → (s.trun σ).NoDiv) : Premise.TSound m s (.update U) σ := by
  have ha := Stmt.trun_erase σ s hb
  apply Premise.tsound_update σ
  · intro τ hτ
    simp only [Stmt.trunSt] at hτ
    cases ht : s.trun σ with
    | error => rw [ht] at hτ; cases hτ
    | ok o =>
      rw [ht] at hτ ha
      obtain rfl : o.st = τ := Except.ok.inj hτ
      exact hs.trans ha
  · intro e he
    simp only [Stmt.trunSt] at he
    cases ht : s.trun σ with
    | ok o => rw [ht] at he; cases he
    | error e' =>
      rw [ht] at he ha
      obtain rfl : e' = e := Except.error.inj he
      cases e' with
      | revert => exact ⟨nofun, fun _ => ⟨_, hs.trans ha⟩⟩
      | panic => exact absurd (hs.trans ha) (Upd.apply_noPanic σ.erase U)
      | diverge => exact ⟨nofun, fun hm => absurd ht (hd hm)⟩

end Bridge

end Solidity.Core
