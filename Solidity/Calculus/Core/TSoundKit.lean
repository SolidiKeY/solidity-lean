import Solidity.Calculus.Core.TProvesSound

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

end Solidity.Core
