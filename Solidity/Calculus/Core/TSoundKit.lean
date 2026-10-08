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
only where `U` does under the diamond (but when it is exhausted, which both
modalities accept), never in a panic. -/
theorem Premise.tsound_update {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : TState C Γ)
    (hs : ∀ τ, Stmt.trunSt σ s = .ok τ → U.apply σ.erase = .ok τ.erase)
    (hh : ∀ e, Stmt.trunSt σ s = .error e →
      e ≠ .panic ∧ (m = .diamond → e ≠ .exhausted → ∃ e', U.apply σ.erase = .error e')) :
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
      show e = .exhausted
      by_cases hx : e = .exhausted
      · exact hx
      · obtain ⟨e', he'⟩ := hd rfl hx
        rw [he'] at h'
        exact h'.elim

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
`hq : …Step k … = some q`.  An arm that is sound only under a condition
takes it as a hypothesis, and `Stmt.TArmOk` collects them
(`Calculus/Core/TSoundStep.lean`'s module docstring says why it holds).
Decisions 15 and 16 took two away (a push at the bound is exhausted; no
struct repeats a member name); one is left:

* `T memory mv = r;` at an allocating `r` has, under the box, a reference
  of its type in the heap (decision 12); an alias `T memory mv = mp;` needs
  none. -/

/-- **What an arm asks of the statement** for its rule to be sound over the
typed state in `σ` under `m`; `True` for every other statement. -/
def Stmt.TArmOk (m : Modality) : {Γ Γ' : Ctx} → TState C Γ → Stmt C Γ Γ' → Prop
  | _, _, _, .declMem _ _ (some (.alias _)) _ _ => True
  | _, _, σ, .declMem R _ (some _) _ _ => m = .box → Nonempty ((LTy.mem R).TDenote C σ.H)
  | _, _, _, _ => True

/-- **The rule of `s` is sound over the typed state** (`Stmt.StepSound`,
over `TState`), in every typed state where `s` meets its arm's condition. -/
def Stmt.TStepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ σ : TState C Γ, ∀ p, s.step k m = some p → s.TArmOk m σ → Premise.TSound m s p σ

/-! ## Evaluators revert -/

section Revert

variable {Γ : Ctx} (σ : TState C Γ)

/-- A typed result that neither panics, diverges nor is exhausted halts
with a revert. -/
theorem TRes.eq_revert {α : Type} {t : TRes α} (hp : t ≠ .error .panic) (he : t.Ends)
    {h : THalt} (ht : t = .error h) : h = .revert := by
  subst ht
  cases h with
  | revert => rfl
  | panic => exact absurd rfl hp
  | diverge => exact absurd rfl he.1
  | exhausted => exact absurd rfl he.2

theorem Val.evalT_revert {p : PrimTy} (v : Val C Γ p) {h : THalt} (hv : v.evalT σ = .error h) :
    h = .revert :=
  TRes.eq_revert (Val.evalT_noPanic σ v) (Val.evalT_ends σ v) hv

theorem SPath.resolveT_revert {T : Ty} (b : SPath C Γ T) {h : THalt}
    (hb : b.resolveT σ = .error h) : h = .revert :=
  TRes.eq_revert (SPath.resolveT_noPanic σ b) (SPath.resolveT_ends σ b) hb

theorem MPath.mvalT_revert {T : Ty} (b : MPath C Γ T) {h : THalt}
    (hb : b.mvalT σ = .error h) : h = .revert :=
  TRes.eq_revert (MPath.mvalT_noPanic σ b) (MPath.mvalT_ends σ b) hb

/-- **A push never diverges**: onto `2^256 - 1` elements it is exhausted
(`Storage.full`, decision 15), which both modalities accept. -/
theorem TRun.push_nd {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    (TRun.push b v σ).NoDiv := by
  unfold TRun.push
  refine TRes.NoDiv.bind (SPath.resolveT_ends σ b).1 fun ref => ?_
  cases v with
  | none =>
    dsimp only
    split
    · exact fun h => nomatch h
    · exact TRes.NoDiv.bind (TRes.NoDiv.ofOpt _) fun _ => TRes.NoDiv.ok _
  | some r =>
    refine TRes.NoDiv.bind (Src.valueT_ends σ r).1 fun _ => ?_
    dsimp only
    split
    · exact fun h => nomatch h
    · exact TRes.NoDiv.bind (TRes.NoDiv.ofOpt _) fun _ => TRes.NoDiv.ok _

/-- An alias's right-hand side never diverges: a push onto `2^256 - 1`
elements is exhausted. -/
theorem ARhs.evalT_nd {R : RefTy} : (r : ARhs C Γ R) → (r.evalT σ).NoDiv
  | .path p => TRes.NoDiv.bind (SPath.resolveT_ends σ p).1 fun _ => TRes.NoDiv.ok _
  | .push b _ => by
    simp only [ARhs.evalT]
    refine TRes.NoDiv.bind (SPath.resolveT_ends σ b).1 fun ref => ?_
    split
    · exact fun h => nomatch h
    · exact TRes.NoDiv.bind (TRes.NoDiv.ofOpt _) fun _ => TRes.NoDiv.ok _

end Revert

/-! ## Runs that halt alike

A rule that captures a part evaluates it first, where the statement may read
another part first; the two runs then halt alike but maybe not with the same
halt, which a modality does not tell apart but for a panic
(`Modality.afterRunTR`): `Res.Sim`, over the typed run. -/

section Sim

variable {α β : Type}

/-- The same state, or two halts that are both panics or both not, the
second exhausted where the first is (`exhausted` is the one halt the
diamond accepts). -/
def TRes.Sim : TRes α → TRes α → Prop
  | .ok a, .ok b => a = b
  | .error e, .error e' => (e = .panic ↔ e' = .panic) ∧ (e = .exhausted → e' = .exhausted)
  | _, _ => False

theorem TRes.Sim.refl (r : TRes α) : TRes.Sim r r := by
  cases r
  · exact ⟨Iff.rfl, id⟩
  · rfl

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
    refine ⟨?_, fun he => h₂ (by rw [h.1.2 (Except.error.inj he)])⟩
    cases m with
    | box => trivial
    | diamond => exact h.2 h₁

/-- A revert against a run that does not panic and does not end. -/
theorem TRes.Sim.err {r : TRes α} {e : THalt} (he : e = .revert) (hr : r ≠ .error .panic)
    (hok : ∀ a, r ≠ .ok a) : TRes.Sim (.error e) r := by
  subst he
  match r with
  | .ok a => exact absurd rfl (hok a)
  | .error e' => exact ⟨⟨nofun, fun h => absurd (h ▸ rfl) hr⟩, nofun⟩

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
arm shows that it does not happen (no update arm's statement loops; a push
at the bound is exhausted, `TRun.push_nd`, which agrees with anything too
and which both modalities accept). -/

section Bridge

variable {Γ Γ' : Ctx} {m : Modality}

/-- **An update, through the bridge, up to the halt**: an update that ends
as the scoped run of the statement does from the erasure, up to the halt
(`Res.Sim`), is sound over the typed state, where the typed run does not
diverge under the diamond. -/
theorem Premise.tsound_updateSim_run {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : TState C Γ)
    (hs : Res.Sim (U.apply σ.erase) (s.run σ.erase))
    (hd : m = .diamond → (s.trun σ).NoDiv) : Premise.TSound m s (.update U) σ := by
  have ha := Stmt.trun_erase σ s
  have hU := Upd.apply_noPanic σ.erase U
  apply Premise.tsound_update σ
  · intro τ hτ
    simp only [Stmt.trunSt] at hτ
    cases ht : s.trun σ with
    | error => rw [ht] at hτ; cases hτ
    | ok o =>
      rw [ht] at hτ ha
      obtain rfl : o.st = τ := Except.ok.inj hτ
      have ha' : s.run σ.erase = .ok o.st.erase := ha
      rw [ha'] at hs
      revert hs
      cases U.apply σ.erase with
      | ok a => intro hs; exact congrArg Except.ok hs
      | error => intro hs; exact hs.elim
  · intro e he
    simp only [Stmt.trunSt] at he
    cases ht : s.trun σ with
    | ok o => rw [ht] at he; cases he
    | error e' =>
      rw [ht] at he ha
      obtain rfl : e' = e := Except.error.inj he
      cases e' with
      | revert =>
        have ha' : s.run σ.erase = .error .revert := ha
        rw [ha'] at hs
        revert hs
        cases U.apply σ.erase with
        | ok => intro hs; exact hs.elim
        | error e'' => exact fun _ => ⟨nofun, fun _ _ => ⟨e'', rfl⟩⟩
      | panic =>
        have ha' : s.run σ.erase = .error .panic := ha
        rw [ha'] at hs
        revert hs hU
        cases U.apply σ.erase with
        | ok => intro hs _; exact hs.elim
        | error e'' => exact fun hs hU => absurd (congrArg Except.error (hs.2 rfl)) hU
      | diverge => exact ⟨nofun, fun hm _ => absurd ht (hd hm)⟩
      | exhausted => exact ⟨nofun, fun _ hx => absurd rfl hx⟩

/-- **An update, through the bridge**: an update that ends as the scoped run
of the statement does from the erasure (M3's `Premise.Sound.update`'s
equation). -/
theorem Premise.tsound_update_run {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : TState C Γ)
    (hs : U.apply σ.erase = s.run σ.erase)
    (hd : m = .diamond → (s.trun σ).NoDiv) : Premise.TSound m s (.update U) σ :=
  Premise.tsound_updateSim_run σ (hs ▸ Res.Sim.refl _) hd

theorem tholds_conj {σ : TState C Γ} :
    (l : List (Fml C Γ)) → (tholds σ (Fml.conj l) ↔ ∀ ψ ∈ l, tholds σ ψ)
  | [] => by simp only [Fml.conj, tholds, List.not_mem_nil, false_implies, implies_true]
  | [φ] => by simp only [Fml.conj, List.mem_singleton, forall_eq]
  | φ :: ψ :: l => by
    show tholds σ φ ∧ tholds σ (Fml.conj (ψ :: l)) ↔ _
    rw [tholds_conj (ψ :: l)]
    simp only [List.mem_cons, forall_eq_or_imp]

/-- **Labelled goals, through the bridge**: the formulas `fs`, then the rest
after each update of `us`, give `⟨ s; ω κ ⟩ φ` when, the formulas holding,
the statement runs as one of the updates up to the halt from the erasure. -/
theorem Premise.tsound_cases_run {fs : List (Fml C Γ)} {us : List (Upd C Γ Γ)} {s : Stmt C Γ Γ}
    (σ : TState C Γ)
    (h : (∀ f ∈ fs, tholds σ f) → ∃ U ∈ us, Res.Sim (U.apply σ.erase) (s.run σ.erase))
    (hd : m = .diamond → (s.trun σ).NoDiv) : Premise.TSound m s (.cases fs us) σ := by
  intro Γ₁ Γ₀ ω κ φ hp
  have hp' := (tholds_conj _).1 hp
  obtain ⟨U, hU, hs⟩ := h fun f hf => hp' f (List.mem_append_left _ hf)
  exact Premise.tsound_updateSim_run σ hs hd ω κ φ
    (hp' _ (List.mem_append_right _ (List.mem_map_of_mem hU)))

end Bridge

/-! ## A shifted part reads as it did, typed

`Calculus/Core/Logic.lean`'s "A shifted part reads as it did" over the
typed state: a rule reads the parts of its `\find` under its fresh local
(`Val.up` and its kin, `Calculus/Core/Shift.lean`), and the state with a
local pushed is the state lifted along `up` (`TState.push_lift`), so each
is `Semantics/Core/TypedRunWk.lean`'s `*_wk` at `up`. -/

section Shift

variable {Γ : Ctx} {t : LTy} (σ : TState C Γ) (w : t.TDenote C σ.H)

theorem TState.push_lift : σ.push w = σ.lift Core.up (w, σ.env) := rfl

theorem Simple.evalT_up {p : PrimTy} (s : Simple C Γ p) :
    (s.up (t := t)).evalT (σ.push w) = s.evalT σ := by
  rw [Simple.up_eq]; exact Simple.evalT_wk Core.up σ (w, σ.env) s

theorem SPath.resolveT_up {T : Ty} (b : SPath C Γ T) :
    (b.up (t := t)).resolveT (σ.push w) = b.resolveT σ := by
  rw [SPath.up_eq]; exact SPath.resolveT_wk Core.up σ (w, σ.env) b

theorem Loc.resolveT_up {T : Ty} (l : Loc C Γ T) :
    (l.up (t := t)).resolveT (σ.push w) = l.resolveT σ := by
  rw [Loc.up_eq]; exact Loc.resolveT_wk Core.up σ (w, σ.env) l

theorem MPath.mvalT_up {T : Ty} (b : MPath C Γ T) :
    (b.up (t := t)).mvalT (σ.push w) = b.mvalT σ := by
  rw [MPath.up_eq]; exact MPath.mvalT_wk Core.up σ (w, σ.env) b

theorem MLoc.addrT_up {T : Ty} (l : MLoc C Γ T) :
    (l.up (t := t)).addrT (σ.push w) = l.addrT σ := by
  rw [MLoc.up_eq]; exact MLoc.addrT_wk Core.up σ (w, σ.env) l

theorem Val.evalT_up {p : PrimTy} (v : Val C Γ p) :
    (v.up (t := t)).evalT (σ.push w) = v.evalT σ := by
  rw [Val.up_eq]; exact Val.evalT_wk Core.up σ (w, σ.env) v

theorem Src.valueT_up {T : Ty} (r : Src C Γ T) :
    (r.up (t := t)).valueT (σ.push w) = r.valueT σ := by
  rw [Src.up_eq]; exact Src.valueT_wk Core.up σ (w, σ.env) r

theorem MSrc.mvalT_up {T : Ty} (r : MSrc C Γ T) :
    (r.up (t := t)).mvalT (σ.push w) = r.mvalT σ := by
  rw [MSrc.up_eq]; exact MSrc.mvalT_wk Core.up σ (w, σ.env) r

theorem ARhs.evalT_up {R : RefTy} (r : ARhs C Γ R) :
    (r.up (t := t)).evalT (σ.push w) = r.evalT σ := by
  rw [ARhs.up_eq]; exact ARhs.evalT_wk Core.up σ (w, σ.env) r

theorem TState.get_push_here : (TEnv.get .here (σ.push w).env : t.TDenote C σ.H) = w := rfl

theorem TState.get_push_there {u : LTy} (i : Idx Γ u) :
    (TEnv.get i.there (σ.push w).env : u.TDenote C σ.H) = TEnv.get i σ.env := rfl

theorem TState.push_setLocal {u : LTy} (i : Idx Γ u) (x : u.TDenote C σ.H) :
    (σ.push w).setLocal i.there x = (σ.setLocal i x).push w := rfl

theorem TState.drop_push : (σ.push w).drop (.push .refl) = σ := rfl

/-- An outcome lifted along `up`, its top local popped: the outcome. -/
theorem liftedT_up_drop (r : TRes (Out C σ.H Γ)) :
    ((liftedT Core.up (w, σ.env) r).map (·.st)).map (TState.drop (.push .refl)) = r.map (·.st) := by
  cases r <;> rfl

end Shift

/-! ## Captures, up to the halt

`Calculus/Core/SoundCapture.lean`'s capture shapes over the typed run: the
statement on top of the captured part runs as the statement, and where the
part halts the statement halts alike (`TRes.Sim`; no expression panics,
`Val.evalT_noPanic`). -/

section CaptureSim

variable {Γ : Ctx} {m : Modality}

/-- A run that reads a part that does not panic first halts alike to `h`
when what follows does. -/
theorem TRes.Sim.err_bind {α β : Type} {X : TRes α} (hX : X.NoPanic) {h : THalt}
    (hh : h = .revert) {f : α → TRes β} (hf : ∀ a, X = .ok a → TRes.Sim (.error h) (f a)) :
    TRes.Sim (.error h) (X.bind f) := by
  subst hh
  cases hx : X with
  | ok a => exact hf a hx
  | error h' =>
    rw [hx] at hX
    exact ⟨⟨nofun, fun e => absurd (congrArg Except.error e) hX⟩, nofun⟩

theorem TRes.Sim.err_refl {α : Type} {h : THalt} {r : TRes α} (hr : r = .error h) :
    TRes.Sim (.error h) r := hr ▸ TRes.Sim.refl _

/-- **A value captured**: `T se = nse; s'` gives `s`, `s'` running as `s`
with the value on top, and `s` halting alike where `nse` halts. -/
theorem Premise.tsound_captureSim {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (hok : ∀ v, e.evalT σ = .ok v →
      (Stmt.trunSt (σ.push (t := .val p) v) s').map (TState.drop (.push .refl)) = Stmt.trunSt σ s)
    (herr : ∀ h, e.evalT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.trunSt σ s)) :
    Premise.TSound m s (.capture p x e s') σ := by
  refine Premise.tsound_captureK σ
    (fun v => (Stmt.trunSt (σ.push (t := .val p) v) s').map (TState.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases he : e.evalT σ with
  | ok v => exact TRes.Sim.of_eq (hok v he)
  | error h => exact herr h he (Val.evalT_revert σ e he)

/-- **A storage path captured**: `T storage sp = nsp; s'`. -/
theorem Premise.tsound_captureSPSim {R : RefTy} {x : Var} {b : SPath C Γ (.ref R)}
    {s' : Stmt C (.alias R :: Γ) (.alias R :: Γ)} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (hok : ∀ q, b.resolveT σ = .ok q →
      (Stmt.trunSt (σ.push (t := .alias R) (some q)) s').map (TState.drop (.push .refl)) =
        Stmt.trunSt σ s)
    (herr : ∀ h, b.resolveT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.trunSt σ s)) :
    Premise.TSound m s (.captureSP x b s') σ := by
  refine Premise.tsound_captureSPK σ
    (fun q => (Stmt.trunSt (σ.push (t := .alias R) (some q)) s').map (TState.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases hb : b.resolveT σ with
  | ok q => exact TRes.Sim.of_eq (hok q hb)
  | error h => exact herr h hb (SPath.resolveT_revert σ b hb)

/-- **A memory path captured**: `T memory mv = nmp; s'`. -/
theorem Premise.tsound_captureMVSim {R : RefTy} {x : Var} {b : MPath C Γ (.ref R)}
    {s' : Stmt C (.mem R :: Γ) (.mem R :: Γ)} {s : Stmt C Γ Γ} (σ : TState C Γ)
    (hok : ∀ r, b.mvalT σ = .ok r →
      (Stmt.trunSt (σ.push (t := .mem R) r) s').map (TState.drop (.push .refl)) = Stmt.trunSt σ s)
    (herr : ∀ h, b.mvalT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.trunSt σ s)) :
    Premise.TSound m s (.captureMV x b s') σ := by
  refine Premise.tsound_captureMVK σ
    (fun r => (Stmt.trunSt (σ.push (t := .mem R) r) s').map (TState.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases hb : b.mvalT σ with
  | ok r => exact TRes.Sim.of_eq (hok r hb)
  | error h => exact herr h hb (MPath.mvalT_revert σ b hb)

/-- When the box's statement halts, not in a panic, any premise gives it. -/
theorem Premise.tsound_of_halt {Γ' : Ctx} {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'}
    (σ : TState C Γ) {e : THalt} (he : Stmt.trunSt σ s = .error e) (hp : e ≠ .panic) :
    Premise.TSound .box s p σ := by
  intro _ _ ω κ φ _
  rw [tholds_modal_iff, trunSt_cons_frames, he]
  exact ⟨trivial, fun h => hp (Except.error.inj h)⟩

end CaptureSim

/-! ## A scope end that pops nothing -/

theorem Ext.length_le {Γ : Ctx} : {Δ : Ctx} → Ext Γ Δ → Γ.length ≤ Δ.length
  | _, .refl => Nat.le_refl _
  | _, .push h => Nat.le_succ_of_le (Ext.length_le h)

theorem Ext.eq_refl_of {Γ : Ctx} : {Δ : Ctx} → (e : Ext Γ Δ) → (h : Δ = Γ) → h ▸ e = .refl
  | _, .refl, _ => rfl
  | _, .push e, h => by
    have := Ext.length_le e
    have := congrArg List.length h
    simp only [List.length_cons] at this
    omega

/-- A scope end from a context to itself pops nothing. -/
theorem Ext.self_eq_refl {Γ : Ctx} (e : Ext Γ Γ) : e = .refl := Ext.eq_refl_of e rfl

theorem TState.drop_self {Γ : Ctx} (e : Ext Γ Γ) (σ : TState C Γ) : σ.drop e = σ := by
  rw [Ext.self_eq_refl e]; rfl

theorem TRes.map_drop_self {Γ : Ctx} (e : Ext Γ Γ) (r : TRes (TState C Γ)) :
    r.map (TState.drop e) = r := by
  rw [Ext.self_eq_refl e]; cases r <;> rfl

end Solidity.Core
