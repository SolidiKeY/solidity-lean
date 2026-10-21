import Solidity.Calculus.Logic
import Solidity.Calculus.PremiseSound
import Solidity.Semantics.Ends
import Solidity.Calculus.LowerRun
import Solidity.Semantics.Callback
import Solidity.Semantics.NoPanic

/-!
# Soundness of a rule: the premise shapes, and the kit

What each kind of premise needs of the statement it replaces, as an equation
between typed runs (`Premise.Runs`, the arms' statement), which gives
`Premise.Sound` (`Calculus/ProvesSound.lean`, `holds`,
`Calculus/Logic.lean`) and the reading with callbacks
(`Calculus/CallbackSound.lean`).  The runs are read at the states they
end in (`Stmt.runSt`, `Prog.runSt`, `Frames.runSt`), so that a block and
the statement it replaces compare as states; a run only grows the heap
typing (`Out.ext`), which an update's reading asks.

An update rule needs that its update computes the global part and the
locals of the state the typed run ends in (`Upd.applyV`, typed), and halts
where the run halts under the diamond (`Premise.sound_update`); an arm
states that the statement's typed step agrees with what the update computes
(`TRes.AgreesO`, `Premise.sound_update_typed`), from the lowered
expressions' agreements (`Calculus/LowerRun.lean`).  Also here: typed runs
alike up to the halt (`TRes.Sim`).
-/

namespace Solidity
open Solidity (Modality Srt)

variable {C : Contract}

open Solidity (Modality)

/-! ## Runs read at the states they end in -/

section Runs

variable {Γ Γ' Γ₁ Γ₀ : Ctx}

/-- The state a statement's typed run ends in. -/
def Stmt.runSt (σ : State C Γ) (s : Stmt C Γ Γ') : TRes (State C Γ') := (s.run σ).map (·.st)

/-- The state a sequence's typed run ends in. -/
def Prog.runSt (σ : State C Γ) (P : Prog C Γ Γ') : TRes (State C Γ') :=
  (Prog.run σ P).map (·.st)

/-- The state the frames' typed run ends in. -/
def Frames.runSt (σ : State C Γ) (κ : Frames C Γ Γ₀) : TRes (State C Γ₀) :=
  (Frames.run σ κ).map (·.st)

theorem Prog.runFrames_eq (σ : State C Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    Prog.runFrames σ P κ = (Prog.runSt σ P).bind (Frames.runSt · κ) := by
  simp only [Prog.runFrames, Prog.runSt, Frames.runSt, bind, Except.bind, Except.map]
  cases Prog.run σ P with
  | error => rfl
  | ok o => cases Frames.run o.st κ <;> rfl

theorem Prog.runSt_nil (σ : State C Γ) : Prog.runSt σ (.nil : Prog C Γ Γ) = .ok σ := rfl

theorem Prog.runSt_cons (σ : State C Γ) (s : Stmt C Γ Γ') (P : Prog C Γ' Γ₁) :
    Prog.runSt σ (.cons s P) = (Stmt.runSt σ s).bind (Prog.runSt · P) := by
  simp only [Prog.runSt, Stmt.runSt]
  cases h : s.run σ with
  | error e =>
    show (TRun.seq s.runR P.runR σ).map _ = _
    simp only [TRun.seq, Stmt.run] at h ⊢
    rw [h]
    rfl
  | ok o =>
    rw [Prog.run_cons_ok h]
    show ((Prog.run o.st P).map _).map _ = (Prog.run o.st P).map _
    cases Prog.run o.st P <;> rfl

theorem Frames.runSt_nil (σ : State C Γ) : Frames.runSt σ (.nil : Frames C Γ Γ) = .ok σ := rfl

theorem Frames.runSt_seq (σ : State C Γ) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) :
    Frames.runSt σ (.seq ω κ) = (Prog.runSt σ ω).bind (Frames.runSt · κ) := by
  simp only [Frames.runSt, Frames.run, TRun.seq, Prog.runSt, Except.map, Except.bind]
  cases Prog.run σ ω with
  | error => rfl
  | ok o =>
    dsimp only
    cases Frames.run o.st κ <;> rfl

theorem Frames.runSt_pop {Γ'' : Ctx} (σ : State C Γ'') (b : BlockKind) (h : Ext Γ Γ'')
    (κ : Frames C Γ Γ₀) : Frames.runSt σ (.pop b h κ) = Frames.runSt (σ.drop h) κ := rfl

theorem Frames.runSt_drop {Γ'' : Ctx} (σ : State C Γ'') (h : Thin Γ Γ'') (κ : Frames C Γ Γ₀) :
    Frames.runSt σ (.drop h κ) = Frames.runSt (σ.thin h) κ := rfl

/-- What a modality says, through the states its runs end in. -/
theorem holds_modal_iff {m : Modality} (σ : State C Γ) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) :
    holds σ (.modal m P κ φ) ↔
      m.afterRunTR (holds · φ) ((Prog.runSt σ P).bind (Frames.runSt · κ)) := by
  show m.afterRunTR _ (Prog.runFrames σ P κ) ↔ _
  rw [Prog.runFrames_eq]

/-- The rest of the program, gone into the frames when it is empty, gives
the modality over it. -/
theorem holds_modalK {m : Modality} (σ : State C Γ) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (φ : Fml C Γ₀) (h : holds σ (Fml.modalK m ω κ φ)) : holds σ (.modal m ω κ φ) := by
  cases ω with
  | nil => exact holds_exit m κ φ σ h
  | cons s ω => exact h

/-- The outcome of `s` and then the rest, through the frames. -/
theorem runSt_cons_frames (s : Stmt C Γ Γ') (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀)
    (σ : State C Γ) :
    (Prog.runSt σ (.cons s ω)).bind (Frames.runSt · κ) =
      (Stmt.runSt σ s).bind fun τ => (Prog.runSt τ ω).bind (Frames.runSt · κ) := by
  rw [Prog.runSt_cons]
  cases Stmt.runSt σ s <;> rfl

/-- An outcome's states, each mapped, read through the states. -/
theorem TRes.map_st {H : HTy} {Δ Γ' : Ctx} (X : TRes (Out C H Δ)) (f : Out C H Δ → Out C H Γ')
    (g : State C Δ → State C Γ') (hfg : ∀ o, (f o).st = g o.st) :
    (X.map f).map (·.st) = (X.map (·.st)).map g := by
  cases X with
  | error => rfl
  | ok o => exact congrArg Except.ok (hfg o)

/-- A block, read through its states: the body, its locals popped. -/
theorem Stmt.runSt_block (σ : State C Γ) (P : Prog C Γ Γ₁) :
    Stmt.runSt σ (.block P) = (Prog.runSt σ P).map (State.drop P.ext) :=
  TRes.map_st _ _ _ fun _ => rfl

/-- An `if`, read through its states. -/
theorem Stmt.runSt_ite {Γ₂ : Ctx} (σ : State C Γ) (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) :
    Stmt.runSt σ (.ite c thn els) =
      (c.evalT σ).bind fun v => if boolT v then (Prog.runSt σ thn).map (State.drop thn.ext)
        else (Prog.runSt σ els).map (State.drop els.ext) := by
  unfold Stmt.runSt
  show (TRun.ite c thn.ext thn.runR els.ext els.runR σ).map _ = _
  unfold TRun.ite
  cases c.evalT σ with
  | error => rfl
  | ok v => cases v <;> exact TRes.map_st _ _ _ fun _ => rfl

end Runs

/-! ## Premise shapes -/

section Shapes

variable {Γ Γ' Γ₁ Γ₀ : Ctx} {m : Modality}

/-- An update that halts computed halts in its global part. -/
theorem Upd.globT_none_of_applyV {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ}
    (h : U.applyV σ₀ = none) : U.globT σ₀ = none := by
  cases hg : U.globT σ₀ with
  | none => rfl
  | some g =>
    obtain ⟨ℓ, hℓ⟩ := Upd.applyV_of_globT U hg
    rw [hℓ] at h; cases h

/-- What an update computes, its global part's heap extension forgotten. -/
def Upd.applyP {Δ : Ctx} (σ₀ : State C Γ) (U : Upd C Γ Δ) : Option (State C [] × LocsV C Δ) :=
  (U.applyV σ₀).map fun q => (q.1.1, q.2)

/-- What the update computes is a typed state's parts: it lands there. -/
theorem Upd.lands_of_applyP {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {τ : State C Δ}
    (h : U.applyP σ₀ = some (τ.glob, τ.locV)) : ∃ g, U.Lands σ₀ g τ := by
  unfold Upd.applyP at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨g, ℓ⟩, hq, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨hg, rfl⟩ := he
  exact ⟨g, Upd.lands_iff_applyV.2 ⟨_, hq, hg.symm, fun _ => rfl⟩⟩

/-- **An update**: `{U} ⟨ ω κ ⟩ φ` gives `⟨ s; ω κ ⟩ φ` when `U` computes the
global part and the locals of the state `s` ends in (`Upd.applyP`), and `s`
halts only where `U` does under the diamond (but when it is exhausted, which
both modalities accept), never in a panic. -/
theorem Premise.sound_updateH {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : State C Γ)
    (hs : ∀ τ, Stmt.runSt σ s = .ok τ → U.applyP σ = some (τ.glob, τ.locV))
    (hh : ∀ e, Stmt.runSt σ s = .error e →
      e ≠ .panic ∧ (m = .diamond → e ≠ .exhausted → U.applyV σ = none ∧ U.exh σ = false)) :
    Premise.Sound m s (.update U) σ := by
  intro _ _ ω κ φ h
  rw [holds_modal_iff, runSt_cons_frames]
  cases hτ : Stmt.runSt σ s with
  | ok τ =>
    obtain ⟨g, hl⟩ := Upd.lands_of_applyP (hs τ hτ)
    exact (holds_modal_iff τ ω κ φ).1 (holds_modalK τ ω κ φ (h.of_lands hl))
  | error e =>
    obtain ⟨hp, hd⟩ := hh e hτ
    refine ⟨?_, fun he => hp (Except.error.inj he)⟩
    cases m with
    | box => trivial
    | diamond =>
      show e = .exhausted
      by_cases hx : e = .exhausted
      · exact hx
      · exact (h.of_noExh (Upd.globT_none_of_applyV (hd rfl hx).1) (hd rfl hx).2).elim

/-- Successful sequential updates, as in `a.push() += x`, land on an
intermediate state before computing the final state. -/
def Upd.PairLands {Δ : Ctx} (U : Upd C Γ Δ) (V : Upd C Δ Γ')
    (σ : State C Γ) (τ : State C Γ') : Prop :=
  ∃ ρ : State C Δ, U.applyP σ = some (ρ.glob, ρ.locV) ∧
    V.applyP ρ = some (τ.glob, τ.locV)

/-- An ordinary halt in `{U} {V}`: either `U` fails without exhaustion, or
`U` lands and `V` fails without exhaustion. For example, division by zero
after appending a slot must not prove a returning diamond. -/
def Upd.PairFails {Δ : Ctx} (U : Upd C Γ Δ) (V : Upd C Δ Γ') (σ : State C Γ) : Prop :=
  (U.applyV σ = none ∧ U.exh σ = false) ∨
    ∃ ρ : State C Δ, U.applyP σ = some (ρ.glob, ρ.locV) ∧
      V.applyV ρ = none ∧ V.exh ρ = false

/-- A postcondition after both updates holds in their final state; `V`
reads the slot which `U` appended. -/
theorem Upd.afterT_pair_of_lands {Δ : Ctx} {U : Upd C Γ Δ} {V : Upd C Δ Γ'}
    {σ : State C Γ} {τ : State C Γ'} {P : State C Γ' → Prop}
    (h : U.afterT m σ (fun ρ => V.afterT m ρ P)) (hs : U.PairLands V σ τ) : P τ := by
  obtain ⟨ρ, hU, hV⟩ := hs
  exact (h.of_lands (Upd.lands_of_applyP hU).choose_spec).of_lands
    (Upd.lands_of_applyP hV).choose_spec

/-- A non-exhaustion halt in either update refutes a diamond, including
division by zero in the second update. -/
theorem Upd.afterT_pair_noHalt {Δ : Ctx} {U : Upd C Γ Δ} {V : Upd C Δ Γ'}
    {σ : State C Γ} {P : State C Γ' → Prop}
    (h : U.afterT m σ (fun ρ => V.afterT m ρ P)) (hf : U.PairFails V σ) : m.onHalt := by
  rcases hf with ⟨hU, hx⟩ | ⟨ρ, hU, hV, hx⟩
  · exact h.of_noExh (Upd.globT_none_of_applyV hU) hx
  · exact (h.of_lands (Upd.lands_of_applyP hU).choose_spec).of_noExh
      (Upd.globT_none_of_applyV hV) hx

/-- Run agreement for the two updates of `a.push() += x`, including failure
of the append and of the arithmetic save. -/
def Premise.UpdatesRuns {Δ : Ctx} (m : Modality) (s : Stmt C Γ Γ')
    (U : Upd C Γ Δ) (V : Upd C Δ Γ') (σ : State C Γ) : Prop :=
  (∀ τ, Stmt.runSt σ s = .ok τ → U.PairLands V σ τ) ∧
    (∀ e, Stmt.runSt σ s = .error e → e ≠ .panic ∧
      (m = .diamond → e ≠ .exhausted → U.PairFails V σ))

/-- Agreement for `a.push() += x`: successful outcomes land through both
updates; a revert fails one stage; exhaustion is allowed by both modalities.
Panic and divergence cannot be represented by these update premises. -/
def Upd.PairAgrees {Δ : Ctx} (U : Upd C Γ Δ) (V : Upd C Δ Γ') (σ : State C Γ) :
    TRes (Out C σ.H Γ') → Prop
  | .ok o => U.PairLands V σ o.st
  | .error .revert => U.PairFails V σ
  | .error .exhausted => True
  | .error .panic | .error .diverge | .error (.revertWith _) => False

/-- Agreement with the typed run supplies both modal run conditions for
`a.push() += x`, without an additional storage invariant. -/
theorem Premise.updatesRuns_of_agrees {Δ : Ctx} {U : Upd C Γ Δ} {V : Upd C Δ Γ'}
    {s : Stmt C Γ Γ'} (σ : State C Γ) (ha : U.PairAgrees V σ (s.run σ)) :
    Premise.UpdatesRuns m s U V σ := by
  constructor
  · intro τ hτ
    simp only [Stmt.runSt] at hτ
    cases ht : s.run σ with
    | error => rw [ht] at hτ; cases hτ
    | ok o =>
      rw [ht] at hτ ha
      obtain rfl : o.st = τ := Except.ok.inj hτ
      exact ha
  · intro e he
    simp only [Stmt.runSt] at he
    cases ht : s.run σ with
    | ok o => rw [ht] at he; cases he
    | error e' =>
      rw [ht] at he ha
      obtain rfl : e' = e := Except.error.inj he
      cases e' with
      | revert => exact ⟨nofun, fun _ _ => ha⟩
      | exhausted => exact ⟨nofun, fun _ hx => absurd rfl hx⟩
      | panic | diverge | revertWith _ => exact ha.elim

/-- `{U} {V} ⟨ ω κ ⟩ φ` is sound when both updates agree with the run;
in `a.push() += x`, arithmetic reads the newly appended slot. -/
theorem Premise.sound_updatesH {Δ : Ctx} {U : Upd C Γ Δ} {V : Upd C Δ Γ'}
    {s : Stmt C Γ Γ'} (σ : State C Γ) (hr : Premise.UpdatesRuns m s U V σ) :
    Premise.Sound m s (.updates U V) σ := by
  intro _ _ ω κ φ h
  rw [holds_modal_iff, runSt_cons_frames]
  cases hτ : Stmt.runSt σ s with
  | ok τ =>
    exact (holds_modal_iff τ ω κ φ).1 (holds_modalK τ ω κ φ
      (Upd.afterT_pair_of_lands h (hr.1 τ hτ)))
  | error e =>
    obtain ⟨hp, hd⟩ := hr.2 e hτ
    refine ⟨?_, fun he => hp (Except.error.inj he)⟩
    cases m with
    | box => trivial
    | diamond =>
      show e = .exhausted
      by_cases hx : e = .exhausted
      · exact hx
      · exact (Upd.afterT_pair_noHalt h (hd rfl hx)).elim

/-- **A block dropping a frame from under what it keeps**
(`Premise.inline`). -/
theorem Premise.sound_inline {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Thin Γ' Γ''} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : (Prog.runSt σ P).map (State.thin h) = Stmt.runSt σ s) :
    Premise.Sound m s (.inline P h) σ := by
  intro _ _ ω κ φ hp
  have h' := (holds_modal_iff σ P (.drop h (.seq ω κ)) φ).1 hp
  rw [holds_modal_iff, runSt_cons_frames, ← hs]
  revert h'
  cases Prog.runSt σ P with
  | error => exact id
  | ok τ =>
    intro h'
    change m.afterRunTR _ (Frames.runSt τ (.drop h (.seq ω κ))) at h'
    rw [Frames.runSt_drop, Frames.runSt_seq] at h'
    exact h'

/-- **A hidden binder**: `∀ v. ⟨ P ω κ ⟩ φ` from `σ` with `v` pushed gives
`⟨ s; ω κ ⟩ φ` when, for some `v` of its type, `P` runs from there as `s`
from `σ`. -/
theorem Premise.sound_bindH {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : ∃ v : t.TDenote C σ.H, Prog.runSt (σ.push v) P = Stmt.runSt σ s) :
    Premise.Sound m s (.bind x t P) σ := by
  intro _ _ ω κ φ h
  obtain ⟨v, hv⟩ := hs
  have h' := (holds_modal_iff (σ.push v) P (.seq ω κ) φ).1 (Modality.forallB_all h v)
  rw [holds_modal_iff, runSt_cons_frames, ← hv]
  revert h'
  cases Prog.runSt (σ.push v) P with
  | error => exact id
  | ok τ =>
    intro h'
    change m.afterRunTR _ (Frames.runSt τ (.seq ω κ)) at h'
    rw [Frames.runSt_seq] at h'
    exact h'

/-- A block's run, its locals popped, then the rest and the frames: the
frame a branch ends with (`pop b P.ext`). -/
theorem runSt_block_frames {Δ : Ctx} (b : BlockKind) (P : Prog C Γ Δ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (σ : State C Γ) :
    (Prog.runSt σ P).bind (Frames.runSt · (.pop b P.ext (.seq ω κ))) =
      ((Prog.runSt σ P).map (State.drop P.ext)).bind fun τ =>
        (Prog.runSt τ ω).bind (Frames.runSt · κ) := by
  cases Prog.runSt σ P with
  | error => rfl
  | ok τ =>
    show Frames.runSt τ (.pop b P.ext (.seq ω κ)) = _
    rw [Frames.runSt_pop, Frames.runSt_seq]
    rfl

/-- **Two goals**: `(c → ⟨ P } ω κ ⟩ φ) ∧ (c' → ⟨ Q } ω κ ⟩ φ)` gives
`⟨ s; ω κ ⟩ φ` when one of `c`, `c'` holds, and the branch it guards, its
locals popped, runs as `s`. -/
theorem Premise.sound_splitH {b : BlockKind} {Δ₁ Δ₂ : Ctx} {c c' : Fml C Γ} {P : Prog C Γ Δ₁}
    {Q : Prog C Γ Δ₂} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hc : holds σ c → (Prog.runSt σ P).map (State.drop P.ext) = Stmt.runSt σ s)
    (hc' : holds σ c' → (Prog.runSt σ Q).map (State.drop Q.ext) = Stmt.runSt σ s)
    (hcov : holds σ c ∨ holds σ c') : Premise.Sound m s (.split b c c' P Q) σ := by
  rintro _ _ ω κ φ ⟨h₁, h₂⟩
  rw [holds_modal_iff, runSt_cons_frames]
  rcases hcov with h | h
  · have := (holds_modal_iff σ P _ φ).1 (holds_modalK σ P _ φ (h₁ h))
    rw [runSt_block_frames, hc h] at this
    exact this
  · have := (holds_modal_iff σ Q _ φ).1 (holds_modalK σ Q _ φ (h₂ h))
    rw [runSt_block_frames, hc' h] at this
    exact this

/-- **A check**: `(c → ⟨ ω κ ⟩ φ) ∧ c` gives `⟨ s; ω κ ⟩ φ` when, `c`
holding, `s` does nothing. -/
theorem Premise.sound_check {c : Fml C Γ} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hc : holds σ c → Stmt.runSt σ s = .ok σ) : Premise.Sound m s (.check c) σ := by
  rintro _ _ ω κ φ ⟨h₁, h₂⟩
  rw [holds_modal_iff, runSt_cons_frames, hc h₂]
  exact (holds_modal_iff σ ω κ φ).1 (holds_modalK σ ω κ φ (h₁ h₂))

/-- **A closed goal**: `true` gives a box over a statement that halts, not in
a panic. -/
theorem Premise.sound_done {s : Stmt C Γ Γ'} (σ : State C Γ) (b : Bool)
    (hs : b = true → m = .box ∧ ∃ e, Stmt.runSt σ s = .error e ∧ e ≠ .panic) :
    Premise.Sound m s (.done b) σ := by
  intro _ _ ω κ φ h
  cases b with
  | false => exact absurd trivial h
  | true =>
    obtain ⟨rfl, e, he, hp⟩ := hs rfl
    rw [holds_modal_iff, runSt_cons_frames, he]
    exact ⟨trivial, fun h => hp (Except.error.inj h)⟩

/-- A closing taclet on a statement that runs out (`assumeFalse`): `true`
under either modality. -/
theorem Premise.sound_done_exhausted {s : Stmt C Γ Γ'} (σ : State C Γ)
    (hs : Stmt.runSt σ s = .error .exhausted) : Premise.Sound m s (.done true) σ := by
  intro _ _ ω κ φ _
  rw [holds_modal_iff, runSt_cons_frames, hs]
  cases m <;> exact ⟨by first | trivial | rfl, nofun⟩

end Shapes

/-! ## The per-arm statement

Each arm of `Stmt.step` proves, for its statement, that the premise it
gives is sound in a typed state `σ` (`Premise.Sound`): its theorem is named
after the arm (`localStep_sound`) and takes `σ` first, then the arm's arguments, the premise `q` and
`hq : …Step k … = q`.  No arm takes a condition: decisions 15 and 16
took two away (a push at the bound is exhausted; no struct repeats a member
name), and 17' the last (a memory local may be unset, so the box
`memoryLocalDeclInitDrop`'s binder has the instance its premise needs). -/


/-! ## Evaluators revert -/

section Revert

variable {Γ : Ctx} (σ : State C Γ)

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
(`Modality.afterRunTR`): `TRes.Sim`, over the typed run. -/

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
theorem Premise.sound_unfoldSimH {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''}
    {s : Stmt C Γ Γ'} (σ : State C Γ)
    (hs : TRes.Sim ((Prog.runSt σ P).map (State.drop h)) (Stmt.runSt σ s)) :
    Premise.Sound m s (.unfold P h) σ := by
  intro _ _ ω κ φ hp
  have h' := (holds_modal_iff σ P (.pop .capture h (.seq ω κ)) φ).1 hp
  rw [holds_modal_iff, runSt_cons_frames]
  have e : (Prog.runSt σ P).bind (Frames.runSt · (.pop .capture h (.seq ω κ))) =
      ((Prog.runSt σ P).map (State.drop h)).bind fun τ =>
        (Prog.runSt τ ω).bind (Frames.runSt · κ) := by
    cases Prog.runSt σ P with
    | error => rfl
    | ok τ =>
      show Frames.runSt τ (.pop .capture h (.seq ω κ)) = _
      rw [Frames.runSt_pop, Frames.runSt_seq]
      rfl
  rw [e] at h'
  exact (hs.bind _).afterRunTR h'


/-! ## What a premise asks of the typed run

`Premise.Sound` reads a premise in the formulas. For one update, two
sequential updates (through their intermediate typed state), a block,
a hidden binder and a split, what the shapes above ask of the statement's
typed run is kept as it is (`Premise.Runs`, any other kind read as
`Premise.Sound`): the arms prove that, it gives `Premise.Sound`
(`Premise.Runs.sound`), and the reading with callbacks too
(`Calculus/CallbackSound.lean`), where the rest of the program is read
over runs that may call back. -/

/-- Run conditions for `sp.push() /= se`: the true branch agrees with the
sequential updates; the false branch simulates revert without success or panic. -/
def Premise.GuardedUpdatesRuns {Γ Δ : Ctx} (m : Modality) (s : Stmt C Γ Γ)
    (c : Fml C Γ) (U : Upd C Γ Δ) (V : Upd C Δ Γ) (σ : State C Γ) : Prop :=
  c.hasTransfer = false ∧
    (holds σ c → Premise.UpdatesRuns m s U V σ) ∧
    (¬ holds σ c → TRes.Sim (.error .revert) (Stmt.runSt σ s))

/-- `sp.push() /= se`: preserve the outer zero-divisor test and both
updates; the false branch reverts, or exhausts at the interpreter's bound. -/
theorem Premise.sound_guardedUpdatesH {Γ Δ : Ctx} {m : Modality}
    {s : Stmt C Γ Γ} {c : Fml C Γ} {U : Upd C Γ Δ} {V : Upd C Δ Γ}
    (σ : State C Γ) (hr : Premise.GuardedUpdatesRuns m s c U V σ) :
    Premise.Sound m s (.guardedUpdates c U V) σ := by
  intro _ _ ω κ φ h
  by_cases hc : holds σ c
  · exact Premise.sound_updatesH σ (hr.2.1 hc) ω κ φ (h.1 hc)
  · have he := (holds_modal_iff σ (.cons .revert ω) κ φ).1 (h.2 hc)
    rw [holds_modal_iff, runSt_cons_frames]
    exact ((hr.2.2 hc).bind _).afterRunTR he

/-- **What the premise `p` asks of the typed run of `s` from `σ`**, by its
kind. -/
def Premise.Runs (m : Modality) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → State C Γ → Prop
  | _, _, s, .update U, σ => (∀ τ, Stmt.runSt σ s = .ok τ → U.applyP σ = some (τ.glob, τ.locV)) ∧
      (∀ e, Stmt.runSt σ s = .error e →
        e ≠ .panic ∧ (m = .diamond → e ≠ .exhausted → U.applyV σ = none ∧ U.exh σ = false))
  | _, _, s, .updates U V, σ => Premise.UpdatesRuns m s U V σ
  | _, _, s, .guardedUpdates c U V, σ => Premise.GuardedUpdatesRuns m s c U V σ
  | _, _, s, .unfold P h, σ => TRes.Sim ((Prog.runSt σ P).map (State.drop h)) (Stmt.runSt σ s)
  | _, _, s, .bind _ t P, σ => ∃ v : t.TDenote C σ.H, Prog.runSt (σ.push v) P = Stmt.runSt σ s
  | _, _, s, .split _ c c' P Q, σ =>
      (holds σ c → (Prog.runSt σ P).map (State.drop P.ext) = Stmt.runSt σ s ∧
        ∀ (J : StateInv C) (o : COut C σ.H _), ExecS J σ s o →
          ∃ o', ExecP J σ P o' ∧ o = o'.map (Out.drop P.ext)) ∧
      (holds σ c' → (Prog.runSt σ Q).map (State.drop Q.ext) = Stmt.runSt σ s ∧
        ∀ (J : StateInv C) (o : COut C σ.H _), ExecS J σ s o →
          ∃ o', ExecP J σ Q o' ∧ o = o'.map (Out.drop Q.ext)) ∧
      (holds σ c ∨ holds σ c') ∧ c.hasTransfer = false ∧ c'.hasTransfer = false
  | _, _, s, p, σ => Premise.Sound m s p σ

/-- **What the run gives, the premise gives in the formulas.** -/
theorem Premise.Runs.sound {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {p : Premise C Γ Γ'}
    {σ : State C Γ} (h : Premise.Runs m s p σ) : Premise.Sound m s p σ := by
  cases p with
  | update U => exact Premise.sound_updateH σ h.1 h.2
  | updates U V => exact Premise.sound_updatesH σ h
  | guardedUpdates c U V => exact Premise.sound_guardedUpdatesH σ h
  | unfold P e => exact Premise.sound_unfoldSimH σ h
  | bind x t P => exact Premise.sound_bindH σ h
  | split b c c' P Q =>
    exact Premise.sound_splitH σ (fun hc => (h.1 hc).1) (fun hc => (h.2.1 hc).1) h.2.2.1
  | check _ => exact h
  | done _ => exact h
  | branches _ => exact h
  | cases _ _ => exact h
  | inv _ _ _ _ _ _ _ _ _ _ => exact h
  | inline _ _ => exact h

/-- **An update** (`Premise.sound_updateH`'s conditions). -/
theorem Premise.sound_update {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : State C Γ)
    (hs : ∀ τ, Stmt.runSt σ s = .ok τ → U.applyP σ = some (τ.glob, τ.locV))
    (hh : ∀ e, Stmt.runSt σ s = .error e →
      e ≠ .panic ∧ (m = .diamond → e ≠ .exhausted → U.applyV σ = none ∧ U.exh σ = false)) :
    Premise.Runs m s (.update U) σ := ⟨hs, hh⟩

/-- **A block**, up to the halt. -/
theorem Premise.sound_unfoldSim {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''}
    {s : Stmt C Γ Γ'} (σ : State C Γ)
    (hs : TRes.Sim ((Prog.runSt σ P).map (State.drop h)) (Stmt.runSt σ s)) :
    Premise.Runs m s (.unfold P h) σ := hs

/-- **A block**. -/
theorem Premise.sound_unfold {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : (Prog.runSt σ P).map (State.drop h) = Stmt.runSt σ s) :
    Premise.Runs m s (.unfold P h) σ := TRes.Sim.of_eq hs

/-- **A hidden binder**. -/
theorem Premise.sound_bind {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : ∃ v : t.TDenote C σ.H, Prog.runSt (σ.push v) P = Stmt.runSt σ s) :
    Premise.Runs m s (.bind x t P) σ := hs

/-- **A hidden binder, every value**: a statement that runs as `P` from
`σ` with any value of its type pushed.  Every type has one
(`LTy.tdenote_nonempty`: a memory local may be unset, decision 17'). -/
theorem Premise.sound_bind_all {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    (σ : State C Γ) (hs : ∀ v : t.TDenote C σ.H, Prog.runSt (σ.push v) P = Stmt.runSt σ s) :
    Premise.Runs m s (.bind x t P) σ :=
  let ⟨v⟩ := LTy.tdenote_nonempty (C := C) (H := σ.H) t
  Premise.sound_bind σ ⟨v, hs v⟩

/-- **Two goals**. -/
theorem Premise.sound_split {b : BlockKind} {Δ₁ Δ₂ : Ctx} {c c' : Fml C Γ} {P : Prog C Γ Δ₁}
    {Q : Prog C Γ Δ₂} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hc : holds σ c → (Prog.runSt σ P).map (State.drop P.ext) = Stmt.runSt σ s)
    (hc' : holds σ c' → (Prog.runSt σ Q).map (State.drop Q.ext) = Stmt.runSt σ s)
    (hcov : holds σ c ∨ holds σ c')
    (hcb : holds σ c → ∀ (J : StateInv C) (o : COut C σ.H Γ), ExecS J σ s o →
      ∃ o', ExecP J σ P o' ∧ o = o'.map (Out.drop P.ext))
    (hcb' : holds σ c' → ∀ (J : StateInv C) (o : COut C σ.H Γ), ExecS J σ s o →
      ∃ o', ExecP J σ Q o' ∧ o = o'.map (Out.drop Q.ext))
    (hT : c.hasTransfer = false := by rfl) (hT' : c'.hasTransfer = false := by rfl) :
    Premise.Runs m s (.split b c c' P Q) σ :=
  ⟨fun h => ⟨hc h, hcb h⟩, fun h => ⟨hc' h, hcb' h⟩, hcov, hT, hT'⟩

/-- Two typed runs that end in the same states end alike: an outcome is its
state, the heap's growth a proof. -/
theorem TRes.eq_of_map_st {H : HTy} {Δ : Ctx} {r r' : TRes (Out C H Δ)}
    (h : r.map (·.st) = r'.map (·.st)) : r = r' := by
  cases r with
  | ok a =>
    cases r' with
    | ok b =>
      have e : a.st = b.st := Except.ok.inj h
      cases a; cases b
      cases e
      rfl
    | error => cases h
  | error e =>
    cases r' with
    | ok => cases h
    | error e' => rw [show e = e' from Except.error.inj h]

/-- A statement that runs no other by a choice and pays nothing has one
callback run, its typed run. -/
theorem ExecS.det_inv {Γ Γ' : Ctx} {σ : State C Γ} {J : StateInv C} {s : Stmt C Γ Γ'}
    {o : COut C σ.H Γ'} (h : ExecS J σ s o) (hs : s.forks = false) : o = .ofRes (s.run σ) :=
  ExecS.eq_run_of_forksIn h (Stmt.forksIn_of_forks hs)

/-- The same, where only a `try` calls back unless `J.pay`
(`Stmt.forksIn`). -/
theorem ExecS.detIn_inv {Γ Γ' : Ctx} {σ : State C Γ} {J : StateInv C} {s : Stmt C Γ Γ'}
    {o : COut C σ.H Γ'} (h : ExecS J σ s o) (hs : s.forksIn J.pay = false) :
    o = .ofRes (s.run σ) :=
  ExecS.eq_run_of_forksIn h hs

/-- **A statement that runs no other by a choice runs with callbacks as a
branch that pays nothing**, where it runs so without. -/
theorem ExecS.split_det {s : Stmt C Γ Γ} {Δ : Ctx} {P : Prog C Γ Δ} (σ : State C Γ)
    (hs : s.forks = false) (hP : Prog.hasTransfer P = false)
    (h : (Prog.runSt σ P).map (State.drop P.ext) = Stmt.runSt σ s) (J : StateInv C)
    (o : COut C σ.H Γ) (he : ExecS J σ s o) :
    ∃ o', ExecP J σ P o' ∧ o = o'.map (Out.drop P.ext) := by
  have e : (Prog.run σ P).map (Out.drop P.ext) = s.run σ := by
    refine TRes.eq_of_map_st ?_
    have h' : ((Prog.run σ P).map (·.st)).map (State.drop P.ext) = (s.run σ).map (·.st) := h
    rw [← h']
    cases Prog.run σ P <;> rfl
  have ho : o = .ofRes (s.run σ) := ExecS.det_inv he hs
  refine ⟨.ofRes (Prog.run σ P), ?_, by rw [ho, ← e, COut.map_ofRes]⟩
  rcases Prog.exec_run J P σ with hx | hx
  · exact hx
  · have := ExecP.eq_run hx (Prog.callsBack_of_hasTransfer P hP)
    revert this
    cases Prog.run σ P <;> exact fun h => nomatch h

/-- **The rule of `s` is sound over the typed state** (`Stmt.StepSound`,
over `State`), in every typed state: its premise asks of the run what
`Premise.Runs` says. -/
def Stmt.StepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ σ : State C Γ, ∀ p, s.step k m = p → Premise.Runs m s p σ

/-- A one-statement sequence runs as its statement. -/
theorem Prog.runSt_single {Γ' : Ctx} (σ : State C Γ) (s : Stmt C Γ Γ') :
    Prog.runSt σ (.cons s .nil) = Stmt.runSt σ s := by
  rw [Prog.runSt_cons]
  cases Stmt.runSt σ s <;> rfl

/-- `T se = nse;`, typed: the value read, then pushed. -/
theorem Stmt.runSt_declLocal (σ : State C Γ) (p : PrimTy) (x : Var) (e : Val C Γ p) :
    Stmt.runSt σ (.declLocal p x (some e)) = (e.evalT σ).map fun v => σ.push (t := .val p) v := by
  show (TRun.declLocal p (some e) σ).map _ = _
  simp only [TRun.declLocal]
  cases e.evalT σ <;> rfl

/-- `T storage sp = nsp;`, typed: the path resolved, then pushed. -/
theorem Stmt.runSt_declStorage (σ : State C Γ) (R : RefTy) (x : Var) (b : SPath C Γ (.ref R)) :
    Stmt.runSt σ (.declStorage R x (some (.path b))) =
      (b.resolveT σ).map fun q => σ.push (t := .alias R) (some q) := by
  show (TRun.declStorage R (some (.path b)) σ).map _ = _
  simp only [TRun.declStorage, ARhs.evalT]
  cases b.resolveT σ <;> rfl

/-- `T memory mv = nmp;`, typed: the object read, then pushed. -/
theorem Stmt.runSt_declMem (σ : State C Γ) (R : RefTy) (x : Var) (b : MPath C Γ (.ref R)) :
    Stmt.runSt σ (.declMem R x (some (.alias b)) rfl b.mapFree) =
      (b.mvalT σ).map fun r => σ.push (t := .mem R) (some r) := by
  show (TRun.declMem R (some (.alias b)) b.mapFree σ).map _ = _
  simp only [TRun.declMem, MRhs.evalT]
  cases b.mvalT σ <;> rfl

/-- A declaration that reads a part (`X`) and pushes it (`inj`), then a
sequence: the part read, then the sequence over it. -/
theorem Prog.runSt_declCons {t : LTy} {α : Type} {Γ₁ : Ctx} {σ : State C Γ}
    {d : Stmt C Γ (t :: Γ)} {X : TRes α} {inj : α → t.TDenote C σ.H}
    (hd : Stmt.runSt σ d = X.map fun a => σ.push (inj a)) (P : Prog C (t :: Γ) Γ₁) :
    Prog.runSt σ (.cons d P) = X.bind fun a => Prog.runSt (σ.push (inj a)) P := by
  rw [Prog.runSt_cons, hd]
  cases X <;> rfl

end ShapesSim

/-! ## An update, against the typed step

An update rule's update is computed on the typed state as a global part and
the locals' values (`Upd.applyP`), so what it needs of the typed run
(`Premise.sound_update`) follows from the statement's typed step agreeing
with it (`TRes.AgreesO`, the state the step ends in read so, `none` for a
`revert`, no `panic`).  A typed `diverge` agrees with any reading, so under
the diamond the arm shows that it does not happen (no update arm's
statement loops; a push at the bound is exhausted, `TRun.push_nd`, which
agrees with anything too and which both modalities accept). -/

/-- An update the arms leave pushes nothing: it is never out of gas
(`Upd.exh_of_pushFree`, the lowered parts' `…_pushFree`). -/
macro "exh_free" : tactic => `(tactic| (
  intro _
  apply Upd.exh_of_pushFree
  try simp only [Upd.pushFree, OpLoc.set_pushFree, UpdElem.clearMem_pushFree]
  simp only [Upd.pushFree, UpdElem.pushFree, Rhs.pushFree, Tm.pushFree, Op2.pushFree,
    Op3.pushFree, Simple.lower_pushFree, Val.lower_pushFree, SPath.lower_pushFree,
    Loc.lower_pushFree, MPath.lower_pushFree, MLoc.lower_pushFree, Src.lower_pushFree,
    MSrc.lower_pushFree, Tm.mread_pushFree, Tm.castV_pushFree,
    OpLoc.cur_pushFree, OpLoc.set_pushFree, OpLoc.op_pushFree, Tm.bumped_pushFree,
    Tm.one_pushFree, UpdElem.setLocal, UpdElem.save, UpdElem.saveMem, UpdElem.delAt,
    UpdElem.writeMem, UpdElem.pop, UpdElem.shrink, UpdElem.payTo, UpdElem.rebind,
    UpdElem.rebindMem, Upd.allocCopy, Upd.allocFresh, MLoc.lower_pushFree, Bool.and_self,
    Bool.and_true, Bool.true_and]))

section Bridge

variable {Γ Γ' : Ctx} {m : Modality}

/-- **An update, against what the statement's typed run agrees with**
(`X`, which the update computes). -/
theorem Premise.sound_updateSim_agrees {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : State C Γ)
    {X : Option (State C [] × LocsV C Γ')}
    (ha : TRes.AgreesO (fun o : Out C σ.H Γ' => (o.st.glob, o.st.locV)) (s.run σ) X)
    (hs : U.applyP σ = X)
    (hd : m = .diamond → (s.run σ).NoDiv)
    (hx : s.run σ = .error .revert → U.exh σ = false) : Premise.Runs m s (.update U) σ := by
  subst hs
  apply Premise.sound_update σ
  · intro τ hτ
    simp only [Stmt.runSt] at hτ
    cases ht : s.run σ with
    | error => rw [ht] at hτ; cases hτ
    | ok o =>
      rw [ht] at hτ ha
      obtain rfl : o.st = τ := Except.ok.inj hτ
      exact ha
  · intro e he
    simp only [Stmt.runSt] at he
    cases ht : s.run σ with
    | ok o => rw [ht] at he; cases he
    | error e' =>
      rw [ht] at he ha
      obtain rfl : e' = e := Except.error.inj he
      cases e' with
      | revert =>
        have ha' : U.applyP σ = none := ha
        refine ⟨nofun, fun _ _ => ⟨?_, hx ht⟩⟩
        unfold Upd.applyP at ha'
        exact Option.map_eq_none_iff.1 ha'
      | panic => exact ha.elim
      | revertWith _ => exact ha.elim
      | diverge => exact ⟨nofun, fun hm _ => absurd ht (hd hm)⟩
      | exhausted => exact ⟨nofun, fun _ hx => absurd rfl hx⟩

/-- **An update, against the typed run**, through what the statement's
typed step agrees with (`X`). -/
theorem Premise.sound_updateSim_typed {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} {t : TStep C Γ Γ'}
    (σ : State C Γ) {X : Option (State C [] × LocsV C Γ')}
    (ha : TRes.AgreesO (fun o : Out C σ.H Γ' => (o.st.glob, o.st.locV)) (t σ) X)
    (hs : U.applyP σ = X)
    (hd : m = .diamond → (s.run σ).NoDiv) (ht : s.run σ = t σ := by rfl)
    (hx : t σ = .error .revert → U.exh σ = false := by exh_free) :
    Premise.Runs m s (.update U) σ :=
  Premise.sound_updateSim_agrees σ (by rw [ht]; exact ha) hs hd (by rw [ht]; exact hx)

/-- **An update, against the typed run**: the statement's typed step agrees
with what the update computes. -/
theorem Premise.sound_update_typed {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} {t : TStep C Γ Γ'}
    (σ : State C Γ)
    (ha : TRes.AgreesO (fun o : Out C σ.H Γ' => (o.st.glob, o.st.locV)) (t σ) (U.applyP σ))
    (hd : m = .diamond → (s.run σ).NoDiv) (ht : s.run σ = t σ := by rfl)
    (hx : t σ = .error .revert → U.exh σ = false := by exh_free) :
    Premise.Runs m s (.update U) σ :=
  Premise.sound_updateSim_typed σ ha rfl hd ht hx

theorem holds_conj {σ : State C Γ} :
    (l : List (Fml C Γ)) → (holds σ (Fml.conj l) ↔ ∀ ψ ∈ l, holds σ ψ)
  | [] => by simp only [Fml.conj, holds, List.not_mem_nil, false_implies, implies_true]
  | [φ] => by simp only [Fml.conj, List.mem_singleton, forall_eq]
  | φ :: ψ :: l => by
    show holds σ φ ∧ holds σ (Fml.conj (ψ :: l)) ↔ _
    rw [holds_conj (ψ :: l)]
    simp only [List.mem_cons, forall_eq_or_imp]

/-- **Labelled goals, against the typed run**: the formulas `fs`, then the
rest after each update of `us`, give `⟨ s; ω κ ⟩ φ` when, the formulas
holding, one of the updates ends as what the statement's typed step agrees
with, up to the halt. -/
theorem Premise.sound_cases_typed {fs : List (Fml C Γ)} {us : List (Upd C Γ Γ)} {s : Stmt C Γ Γ}
    {t : TStep C Γ Γ} (σ : State C Γ) {X : Option (State C [] × LocsV C Γ)}
    (ha : TRes.AgreesO (fun o : Out C σ.H Γ => (o.st.glob, o.st.locV)) (t σ) X)
    (h : (∀ f ∈ fs, holds σ f) → ∃ U ∈ us, U.applyP σ = X)
    (hd : m = .diamond → (s.run σ).NoDiv) (ht : s.run σ = t σ := by rfl)
    (hx : ∀ U ∈ us, t σ = .error .revert → U.exh σ = false) :
    Premise.Sound m s (.cases fs us) σ := by
  intro Γ₁ Γ₀ ω κ φ hp
  have hp' := (holds_conj _).1 hp
  obtain ⟨U, hU, hs⟩ := h fun f hf => hp' f (List.mem_append_left _ hf)
  exact (Premise.sound_updateSim_typed σ ha hs hd ht (hx U hU)).sound ω κ φ
    (hp' _ (List.mem_append_right _ (List.mem_map_of_mem hU)))

end Bridge

/-! ## A shifted part reads as it did

A rule reads the parts of its `\find` under its fresh local
(`Val.up` and its kin, `Calculus/Shift.lean`), and the state with a
local pushed is the state lifted along `up` (`State.push_lift`), so each
is `Semantics/RunWk.lean`'s `*_wk` at `up`. -/

section Shift

variable {Γ : Ctx} {t : LTy} (σ : State C Γ) (w : t.TDenote C σ.H)

theorem State.push_lift : σ.push w = σ.lift up (w, σ.env) := rfl

theorem Simple.evalT_up {p : PrimTy} (s : Simple C Γ p) :
    (s.up (t := t)).evalT (σ.push w) = s.evalT σ := by
  rw [Simple.up_eq]; exact Simple.evalT_wk Solidity.up σ (w, σ.env) s

theorem SPath.resolveT_up {T : Ty} (b : SPath C Γ T) :
    (b.up (t := t)).resolveT (σ.push w) = b.resolveT σ := by
  rw [SPath.up_eq]; exact SPath.resolveT_wk Solidity.up σ (w, σ.env) b

theorem Loc.resolveT_up {T : Ty} (l : Loc C Γ T) :
    (l.up (t := t)).resolveT (σ.push w) = l.resolveT σ := by
  rw [Loc.up_eq]; exact Loc.resolveT_wk Solidity.up σ (w, σ.env) l

theorem MPath.mvalT_up {T : Ty} (b : MPath C Γ T) :
    (b.up (t := t)).mvalT (σ.push w) = b.mvalT σ := by
  rw [MPath.up_eq]; exact MPath.mvalT_wk Solidity.up σ (w, σ.env) b

theorem MLoc.addrT_up {T : Ty} (l : MLoc C Γ T) :
    (l.up (t := t)).addrT (σ.push w) = l.addrT σ := by
  rw [MLoc.up_eq]; exact MLoc.addrT_wk Solidity.up σ (w, σ.env) l

theorem Val.evalT_up {p : PrimTy} (v : Val C Γ p) :
    (v.up (t := t)).evalT (σ.push w) = v.evalT σ := by
  rw [Val.up_eq]; exact Val.evalT_wk Solidity.up σ (w, σ.env) v

theorem Src.valueT_up {T : Ty} (r : Src C Γ T) :
    (r.up (t := t)).valueT (σ.push w) = r.valueT σ := by
  rw [Src.up_eq]; exact Src.valueT_wk Solidity.up σ (w, σ.env) r

theorem MSrc.mvalT_up {T : Ty} (r : MSrc C Γ T) :
    (r.up (t := t)).mvalT (σ.push w) = r.mvalT σ := by
  rw [MSrc.up_eq]; exact MSrc.mvalT_wk Solidity.up σ (w, σ.env) r

theorem ARhs.evalT_up {R : RefTy} (r : ARhs C Γ R) :
    (r.up (t := t)).evalT (σ.push w) = r.evalT σ := by
  rw [ARhs.up_eq]; exact ARhs.evalT_wk Solidity.up σ (w, σ.env) r

theorem State.get_push_here : (TEnv.get .here (σ.push w).env : t.TDenote C σ.H) = w := rfl

theorem State.get_push_there {u : LTy} (i : Idx Γ u) :
    (TEnv.get i.there (σ.push w).env : u.TDenote C σ.H) = TEnv.get i σ.env := rfl

/-- An outcome lifted along `up`, its top local popped: the outcome. -/
theorem liftedT_up_drop (r : TRes (Out C σ.H Γ)) :
    ((liftedT up (w, σ.env) r).map (·.st)).map (State.drop (.push .refl)) = r.map (·.st) := by
  cases r <;> rfl

end Shift

/-! ## Captures, up to the halt

`Calculus/SoundCapture.lean`'s capture shapes over the typed run: the
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

/-- **A part captured**: a declaration `d` that reads the part (`X`, which
halts only by a revert) and pushes it, then `s'`, gives `s`, `s'` running as
`s` with the part on top, and `s` halting alike where the part halts. -/
theorem Premise.sound_captureGen {t : LTy} {α : Type} {d : Stmt C Γ (t :: Γ)}
    {s' : Stmt C (t :: Γ) (t :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ) {X : TRes α}
    {inj : α → t.TDenote C σ.H} (hd : Stmt.runSt σ d = X.map fun a => σ.push (inj a))
    (hX : X.RevertOnly)
    (hok : ∀ a, X = .ok a →
      (Stmt.runSt (σ.push (inj a)) s').map (State.drop (.push .refl)) = Stmt.runSt σ s)
    (herr : ∀ h, X = .error h → h = .revert → TRes.Sim (.error h) (Stmt.runSt σ s)) :
    Premise.Runs m s (.unfold (.cons d (.cons s' .nil)) (.push .refl)) σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [Prog.runSt_declCons hd]
  cases hx : X with
  | ok a =>
    show TRes.Sim ((Prog.runSt _ (.cons s' .nil)).map _) _
    rw [Prog.runSt_single]
    exact TRes.Sim.of_eq (hok a hx)
  | error h => exact herr h hx (hX h hx)

/-- **A value captured**: `T se = nse; s'`. -/
theorem Premise.sound_captureSim {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hok : ∀ v, e.evalT σ = .ok v →
      (Stmt.runSt (σ.push (t := .val p) v) s').map (State.drop (.push .refl)) = Stmt.runSt σ s)
    (herr : ∀ h, e.evalT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.runSt σ s)) :
    Premise.Runs m s (.capture p x e s') σ :=
  Premise.sound_captureGen σ (inj := id) (Stmt.runSt_declLocal σ p x e)
    (Val.evalT_revertOnly σ e) hok herr

/-- **A storage path captured**: `T storage sp = nsp; s'`. -/
theorem Premise.sound_captureSPSim {R : RefTy} {x : Var} {b : SPath C Γ (.ref R)}
    {s' : Stmt C (.alias R :: Γ) (.alias R :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hok : ∀ q, b.resolveT σ = .ok q →
      (Stmt.runSt (σ.push (t := .alias R) (some q)) s').map (State.drop (.push .refl)) =
        Stmt.runSt σ s)
    (herr : ∀ h, b.resolveT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.runSt σ s)) :
    Premise.Runs m s (.captureSP x b s') σ :=
  Premise.sound_captureGen σ (inj := some) (Stmt.runSt_declStorage σ R x b)
    (SPath.resolveT_revertOnly σ b) hok herr

/-- **A memory path captured**: `T memory mv = nmp; s'`. -/
theorem Premise.sound_captureMVSim {R : RefTy} {x : Var} {b : MPath C Γ (.ref R)}
    {s' : Stmt C (.mem R :: Γ) (.mem R :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hok : ∀ r, b.mvalT σ = .ok r →
      (Stmt.runSt (σ.push (t := .mem R) (some r)) s').map (State.drop (.push .refl)) =
        Stmt.runSt σ s)
    (herr : ∀ h, b.mvalT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.runSt σ s)) :
    Premise.Runs m s (.captureMV x b s') σ :=
  Premise.sound_captureGen σ (inj := some) (Stmt.runSt_declMem σ R x b)
    (MPath.mvalT_revertOnly σ b) hok herr

end CaptureSim

/-! ## A scope end that pops nothing -/

theorem Ext.eq_refl_of {Γ : Ctx} : {Δ : Ctx} → (e : Ext Γ Δ) → (h : Δ = Γ) → h ▸ e = .refl
  | _, .refl, _ => rfl
  | _, .push e, h => by
    have := (Thin.ofExt e).length_le
    have := congrArg List.length h
    simp only [List.length_cons] at this
    omega

/-- A scope end from a context to itself pops nothing. -/
theorem Ext.self_eq_refl {Γ : Ctx} (e : Ext Γ Γ) : e = .refl := Ext.eq_refl_of e rfl

theorem TRes.map_drop_self {Γ : Ctx} (e : Ext Γ Γ) (r : TRes (State C Γ)) :
    r.map (State.drop e) = r := by
  rw [Ext.self_eq_refl e]; cases r <;> rfl

end Solidity
