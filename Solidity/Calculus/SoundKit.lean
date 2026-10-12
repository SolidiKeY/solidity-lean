import Solidity.Calculus.Logic
import Solidity.Calculus.NoPanic
import Solidity.Calculus.ProvesSound
import Solidity.Semantics.Ends
import Solidity.Calculus.LowerRun
import Solidity.Semantics.Callback

/-!
# Soundness of a rule: the premise shapes, and the kit

What each kind of premise needs of the statement it replaces, as an equation
between typed runs (`Premise.Runs`, the arms' statement), which gives
`Premise.Sound` (`Calculus/ProvesSound.lean`, `holds`,
`Calculus/Logic.lean`) and the reading with callbacks
(`Calculus/CallbackSound.lean`).  The runs are read at the states they
end in (`Stmt.runSt`, `Prog.runSt`, `Frames.runSt`), so that a block and
the statement it replaces compare as states; a run only grows the heap
typing (`Stmt.runSt_ext`, from `Out.ext`), which an update's reading asks.

An update rule needs that its update computes the global part and the
locals of the state the typed run ends in (`Upd.applyV`), and halts where
the run halts under the diamond (`Premise.sound_update`); the update is a
term of `Update.lean`, so an arm states that the statement's typed step
agrees with what the update computes (`TRes.Agrees`,
`Premise.sound_update_typed`), from the lowered expressions' agreements
(`Calculus/LowerRun.lean`).  Also here: outcomes alike up to the halt
(`Res.Sim`, `TRes.Sim`).
-/

namespace Solidity
open Solidity (Modality Srt NoPanic Op0 Op1 Op2 Op3)
open Semantics (Value Res Halt)
open Solidity (readAddr)

variable {C : Contract}

/-! ## A term never panics -/

section NoPanic

variable {Γ : Ctx}

/-- **A scoped term never panics**: its symbols are `Update.lean`'s. -/
theorem Tm.evalT_noPanic (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → s.NoPanic (t.evalT σ)
  | _, .pvV _ => NoPanic.pure _
  | _, .pvP i => by
    show NoPanic (σ.aliasPathT i)
    unfold State.aliasPathT; split <;> no_panic
  | _, .pvS _ => NoPanic.pure _
  | _, .pvI i => by
    show NoPanic (σ.memRefT i)
    unfold State.memRefT; split <;> no_panic
  | _, .netOf i a => by
    have ha : NoPanic (a.evalT σ) := Tm.evalT_noPanic σ a
    simp only [Tm.evalT, Srt.NoPanic]
    no_panic
  | _, .app0 o => Op0.eval_noPanic σ.globE o
  | _, .app1 o _ a => Op1.eval_noPanic σ.globE o (Tm.evalT_noPanic σ a)
  | _, .app2 o a b => Op2.eval_noPanic σ.globE o (Tm.evalT_noPanic σ a) (Tm.evalT_noPanic σ b)
  | _, .app3 o a b c =>
    Op3.eval_noPanic σ.globE o (Tm.evalT_noPanic σ a) (Tm.evalT_noPanic σ b)
      (Tm.evalT_noPanic σ c)

theorem Rhs.evalT_noPanic (σ : State C Γ) {t : LTy} (r : Rhs C Γ t) : NoPanic (r.evalT σ) := by
  cases r with
  | val t => exact Tm.evalT_noPanic σ t
  | path p => have := Tm.evalT_noPanic σ p; simp only [Rhs.evalT]; no_panic
  | unset => exact NoPanic.pure _
  | mref i => have := Tm.evalT_noPanic σ i; simp only [Rhs.evalT]; no_panic
  | store s => have := Tm.evalT_noPanic σ s; simp only [Rhs.evalT]; no_panic
  | saveNet => exact NoPanic.pure _
  | saveNetMt => exact NoPanic.pure _

theorem UpdElem.globT_noPanic {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ)
    (g : Semantics.State) : NoPanic (e.globT σ₀ g) := by
  have hv : ∀ t : Tm C Γ .val, NoPanic (t.evalT σ₀) := fun t => Tm.evalT_noPanic σ₀ t
  have hs : ∀ t : Tm C Γ .st, NoPanic (t.evalT σ₀) := fun t => Tm.evalT_noPanic σ₀ t
  have hm : ∀ t : Tm C Γ .mem, NoPanic (t.evalT σ₀) := fun t => Tm.evalT_noPanic σ₀ t
  cases e with
  | «local» i r => have := Rhs.evalT_noPanic σ₀ r; simp only [UpdElem.globT]; no_panic
  | _ => simp only [UpdElem.globT]; no_panic

theorem UpdElem.applyV_noPanic {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ)
    (g : Semantics.State) (ℓ : Locs C Δ) : NoPanic (e.applyV σ₀ g ℓ) := by
  cases e with
  | «local» i r =>
    have := Rhs.evalT_noPanic σ₀ r
    simp only [UpdElem.applyV]; no_panic
  | _ =>
    simp only [UpdElem.applyV]
    exact NoPanic.bind (UpdElem.globT_noPanic σ₀ _ g) fun _ _ => NoPanic.pure _

/-- **An update never panics.** -/
theorem Upd.applyV_noPanic (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    NoPanic (U.applyV σ₀)
  | _, .nil => NoPanic.pure _
  | _, .snoc U e =>
    NoPanic.bind (Upd.applyV_noPanic σ₀ U) fun p _ => UpdElem.applyV_noPanic σ₀ e p.1 p.2
  | _, .decl U _ r =>
    NoPanic.bind (Upd.applyV_noPanic σ₀ U) fun _ _ =>
      NoPanic.bind (Rhs.evalT_noPanic σ₀ r) fun _ _ => NoPanic.pure _
  | _, .pop U _ =>
    NoPanic.bind (Upd.applyV_noPanic σ₀ U) fun _ _ => NoPanic.pure _
  | _, .drop U _ =>
    NoPanic.bind (Upd.applyV_noPanic σ₀ U) fun _ _ => NoPanic.pure _

end NoPanic

/-! ## Outcomes a modality cannot tell apart

A rule that captures a part evaluates it first, where the statement may read
another part first (`sp[e]` with `sp` an alias: the alias first, then `e`).
The two runs then halt alike but maybe not with the same halt; a modality
tells a halt only from a panic (`Modality.afterRunTR`), and an expression
never panics (`Tm.eval_noPanic`), so the two are alike (`Res.Sim`, today's
`SameOk` with no fresh names). -/

section Sim

variable {α β : Type}

/-- The same state, or two halts that are both panics or both not. -/
def Res.Sim : Res α → Res α → Prop
  | .ok a, .ok b => a = b
  | .error e, .error e' => (e = .panic ↔ e' = .panic)
  | _, _ => False

theorem Res.Sim.refl (r : Res α) : Res.Sim r r := by
  cases r <;> simp only [Res.Sim]

theorem Res.Sim.of_eq {r r' : Res α} (h : r = r') : Res.Sim r r' := h ▸ Res.Sim.refl r

theorem Res.Sim.bind {r r' : Res α} (h : Res.Sim r r') (f : α → Res β) :
    Res.Sim (r >>= f) (r' >>= f) := by
  cases r with
  | ok a => cases r' with
    | ok b => cases (h : a = b); exact Res.Sim.refl _
    | error => exact h.elim
  | error e => cases r' with
    | ok => exact h.elim
    | error e' => exact h

end Sim

open Solidity (Modality)

/-! ## Runs read at the states they end in -/

section Runs

variable {Γ Γ' Γ₁ Γ₀ : Ctx}

/-- The state a statement's typed run ends in. -/
def Stmt.runSt (σ : State C Γ) (s : Stmt C Γ Γ') : TRes (State C Γ') := (s.run σ).map (·.st)

/-- A statement's typed run only grows the heap typing. -/
theorem Stmt.runSt_ext {σ : State C Γ} {s : Stmt C Γ Γ'} {τ : State C Γ'}
    (h : Stmt.runSt σ s = .ok τ) : σ.H <+: τ.H := by
  unfold Stmt.runSt at h
  cases ho : s.run σ with
  | error => rw [ho] at h; cases h
  | ok o =>
    rw [ho] at h
    cases h
    exact o.ext

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

end Runs

/-! ## Premise shapes -/

section Shapes

variable {Γ Γ' Γ₁ Γ₀ : Ctx} {m : Modality}

/-- An update that halts computed halts in its global part. -/
theorem Upd.globT_error_of_applyV {Δ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ} {e : Halt}
    (h : U.applyV σ₀ = .error e) : ∃ e', U.globT σ₀ = .error e' := by
  cases hg : U.globT σ₀ with
  | error e' => exact ⟨e', rfl⟩
  | ok g =>
    obtain ⟨ℓ, hℓ⟩ := Upd.applyV_of_globT U hg
    rw [hℓ] at h; cases h

/-- **An update**: `{U} ⟨ ω κ ⟩ φ` gives `⟨ s; ω κ ⟩ φ` when `U` computes the
global part and the locals of the state `s` ends in (`Upd.applyV`), and `s`
halts only where `U` does under the diamond (but when it is exhausted, which
both modalities accept), never in a panic. -/
theorem Premise.sound_updateH {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : State C Γ)
    (hs : ∀ τ, Stmt.runSt σ s = .ok τ → U.applyV σ = .ok (τ.globE, τ.loc))
    (hh : ∀ e, Stmt.runSt σ s = .error e →
      e ≠ .panic ∧ (m = .diamond → e ≠ .exhausted → ∃ e', U.applyV σ = .error e')) :
    Premise.Sound m s (.update U) σ := by
  intro _ _ ω κ φ h
  rw [holds_modal_iff, runSt_cons_frames]
  cases hτ : Stmt.runSt σ s with
  | ok τ =>
    have hl : U.Lands σ τ.globE τ := Upd.lands_iff_applyV.2 ⟨τ.loc, hs τ hτ, rfl, fun _ => rfl⟩
    exact (holds_modal_iff τ ω κ φ).1 (holds_modalK τ ω κ φ (h.of_lands hl (Stmt.runSt_ext hτ)))
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
        obtain ⟨e'', hg⟩ := Upd.globT_error_of_applyV he'
        exact (h.of_error hg).elim

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

`Premise.Sound` reads a premise in the formulas.  For the update, a block,
a hidden binder and a split, what the shapes above ask of the statement's
typed run is kept as it is (`Premise.Runs`, any other kind read as
`Premise.Sound`): the arms prove that, it gives `Premise.Sound`
(`Premise.Runs.sound`), and the reading with callbacks too
(`Calculus/CallbackSound.lean`), where the rest of the program is read
over runs that may call back. -/

/-- **What the premise `p` asks of the typed run of `s` from `σ`**, by its
kind. -/
def Premise.Runs (m : Modality) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Premise C Γ Γ' → State C Γ → Prop
  | _, _, s, .update U, σ => (∀ τ, Stmt.runSt σ s = .ok τ → U.applyV σ = .ok (τ.globE, τ.loc)) ∧
      (∀ e, Stmt.runSt σ s = .error e →
        e ≠ .panic ∧ (m = .diamond → e ≠ .exhausted → ∃ e', U.applyV σ = .error e'))
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
    (hs : ∀ τ, Stmt.runSt σ s = .ok τ → U.applyV σ = .ok (τ.globE, τ.loc))
    (hh : ∀ e, Stmt.runSt σ s = .error e →
      e ≠ .panic ∧ (m = .diamond → e ≠ .exhausted → ∃ e', U.applyV σ = .error e')) :
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
    {o : COut C σ.H Γ'} (h : ExecS J σ s o) (hs : s.forks = false) : o = .ofRes (s.run σ) := by
  cases h with
  | det _ => rfl
  | _ => simp_all only [Stmt.forks, Bool.true_eq_false]

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
  · have := ExecP.eq_run hx hP
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

/-- A declaration, then a statement on top of it, its local popped: the
declaration's outcome, then the statement's. -/
theorem runSt_declThen {t : LTy} (σ : State C Γ) (d : Stmt C Γ (t :: Γ))
    (s' : Stmt C (t :: Γ) (t :: Γ)) :
    (Prog.runSt σ (.cons d (.cons s' .nil))).map (State.drop (.push .refl)) =
      (Stmt.runSt σ d).bind fun τ => (Stmt.runSt τ s').map (State.drop (.push .refl)) := by
  rw [Prog.runSt_cons]
  cases Stmt.runSt σ d with
  | error => rfl
  | ok τ =>
    show (Prog.runSt τ (.cons s' .nil)).map _ = _
    rw [Prog.runSt_single]
    rfl

/-- **A value captured**, by what the statement does with the value (`G`):
the statement on top of the local runs as `G`, and the statement is the value
read, then `G`, up to the halt. -/
theorem Premise.sound_captureK {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (G : p.Denote → TRes (State C Γ))
    (hs' : ∀ v, (Stmt.runSt (σ.push (t := .val p) v) s').map (State.drop (.push .refl)) = G v)
    (hs : TRes.Sim ((e.evalT σ).bind G) (Stmt.runSt σ s)) :
    Premise.Runs m s (.capture p x e s') σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [runSt_declThen, Stmt.runSt_declLocal]
  have : ((e.evalT σ).map fun v => σ.push (t := .val p) v).bind
      (fun τ => (Stmt.runSt τ s').map (State.drop (.push .refl))) = (e.evalT σ).bind G := by
    cases e.evalT σ with
    | error => rfl
    | ok v => exact hs' v
  rw [this]; exact hs

/-- **A storage path captured**, by what the statement does with the
reference. -/
theorem Premise.sound_captureSPK {R : RefTy} {x : Var} {b : SPath C Γ (.ref R)}
    {s' : Stmt C (.alias R :: Γ) (.alias R :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (G : SRef C (.ref R) → TRes (State C Γ))
    (hs' : ∀ q, (Stmt.runSt (σ.push (t := .alias R) (some q)) s').map
      (State.drop (.push .refl)) = G q)
    (hs : TRes.Sim ((b.resolveT σ).bind G) (Stmt.runSt σ s)) :
    Premise.Runs m s (.captureSP x b s') σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [runSt_declThen, Stmt.runSt_declStorage]
  have : ((b.resolveT σ).map fun q => σ.push (t := .alias R) (some q)).bind
      (fun τ => (Stmt.runSt τ s').map (State.drop (.push .refl))) = (b.resolveT σ).bind G := by
    cases b.resolveT σ with
    | error => rfl
    | ok q => exact hs' q
  rw [this]; exact hs

/-- **A memory path captured**, by what the statement does with the
object. -/
theorem Premise.sound_captureMVK {R : RefTy} {x : Var} {b : MPath C Γ (.ref R)}
    {s' : Stmt C (.mem R :: Γ) (.mem R :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (G : MVal σ.H (.ref R) → TRes (State C Γ))
    (hs' : ∀ r, (Stmt.runSt (σ.push (t := .mem R) (some r)) s').map
      (State.drop (.push .refl)) = G r)
    (hs : TRes.Sim ((b.mvalT σ).bind G) (Stmt.runSt σ s)) :
    Premise.Runs m s (.captureMV x b s') σ := by
  refine Premise.sound_unfoldSim σ ?_
  rw [runSt_declThen, Stmt.runSt_declMem]
  have : ((b.mvalT σ).map fun r => σ.push (t := .mem R) (some r)).bind
      (fun τ => (Stmt.runSt τ s').map (State.drop (.push .refl))) = (b.mvalT σ).bind G := by
    cases b.mvalT σ with
    | error => rfl
    | ok r => exact hs' r
  rw [this]; exact hs

end ShapesSim

/-! ## An update, against the typed step

An update rule's update is a term of `Update.lean`, computed on the typed
state as a global part and the locals' values (`Upd.applyV`), so what it
needs of the typed run (`Premise.sound_update`) follows from the statement's
typed step agreeing with it (`TRes.Agrees`, the state the step ends in read
so, the same `revert` or `panic`): the update ends where the step ends, up to the
halt, and the typed run does not diverge under the diamond.  A typed `diverge` agrees with any untyped outcome, so under the
diamond the arm shows that it does not happen (no update arm's statement
loops; a push at the bound is exhausted, `TRun.push_nd`, which agrees with
anything too and which both modalities accept). -/

section Bridge

variable {Γ Γ' : Ctx} {m : Modality}

/-- **An update, up to the halt**: an update that ends as what the
statement's typed run agrees with (`X`), up to the halt (`Res.Sim`), is
sound over the typed state, where the typed run does not diverge under the
diamond. -/
theorem Premise.sound_updateSim_agrees {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} (σ : State C Γ)
    {X : Res (Semantics.State × Locs C Γ')}
    (ha : TRes.Agrees (fun o : Out C σ.H Γ' => (o.st.globE, o.st.loc)) (s.run σ) X)
    (hs : Res.Sim (U.applyV σ) X)
    (hd : m = .diamond → (s.run σ).NoDiv) : Premise.Runs m s (.update U) σ := by
  have hU := Upd.applyV_noPanic σ U
  apply Premise.sound_update σ
  · intro τ hτ
    simp only [Stmt.runSt] at hτ
    cases ht : s.run σ with
    | error => rw [ht] at hτ; cases hτ
    | ok o =>
      rw [ht] at hτ ha
      obtain rfl : o.st = τ := Except.ok.inj hτ
      have ha' : X = .ok (o.st.globE, o.st.loc) := ha
      rw [ha'] at hs
      revert hs
      cases U.applyV σ with
      | ok a => intro hs; exact congrArg Except.ok hs
      | error => intro hs; exact hs.elim
  · intro e he
    simp only [Stmt.runSt] at he
    cases ht : s.run σ with
    | ok o => rw [ht] at he; cases he
    | error e' =>
      rw [ht] at he ha
      obtain rfl : e' = e := Except.error.inj he
      cases e' with
      | revert =>
        have ha' : X = .error .revert := ha
        rw [ha'] at hs
        revert hs
        cases U.applyV σ with
        | ok => intro hs; exact hs.elim
        | error e'' => exact fun _ => ⟨nofun, fun _ _ => ⟨e'', rfl⟩⟩
      | panic =>
        have ha' : X = .error .panic := ha
        rw [ha'] at hs
        revert hs hU
        cases U.applyV σ with
        | ok => intro hs _; exact hs.elim
        | error e'' => exact fun hs hU => absurd (congrArg Except.error (hs.2 rfl)) hU
      | diverge => exact ⟨nofun, fun hm _ => absurd ht (hd hm)⟩
      | exhausted => exact ⟨nofun, fun _ hx => absurd rfl hx⟩

/-- **An update, against the typed run, up to the halt**: an update that
ends, up to the halt (`Res.Sim`), as what the statement's typed step agrees
with (`X`). -/
theorem Premise.sound_updateSim_typed {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} {t : TStep C Γ Γ'}
    (σ : State C Γ) {X : Res (Semantics.State × Locs C Γ')}
    (ha : TRes.Agrees (fun o : Out C σ.H Γ' => (o.st.globE, o.st.loc)) (t σ) X)
    (hs : Res.Sim (U.applyV σ) X)
    (hd : m = .diamond → (s.run σ).NoDiv) (ht : s.run σ = t σ := by rfl) :
    Premise.Runs m s (.update U) σ :=
  Premise.sound_updateSim_agrees σ (by rw [ht]; exact ha) hs hd

/-- **An update, against the typed run**: the statement's typed step agrees
with what the update computes. -/
theorem Premise.sound_update_typed {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} {t : TStep C Γ Γ'}
    (σ : State C Γ)
    (ha : TRes.Agrees (fun o : Out C σ.H Γ' => (o.st.globE, o.st.loc)) (t σ) (U.applyV σ))
    (hd : m = .diamond → (s.run σ).NoDiv) (ht : s.run σ = t σ := by rfl) :
    Premise.Runs m s (.update U) σ :=
  Premise.sound_updateSim_typed σ ha (Res.Sim.refl _) hd ht

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
    {t : TStep C Γ Γ} (σ : State C Γ) {X : Res (Semantics.State × Locs C Γ)}
    (ha : TRes.Agrees (fun o : Out C σ.H Γ => (o.st.globE, o.st.loc)) (t σ) X)
    (h : (∀ f ∈ fs, holds σ f) → ∃ U ∈ us, Res.Sim (U.applyV σ) X)
    (hd : m = .diamond → (s.run σ).NoDiv) (ht : s.run σ = t σ := by rfl) :
    Premise.Sound m s (.cases fs us) σ := by
  intro Γ₁ Γ₀ ω κ φ hp
  have hp' := (holds_conj _).1 hp
  obtain ⟨U, hU, hs⟩ := h fun f hf => hp' f (List.mem_append_left _ hf)
  exact (Premise.sound_updateSim_typed σ ha hs hd ht).sound ω κ φ
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

/-- **A value captured**: `T se = nse; s'` gives `s`, `s'` running as `s`
with the value on top, and `s` halting alike where `nse` halts. -/
theorem Premise.sound_captureSim {p : PrimTy} {x : Var} {e : Val C Γ p}
    {s' : Stmt C (.val p :: Γ) (.val p :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hok : ∀ v, e.evalT σ = .ok v →
      (Stmt.runSt (σ.push (t := .val p) v) s').map (State.drop (.push .refl)) = Stmt.runSt σ s)
    (herr : ∀ h, e.evalT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.runSt σ s)) :
    Premise.Runs m s (.capture p x e s') σ := by
  refine Premise.sound_captureK σ
    (fun v => (Stmt.runSt (σ.push (t := .val p) v) s').map (State.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases he : e.evalT σ with
  | ok v => exact TRes.Sim.of_eq (hok v he)
  | error h => exact herr h he (Val.evalT_revert σ e he)

/-- **A storage path captured**: `T storage sp = nsp; s'`. -/
theorem Premise.sound_captureSPSim {R : RefTy} {x : Var} {b : SPath C Γ (.ref R)}
    {s' : Stmt C (.alias R :: Γ) (.alias R :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hok : ∀ q, b.resolveT σ = .ok q →
      (Stmt.runSt (σ.push (t := .alias R) (some q)) s').map (State.drop (.push .refl)) =
        Stmt.runSt σ s)
    (herr : ∀ h, b.resolveT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.runSt σ s)) :
    Premise.Runs m s (.captureSP x b s') σ := by
  refine Premise.sound_captureSPK σ
    (fun q => (Stmt.runSt (σ.push (t := .alias R) (some q)) s').map (State.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases hb : b.resolveT σ with
  | ok q => exact TRes.Sim.of_eq (hok q hb)
  | error h => exact herr h hb (SPath.resolveT_revert σ b hb)

/-- **A memory path captured**: `T memory mv = nmp; s'`. -/
theorem Premise.sound_captureMVSim {R : RefTy} {x : Var} {b : MPath C Γ (.ref R)}
    {s' : Stmt C (.mem R :: Γ) (.mem R :: Γ)} {s : Stmt C Γ Γ} (σ : State C Γ)
    (hok : ∀ r, b.mvalT σ = .ok r →
      (Stmt.runSt (σ.push (t := .mem R) (some r)) s').map (State.drop (.push .refl)) =
        Stmt.runSt σ s)
    (herr : ∀ h, b.mvalT σ = .error h → h = .revert → TRes.Sim (.error h) (Stmt.runSt σ s)) :
    Premise.Runs m s (.captureMV x b s') σ := by
  refine Premise.sound_captureMVK σ
    (fun r => (Stmt.runSt (σ.push (t := .mem R) (some r)) s').map
      (State.drop (.push .refl)))
    (fun _ => rfl) ?_
  cases hb : b.mvalT σ with
  | ok r => exact TRes.Sim.of_eq (hok r hb)
  | error h => exact herr h hb (MPath.mvalT_revert σ b hb)

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

theorem TRes.map_drop_self {Γ : Ctx} (e : Ext Γ Γ) (r : TRes (State C Γ)) :
    r.map (State.drop e) = r := by
  rw [Ext.self_eq_refl e]; cases r <;> rfl

end Solidity
