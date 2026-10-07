import Solidity.Calculus.Core.Logic
import Solidity.Calculus.NoPanic

/-!
# Soundness of a rule on scoped statements: the statement, and its kit

What it means for one arm of `Stmt.step` (`Calculus/Core/Step.lean`) to be
sound against M3's interpreter (`Core.Stmt.run`), stated once here so that
every arm, `Calculus/Core/SoundArms.lean`'s and the call, `try` and loop
arms of `Calculus/Core/Blocks.lean`, proves the same shape
(`docs/intrinsic.md`, M6a):

* `Premise.Sound m s p σ`: in the state `σ`, the premise `p` put in front of
  any rest `ω`, frames `κ` and postcondition `φ` (`Premise.fml`) gives
  `⟨ s; ω κ ⟩ φ`;
* `Stmt.StepSound k m s`: whatever premise `s.step k m` gives is sound in
  every state whose locals are typed (`State.Typed`).

`State.Typed` is the one typing fact a rule needs that M3's untyped values
do not give: a `bool` local holds a `bool`, so a split on a simple condition
has one of its two goals (the cover goal today's split proves).  M4a's
typed values make it true of every state.

The kit: a scoped term never panics (`Tm.eval_noPanic`, from
`Calculus/NoPanic.lean`'s symbols), so neither does an update
(`Upd.apply_noPanic`), and an update rule needs only that its update ends as
the statement does (`Premise.Sound.update`).
-/

namespace Solidity.Core

open Solidity (Modality Srt NoPanic Op0 Op1 Op2 Op3)
open Semantics (Value Res Halt)

variable {C : Contract}

/-! ## The statement -/

/-- A `bool` local holds a `bool` (M4a's typed values make it true of every
state). -/
def State.Typed {Γ : Ctx} (σ : State C Γ) : Prop :=
  ∀ i : Idx Γ (.val .bool), ∃ b : Bool, (Env.get i σ.env : Value) = .bool b

/-- **A premise is sound** for the statement `s` in `σ` under `m`: in front of
any rest, frames and postcondition, it gives `⟨ s; ω κ ⟩ φ`. -/
def Premise.Sound (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
    (σ : State C Γ) : Prop :=
  ∀ {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀),
    holds σ (p.fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ)

/-- **The rule of `s` is sound**: the premise `Stmt.step` gives, fresh names
at `k`, is sound in every typed state.  Each arm proves this of its
statements. -/
def Stmt.StepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : Prop :=
  ∀ σ : State C Γ, σ.Typed → ∀ p, s.step k m = some p → Premise.Sound m s p σ

/-- An arm that gives the premise `p` is sound when `p` is. -/
theorem Stmt.StepSound.of_eq {k : Nat} {m : Modality} {Γ Γ' : Ctx} {s : Stmt C Γ Γ'}
    {p : Premise C Γ Γ'} (hs : s.step k m = some p)
    (h : ∀ σ : State C Γ, σ.Typed → Premise.Sound m s p σ) : Stmt.StepSound k m s := by
  intro σ hσ p' hp'
  rw [hs] at hp'
  cases hp'
  exact h σ hσ

/-! ## A term never panics -/

section NoPanic

variable {Γ : Ctx}

/-- **A scoped term never panics**: its symbols are `Update.lean`'s. -/
theorem Tm.eval_noPanic (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → s.NoPanic (t.eval σ)
  | _, .pvV _ => NoPanic.pure _
  | _, .pvP i => by
    show NoPanic (aliasPath σ i)
    unfold aliasPath; split <;> no_panic
  | _, .pvS _ => NoPanic.pure _
  | _, .pvI _ => NoPanic.pure _
  | _, .netOf i a => by
    have ha : NoPanic (a.eval σ) := Tm.eval_noPanic σ a
    simp only [Tm.eval, Srt.NoPanic]
    no_panic
  | _, .app0 o => Op0.eval_noPanic σ.glob o
  | _, .app1 o _ a => Op1.eval_noPanic σ.glob o (Tm.eval_noPanic σ a)
  | _, .app2 o a b => Op2.eval_noPanic σ.glob o (Tm.eval_noPanic σ a) (Tm.eval_noPanic σ b)
  | _, .app3 o a b c =>
    Op3.eval_noPanic σ.glob o (Tm.eval_noPanic σ a) (Tm.eval_noPanic σ b) (Tm.eval_noPanic σ c)

theorem Rhs.eval_noPanic (σ : State C Γ) {t : LTy} (r : Rhs C Γ t) : NoPanic (r.eval σ) := by
  cases r with
  | val t => exact Tm.eval_noPanic σ t
  | path p => have := Tm.eval_noPanic σ p; simp only [Rhs.eval]; no_panic
  | unset => exact NoPanic.pure _
  | mref i => exact Tm.eval_noPanic σ i
  | store s => have := Tm.eval_noPanic σ s; simp only [Rhs.eval]; no_panic
  | saveNet => exact NoPanic.pure _
  | saveNetMt => exact NoPanic.pure _

theorem UpdElem.write_noPanic {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ) (τ : State C Δ) :
    NoPanic (e.write σ₀ τ) := by
  have hv : ∀ t : Tm C Γ .val, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hs : ∀ t : Tm C Γ .st, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  have hm : ∀ t : Tm C Γ .mem, NoPanic (t.eval σ₀) := fun t => Tm.eval_noPanic σ₀ t
  cases e with
  | «local» i r => have := Rhs.eval_noPanic σ₀ r; simp only [UpdElem.write]; no_panic
  | _ => simp only [UpdElem.write]; no_panic

/-- **An update never panics.** -/
theorem Upd.apply_noPanic (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) → NoPanic (U.apply σ₀)
  | _, .nil => NoPanic.pure _
  | _, .snoc U e =>
    NoPanic.bind (Upd.apply_noPanic σ₀ U) fun τ _ => UpdElem.write_noPanic σ₀ e τ
  | _, .decl U _ r =>
    NoPanic.bind (Upd.apply_noPanic σ₀ U) fun _ _ =>
      NoPanic.bind (Rhs.eval_noPanic σ₀ r) fun _ _ => NoPanic.pure _
  | _, .pop U h => by
    show NoPanic (State.drop h <$> U.apply σ₀)
    rw [NoPanic.map]; exact Upd.apply_noPanic σ₀ U
  | _, .drop U h => by
    show NoPanic (State.thin h <$> U.apply σ₀)
    rw [NoPanic.map]; exact Upd.apply_noPanic σ₀ U

end NoPanic

/-! ## The premise shapes, as `Premise.Sound` -/

section Shapes

variable {Γ Γ' : Ctx} {m : Modality}

/-- **An update** is sound when it ends as the statement does. -/
theorem Premise.Sound.update {U : Upd C Γ Γ'} {s : Stmt C Γ Γ'} {σ : State C Γ}
    (hs : U.apply σ = s.run σ) : Premise.Sound m s (.update U) σ :=
  fun ω κ φ => Premise.sound_update σ hs (hs ▸ Upd.apply_noPanic σ U) ω κ φ

/-- **A block** is sound when it runs as the statement, its fresh locals
popped. -/
theorem Premise.Sound.unfold {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Ext Γ' Γ''} {s : Stmt C Γ Γ'}
    {σ : State C Γ} (hs : (Prog.run σ P).map (State.drop h) = s.run σ) :
    Premise.Sound m s (.unfold P h) σ :=
  fun ω κ φ => Premise.sound_unfold σ hs ω κ φ

/-- **A block dropping a frame** from under what it keeps. -/
theorem Premise.Sound.inline {Γ'' : Ctx} {P : Prog C Γ Γ''} {h : Thin Γ' Γ''} {s : Stmt C Γ Γ'}
    {σ : State C Γ} (hs : (Prog.run σ P).map (State.thin h) = s.run σ) :
    Premise.Sound m s (.inline P h) σ :=
  fun ω κ φ => Premise.sound_inline σ hs ω κ φ

/-- **A hidden binder** is sound when, for some value of the local, the
block runs as the statement. -/
theorem Premise.Sound.bind {x : Var} {t : LTy} {P : Prog C (t :: Γ) Γ'} {s : Stmt C Γ Γ'}
    {σ : State C Γ} (hs : ∃ v, Prog.run (σ.push v) P = s.run σ) :
    Premise.Sound m s (.bind x t P) σ :=
  fun ω κ φ => Premise.sound_bind σ hs ω κ φ

end Shapes

end Solidity.Core
