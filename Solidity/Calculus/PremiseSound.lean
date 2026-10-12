import Solidity.Calculus.Logic
import Solidity.Calculus.Step

/-!
# A rule is sound: the per-arm interface

What a rule's soundness states (`Premise.Sound`, `Stmt.Sound`), read in the
formulas over the typed run (`holds`, `Calculus/Logic.lean`), and the scope
ends a finished program goes through (`holds_exit`).  Below the sequent
(`Calculus/Proves.lean`), so that the arms' soundness (`Calculus/Sound*.lean`,
`Stmt.sound`) needs nothing of the sequent's rules; the sequent's soundness
is `Calculus/ProvesSound.lean`'s.
-/

namespace Solidity
open Solidity (Modality)

variable {C : Contract}

/-! ## The per-arm interface -/

/-- **A premise is sound** for the statement `s` in the typed state `σ`
under `m`: in front of any rest, frames and postcondition, it gives
`⟨ s; ω κ ⟩ φ` (`Premise.Sound`, over `State`). -/
def Premise.Sound (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
    (σ : State C Γ) : Prop :=
  ∀ {Γ₁ Γ₀ : Ctx} (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀),
    holds σ (p.fml m ω κ φ) → holds σ (.modal m (.cons s ω) κ φ)

/-- **Every rule the strategy fires is sound** over the typed state, in
every typed state, at any fresh index (`Stmt.Sound`, over `State`). -/
def Stmt.Sound (C : Contract) : Prop :=
  ∀ (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ'),
    s.step k m = p → ∀ σ : State C Γ, Premise.Sound m s p σ

/-! ## Scope ends -/

theorem Prog.runFrames_seq {Γ Γ₁ Γ₀ : Ctx} (σ : State C Γ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) : Prog.runFrames σ .nil (.seq ω κ) = Prog.runFrames σ ω κ := by
  simp only [Prog.runFrames, Prog.run_nil, Frames.run, TRun.seq, bind, Except.bind]
  cases Prog.run σ ω with
  | error => rfl
  | ok o =>
    simp only [Except.map]
    cases Frames.run o.st κ <;> rfl

/-- A finished program's frames, as the formula `emptyModality` leaves
(`Frames.exit`), give the modality: each scope end's update is read in the
state the frame pops to, one of the states it lands on. -/
theorem holds_exit (m : Modality) {Γ₀ : Ctx} : {Γ : Ctx} → (κ : Frames C Γ Γ₀) →
    ∀ (φ : Fml C Γ₀) (σ : State C Γ), holds σ (κ.exit m φ) → holds σ (.modal m .nil κ φ)
  | _, .nil, φ, σ, h => ⟨h, nofun⟩
  | _, .seq .nil κ, φ, σ, h => by
    show m.afterRunTR (holds · φ) (Prog.runFrames σ .nil (.seq .nil κ))
    rw [Prog.runFrames_seq]
    exact holds_exit m κ φ σ h
  | _, .seq (.cons s ω) κ, φ, σ, h => by
    show m.afterRunTR (holds · φ) (Prog.runFrames σ .nil (.seq (.cons s ω) κ))
    rw [Prog.runFrames_seq]
    exact h
  | _, .pop _ e κ, φ, σ, h =>
    holds_exit m κ φ (σ.drop e) (Upd.afterT.of_lands h (Upd.lands_pop_nil e σ))
  | _, .drop e κ, φ, σ, h =>
    holds_exit m κ φ (σ.thin e) (Upd.afterT.of_lands h (Upd.lands_drop_nil e σ))

end Solidity
