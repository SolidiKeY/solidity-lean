import Solidity.Calculus.SoundStep
import Solidity.Calculus.SoundCalls
import Solidity.Calculus.SoundLoops

/-!
# Every rule of `Stmt.step` over the typed state

The arms (`Stmt.stepSound_arms`, `Calculus/SoundStep.lean`) and the
blocks' (`Stmt.sound_call`, `Stmt.sound_tryCall`, `Stmt.sound_loop`),
assembled: `Stmt.sound`, every rule sound in every typed state, with no
hypothesis.  The sequent's soundness (`Proves.sound`, `Proves.valid`) is
`Calculus/Sound.lean`'s, which adds the sequent's own rules.

Decisions 15 and 16 took two conditions away (a push at the bound is
exhausted, which both modalities accept; no struct repeats a member name),
and 17' the last (`docs/intrinsic.md`, "Decision 17', implemented"): a
memory local may be unset, so `T memory mv = r;`'s premise
`∀ mv. [mv = r; ω] φ` holds at `mv` unset, from which `mv = r;` runs as the
declaration does, where before no typed value of `mv` named the object `r`
was about to allocate.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-- **Every rule of `Stmt.step` is sound over the typed state.** -/
theorem Stmt.stepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    Stmt.StepSound k m s := by
  intro σ p hp
  cases s with
  | call f args ret body => exact Stmt.sound_call k m f args ret body σ p hp
  | tryCall call rets ok err code pnc other =>
    exact Stmt.sound_tryCall k m call rets ok err code pnc other σ p hp
  | loop a c body => exact Stmt.sound_loop k m a c body σ p hp
  | _ => exact Stmt.stepSound_arms k m _ rfl σ p hp

/-- **Every rule the strategy fires is sound over the typed state**, in
every typed state, at every contract. -/
theorem Stmt.sound : Stmt.Sound C :=
  fun k m _ _ s p hp σ => (Stmt.stepSound k m s σ p hp).sound

/-- **Every rule the strategy fires asks of the typed run what its premise
says** (`Premise.Runs`): the arms' statement, which the reading with
callbacks reads (`Calculus/CallbackSound.lean`). -/
theorem Stmt.runs (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (p : Premise C Γ Γ')
    (hp : s.step k m = p) (σ : State C Γ) : Premise.Runs m s p σ :=
  Stmt.stepSound k m s σ p hp

/-- info: 'Solidity.Stmt.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Stmt.sound

end Solidity
