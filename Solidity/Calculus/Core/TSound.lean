import Solidity.Calculus.Core.TSoundStep
import Solidity.Calculus.Core.TSoundCalls
import Solidity.Calculus.Core.TSoundLoops

/-!
# Every rule of `Stmt.step` over the typed state

The arms (`Stmt.tstepSound_arms`, `Calculus/Core/TSoundStep.lean`) and the
blocks' (`Stmt.tsound_call`, `Stmt.tsound_tryCall`, `Stmt.tsound_loop`),
assembled: `Stmt.tsound`, every rule sound in every typed state, so the
sequent is sound over the typed state with no hypothesis
(`Proves.tsound`, `Proves.tvalid`).

Decisions 15 and 16 took two conditions away (a push at the bound is
exhausted, which both modalities accept; no struct repeats a member name),
and 17' the last (`docs/intrinsic.md`, "Decision 17', implemented"): a
memory local may be unset, so `T memory mv = r;`'s premise
`∀ mv. [mv = r; ω] φ` holds at `mv` unset, from which `mv = r;` runs as the
declaration does, where before no typed value of `mv` named the object `r`
was about to allocate.
-/

namespace Solidity.Core

open Solidity (Modality RuleSet)

variable {C : Contract}

/-- **Every rule of `Stmt.step` is sound over the typed state.** -/
theorem Stmt.tstepSound (k : Nat) (m : Modality) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') :
    Stmt.TStepSound k m s := by
  intro σ p hp
  cases s with
  | call f args ret body => exact Stmt.tsound_call k m f args ret body σ p hp
  | tryCall call rets ok err code pnc other =>
    exact Stmt.tsound_tryCall k m call rets ok err code pnc other σ p hp
  | loop a c body => exact Stmt.tsound_loop k m a c body σ p hp
  | _ => exact Stmt.tstepSound_arms k m _ rfl σ p hp

/-- **Every rule the strategy fires is sound over the typed state**, in
every typed state, at every contract. -/
theorem Stmt.tsound (C : Contract) : Stmt.TSound C :=
  fun k m _ _ s p hp σ => Stmt.tstepSound k m s σ p hp

/-- **Soundness of the scoped sequent over the typed state**: what `H ⊢ φ`
proves holds, its context in front, in every typed state of the outer
scope. -/
theorem Proves.tsound {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (d : Proves C R Γ₀ H φ) : ∀ σ, tholds σ (H.wrap φ) :=
  Proves.tsound_of (Stmt.tsound C) d

/-- **A goal proved with an empty context is valid over the typed
state.** -/
theorem Proves.tvalid {R : RuleSet} {φ : Fml C []} (d : Proves C R [] .nil φ) : TValid φ :=
  Proves.tsound d

/-- info: 'Solidity.Core.Stmt.tsound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Stmt.tsound

/-- info: 'Solidity.Core.Proves.tvalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Proves.tvalid

end Solidity.Core
