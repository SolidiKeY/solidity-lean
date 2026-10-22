import Solidity.Calculus.Correct
import Solidity.Calculus.StmtSound
import Solidity.Calculus.ProvesSound

/-!
# The scoped sequent is sound over the typed state

Every rule the strategy fires is sound (`Stmt.sound`,
`Calculus/StmtSound.lean`), and so is the sequent's structure
(`Proves.sound_of`, `Calculus/ProvesSound.lean`): what `H ⊢ φ` proves holds,
with no hypothesis (`Proves.sound`, `Proves.fmlValid`).
-/

namespace Solidity

open Solidity (Modality RuleSet)

variable {C : Contract}

/-- **Soundness of the scoped sequent over the typed state**: what `H ⊢ φ`
proves holds, its context in front, in every typed state of the outer
scope. -/
theorem Proves.sound {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ} {φ : Fml C Γ}
    (d : Proves C R Γ₀ H φ) : ∀ σ, holds σ (H.wrap φ) :=
  Proves.sound_of Stmt.sound d

/-- **A goal proved with an empty context is valid over the typed
state.** -/
theorem Proves.fmlValid {R : RuleSet} {φ : Fml C []} (d : Proves C R [] .nil φ) : Fml.Valid φ :=
  Proves.sound d

/-- info: 'Solidity.Proves.fmlValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Proves.fmlValid

/-- A derivation of a translated correctness statement proves its direct
execution meaning. For example, a proof of `[x = 1;] x = 1` says the
program runs without panic and its returned local evaluates to `1`. -/
theorem Proves.valid {R : RuleSet} {φ : Spec C []}
    (d : Proves C R [] .nil φ.toFml) : Spec.Valid φ :=
  (Spec.valid_iff φ).mpr (Proves.fmlValid d)

/-- info: 'Solidity.Proves.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Proves.valid

end Solidity
