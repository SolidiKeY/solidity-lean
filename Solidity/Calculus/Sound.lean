import Solidity.Calculus.StmtSound
import Solidity.Calculus.ProvesSound

/-!
# The scoped sequent is sound over the typed state

Every rule the strategy fires is sound (`Stmt.sound`,
`Calculus/StmtSound.lean`), and so is the sequent's structure
(`Proves.sound_of`, `Calculus/ProvesSound.lean`): what `H ⊢ φ` proves holds,
with no hypothesis (`Proves.sound`, `Proves.valid`).
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
theorem Proves.valid {R : RuleSet} {φ : Fml C []} (d : Proves C R [] .nil φ) : Valid φ :=
  Proves.sound d

/-- info: 'Solidity.Proves.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Proves.valid

end Solidity
