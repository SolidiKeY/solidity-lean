import Solidity.Correctness.Panic.Provenance.Updates
import Solidity.Examples.Panic.ProvenanceEval
import Solidity.Semantics.Panic.Run.UpdateProofs

/-!
# Checks: update leaves of panic code provenance

Failing update steps whose solc code is read off the retained failed site
through the leaves of `Correctness/Panic/Provenance/Updates.lean`.
-/

namespace Solidity.Examples.Panic.ProvenanceUpdates
open Solidity.Panic Solidity.Semantics.Panic Solidity.Correctness.Panic
open Solidity.Examples.Panic.ProvenanceEval

variable {C : Contract} {Γ : Ctx}

/-- `x += 1` on a local holding `type(uint256).max` retains the arithmetic
site, hence code 0x11. -/
example (σ : State C Γ) (i : Idx Γ (.val .uint)) (max : TEnv.get i σ.env = maxU) :
    code? (Run.opAssign .add rfl (.local i) (.simple (.lit 1 (by decide))) σ) = some 0x11 := by
  rw [code_of_site (Run.opAssign_coded .add rfl (.local i) _ σ)]
  have : site? (Run.opAssign .add rfl (.local i) (.simple (.lit 1 (by decide))) σ) =
      some .arithmetic := by
    simp only [Run.opAssign, opLocStore, compound, max]
    have hv : value σ (.simple (.lit 1 (by decide))) = .ok one := rfl
    simp only [hv, bind, Except.bind]
    have hb : site? (binary .add rfl maxU one) = some .arithmetic := by decide +kernel
    have he : evalProducer (.binary .add .uint rfl maxU one) = binary .add rfl maxU one := rfl
    rw [he]
    generalize binary .add rfl maxU one = r at hb ⊢
    cases r with
    | ok => cases hb
    | error h => cases h <;> exact hb
  rw [this]
  rfl

/-- `values.pop()` on an empty array retains the empty-pop site, hence code 0x31. -/
example {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ)
    (ref : SRef C (.ref (.array E))) (hr : path σ b = .ok ref)
    (empty : Solidity.Panic.Origin (.pop σ.storage E.isMapping ref) .emptyPop) :
    code? (Run.pop b σ) = some 0x31 := by
  rw [code_of_site (Run.pop_coded b σ)]
  have : site? (Run.pop b σ) = some .emptyPop := by
    rw [Run.pop_origin b σ ref hr empty]
    exact congrArg some (Raised.ofOrigin_site _ _ _)
  rw [this]
  rfl

end Solidity.Examples.Panic.ProvenanceUpdates
