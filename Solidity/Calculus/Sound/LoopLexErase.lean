import Solidity.Calculus.SoundKit

/-!
# Erasing a proof annotation preserves execution

An annotation is evidence requested of a verifier, not an executable statement.
Replacing it does not prove that its metric decreases. The tuple erasure step
uses this equality to reach the existing invariant rule; successful termination
has a separate certificate over the actual typed metric tuple.
-/

namespace Solidity

variable {C : Contract} {Γ Γb : Ctx} {m : Modality}

/-- `while (c) body` runs as itself with another annotation, under either
modality. No body, condition, break flag or runtime value is transformed. -/
theorem Premise.sound_loopAnnotation (σ : State C Γ) (a a' : LoopAnn C Γ)
    (c : Val C Γ .bool) (body : Prog C Γ Γb) :
    Premise.Runs m (.loop a c body)
      (.unfold (.cons (.loop a' c body) .nil) .refl) σ := by
  apply Premise.sound_unfold
  rw [Prog.runSt_single, TRes.map_drop_self]
  rfl

end Solidity
