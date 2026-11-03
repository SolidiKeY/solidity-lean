import Solidity.Lowering.Readonly.ReferenceEffects

/-! Actual mapping-key conversion history, including refused keys and bounded
reference reads. No key/hash correctness or ABI admission is asserted. -/
namespace Solidity.Lowering.Readonly.SourceHistory
theorem keyStep_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (k : Solidity.Source.RVal E.layout τ), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.keyStep (Γ := Γ) F n k) := by
  intro E Γ τ mode F n k
  unfold Solidity.Source.keyStep
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect mode F n _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only
end Solidity.Lowering.Readonly.SourceHistory
