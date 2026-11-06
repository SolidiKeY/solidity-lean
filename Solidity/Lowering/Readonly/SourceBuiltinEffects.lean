import Solidity.Lowering.Readonly.SourceAggregateReadEffects
import Solidity.Lowering.Readonly.SourceLvalueCallEffects

/-! Actual builtin successor history. Argument order, refusals and precompile
result handling remain unchanged; no digest/precompile/native correctness claim. -/
namespace Solidity.Lowering.Readonly.SourceHistory
theorem evalBuiltin_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) {Γ : Solidity.Source.RCtx} {σs : List Solidity.Source.STy} (b : Solidity.Source.Builtin) (args : Solidity.Source.RArgs E Γ σs) (τ : Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalBuiltin G F (n+1) b args τ) := by
  intro E G F n h Γ σs b args τ
  cases b <;> unfold Solidity.Source.evalBuiltin <;> dsimp only
  all_goals repeat' first
   | (with_reducible exact h.evalArgsRev F _)
   | (with_reducible exact h.evalArgs F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F n _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F n _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.ret32_effect F.static _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only
end Solidity.Lowering.Readonly.SourceHistory
