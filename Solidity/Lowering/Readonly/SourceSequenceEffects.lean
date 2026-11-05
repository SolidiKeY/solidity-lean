import Solidity.Lowering.Readonly.ReferenceEffects
import Solidity.Lowering.Readonly.SourceHistoryBase

/-! Actual sequencing induction steps. Every premise concerns the smaller
bound of the same Source global, frame, mode and computations. These four
components do not construct the full seventeen-component positive-bound At. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem evalPair_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) {Γ : Solidity.Source.RCtx} {σ τ : Solidity.Source.STy} (a : Solidity.Source.RExpr E Γ σ) (b : Solidity.Source.RExpr E Γ τ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalPair G F (n+1) a b) := by
  intro E G F n h
  intros
  unfold Solidity.Source.evalPair
  repeat' first
   | (with_reducible exact h.evalE F _)
   | (with_reducible exact h.evalArgs F _)
   | (with_reducible exact h.evalConvArgs F _)
   | (with_reducible exact h.evalArgsRev F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F n _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem evalArgs_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) {Γ : Solidity.Source.RCtx} {τs : List Solidity.Source.STy} (es : Solidity.Source.RArgs E Γ τs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalArgs G F (n+1) es) := by
  intro E G F n h
  intros
  unfold Solidity.Source.evalArgs
  repeat' first
   | (with_reducible exact h.evalE F _)
   | (with_reducible exact h.evalArgs F _)
   | (with_reducible exact h.evalConvArgs F _)
   | (with_reducible exact h.evalArgsRev F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F n _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem evalConvArgs_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) {Γ : Solidity.Source.RCtx} {τs : List Solidity.Source.STy} (es : Solidity.Source.RConvArgs E Γ τs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalConvArgs G F (n+1) es) := by
  intro E G F n h
  intros
  unfold Solidity.Source.evalConvArgs
  repeat' first
   | (with_reducible exact h.evalE F _)
   | (with_reducible exact h.evalArgs F _)
   | (with_reducible exact h.evalConvArgs F _)
   | (with_reducible exact h.evalArgsRev F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F n _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem evalArgsRev_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) {Γ : Solidity.Source.RCtx} {τs : List Solidity.Source.STy} (es : Solidity.Source.RArgs E Γ τs), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalArgsRev G F (n+1) es) := by
  intro E G F n h
  intros
  unfold Solidity.Source.evalArgsRev
  repeat' first
   | (with_reducible exact h.evalE F _)
   | (with_reducible exact h.evalArgs F _)
   | (with_reducible exact h.evalConvArgs F _)
   | (with_reducible exact h.evalArgsRev F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect F.static F n _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
