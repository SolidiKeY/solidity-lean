import Solidity.Lowering.Readonly.KeyStepEffects
import Solidity.Lowering.Readonly.LocationEffects
import Solidity.Lowering.Readonly.SourceSequenceEffects

/-! Actual lvalue/call sequencing induction components at the successor bound.
The smaller-bound At premise is retained; no full evaluator closure follows. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem evalLoc_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (l : Solidity.Source.RLVal E Γ τ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.evalLoc G F (n+1) l) := by
  intro E G F n h Γ τ l
  unfold Solidity.Source.evalLoc
  repeat' first
   | (with_reducible exact h.evalE F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexNat_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.indexLoc_effect F.static F _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.keyStep_effect F.static F n _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readLen_effect F.static F _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem pay_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) {Γ : Solidity.Source.RCtx} (a : Solidity.Source.RExpr E Γ (.address true)) (v : Solidity.Source.RExpr E Γ (.int Solidity.Source.IntTy.u256)), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.pay G F (n+1) a v) := by
  intro E G F n h Γ a v
  unfold Solidity.Source.pay
  repeat' first
   | (with_reducible exact h.evalE F _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.parent F.static false _ (h.callAddr F _ _ _ false))
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.sub F.static _ _ ?_
   | split
   | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
