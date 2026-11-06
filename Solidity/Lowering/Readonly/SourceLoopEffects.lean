import Solidity.Lowering.Readonly.SourceBodyEffects

/-! Actual loop successor journal effect, preserving all exits and the smaller-bound premise. -/
namespace Solidity.Lowering.Readonly.SourceHistory
theorem forIter_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (nps : Nat) (ph : Option (Solidity.Source.Ph E)) {R : List Solidity.Source.STy} {M u : Bool} {Γ₁ Γ₂ : Solidity.Source.RCtx} (c : Solidity.Source.ROptBool E Γ₁) (post : Solidity.Source.ROptExpr E Γ₁) (body : Solidity.Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂) (l : Solidity.Source.Locals E.layout Γ₁), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.forIter G F (n+1) nps ph c post body l) := by
  intro E G F n h nps ph R M u Γ₁ Γ₂ c post body l
  cases c <;> unfold Solidity.Source.forIter <;> dsimp only
  all_goals repeat' first
   | (with_reducible exact h.forIter F _ _ _ _ _ _)
   | (with_reducible exact h.execS F _ _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible apply Solidity.Lowering.Readonly.SourceHistory.Effect.sub; exact h.evalE F _)
   | (refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_))
   | (cases post <;> dsimp only)
   | split
   | dsimp only
end Solidity.Lowering.Readonly.SourceHistory
