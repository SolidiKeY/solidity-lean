import Solidity.Lowering.Readonly.EvalEffectsBase

/-! Closed effects of actual Source value-list and inner-local initialization.
Caller EM locals and returned function locals remain separately indexed. Empty
work preserves its actual success behavior even when initialization bound is zero. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source

theorem zeroVals_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (n : Nat) (τs : List Solidity.Source.STy),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.zeroVals (E := E) (Γ := Γ) n τs) := by
  intro E Γ mode n τs
  induction τs with
  | nil => exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  | cons τ τs ih =>
      exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ((Solidity.Lowering.Readonly.SourceHistory.zero_histories mode n).2.1 τ)
        (fun x => Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ih (fun xs => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _))

theorem zeroInner_effect : ∀ {E : Solidity.Source.Env} {Γ' : Solidity.Source.RCtx} (mode : Bool) (n k : Nat) {Γ : Solidity.Source.RCtx} (locals : Solidity.Source.Locals E.layout Γ),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.zeroInner (Γ' := Γ') n k locals) := by
  intro E Γouter mode n k
  induction k with
  | zero => intro Γ locals; exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  | succ k ih =>
    intro Γ locals
    cases locals
    case nil => exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
    case cons =>
      exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ((Solidity.Lowering.Readonly.SourceHistory.zero_histories mode n).2.1 _)
        (fun x => Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (ih _) (fun xs => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _))

end Solidity.Lowering.Readonly.SourceHistory
