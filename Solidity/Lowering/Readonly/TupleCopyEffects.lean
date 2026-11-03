import Solidity.Lowering.Readonly.ReferenceEffects

/-! Effects of the existing typed tuple-pushing and storage-copy helpers.
Caller/returned local contexts remain separate; no value-copy correctness or
ABI/layout admission follows from these journal effects. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem pushVals_effect : ∀ {E : Solidity.Source.Env} {Γ' : Solidity.Source.RCtx} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (slots : List (Option Solidity.Source.STy)) {σs : List Solidity.Source.STy} (vs : Solidity.Source.RVals E.layout σs) {Γ : Solidity.Source.RCtx} (locals : Solidity.Source.Locals E.layout Γ), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.pushVals (Γ' := Γ') F n slots vs locals) := by
  intro E Γ' mode F n slots
  induction slots with
  | nil =>
    intro σs vs Γ locals
    cases vs
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
  | cons slot slots ih =>
    intro σs vs Γ locals
    cases vs with
    | nil => cases slot <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
    | cons v vs =>
      cases slot with
      | none => exact ih vs locals
      | some τ =>
        exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.convRV_effect mode F n τ v) (fun converted =>
          Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.getV_effect mode converted) (fun x => ih vs (.cons x locals)))

theorem copyInto_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (F : Solidity.Source.Fr) (n : Nat) (τ : Solidity.Source.STy) (p : Solidity.Source.SPath) {σ : Solidity.Source.STy} (v : Solidity.Source.RVal E.layout σ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.copyInto (Γ := Γ) F n τ p v) := by
  intro E Γ F n τ p σ v
  unfold Solidity.Source.copyInto
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact (Solidity.Lowering.Readonly.SourceHistory.store_histories F n).1 _ _ _)
   | (with_reducible exact (Solidity.Lowering.Readonly.SourceHistory.store_histories F n).2.1 _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.cdToMem_effect F.static F _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
