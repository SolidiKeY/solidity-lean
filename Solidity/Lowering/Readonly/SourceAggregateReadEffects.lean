import Solidity.Lowering.Readonly.SourcePayloadDecodeEffects

/-! Journal effects of existing aggregate/read-only helpers. No successful
value construction, getter coverage, digest or ABI correctness is asserted. -/
namespace Solidity.Lowering.Readonly.SourceHistory
theorem ret32_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (τ : Solidity.Source.STy) (bs : Solidity.Roadmap.Bytes), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.ret32 (E := E) (Γ := Γ) τ bs) := by
  intro E Γ mode τ bs
  unfold Solidity.Source.ret32
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
theorem fieldsOf_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {D : Solidity.Source.Layout} (mode : Bool) {ps : List Solidity.Source.STy} (vs : Solidity.Source.Vals D ps) (τs : List Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.fieldsOf (E := E) (Γ := Γ) vs τs) := by
  intro E Γ D mode ps
  induction ps with
  | nil =>
    intro vs τs
    cases vs
    cases τs
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
  | cons σ ps ih =>
    intro vs τs
    cases vs with
    | cons v vs =>
      cases τs with
      | nil => exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
      | cons τ τs =>
        unfold Solidity.Source.fieldsOf
        split
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (ih vs τs) (fun fields => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _

theorem getterPath_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (data : Solidity.Roadmap.Bytes) (τ : Solidity.Source.STy) (p : Solidity.Source.SPath) (i : Nat), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.getterPath (E := E) (Γ := Γ) F n data τ p i) := by
  intro E Γ mode F n data τ
  generalize size : sizeOf τ = count
  induction count using Nat.strongRecOn generalizing τ with
  | ind count ih =>
    intro p i
    cases τ
    case mapping key value =>
      have smaller : sizeOf value < count := by
        simp only [Solidity.Source.STy.mapping.sizeOf_spec] at size
        omega
      unfold Solidity.Source.getterPath
      exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _) (fun key =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.keyStep_effect mode F n _) (fun step =>
          ih (sizeOf value) smaller value rfl _ _))
    case array l elem len =>
      have smaller : sizeOf elem < count := by
        simp only [Solidity.Source.STy.array.sizeOf_spec] at size
        omega
      unfold Solidity.Source.getterPath
      cases len with
      | none =>
        exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.readLen_effect mode F _) (fun length => by
          dsimp only
          split
          · exact ih (sizeOf elem) smaller elem rfl _ _
          · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
      | some len =>
        exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _) (fun length => by
          dsimp only
          split
          · exact ih (sizeOf elem) smaller elem rfl _ _
          · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
    all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _

end Solidity.Lowering.Readonly.SourceHistory
