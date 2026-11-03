import Solidity.Lowering.Readonly.EvalEffectsBase

/-! Actual lookup/event/mark/outcome effects. No unconditional rollback rule,
whole-state equality or native-call provenance is asserted. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem instanceAt_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (G : Solidity.Source.Glob E) (a : Solidity.Roadmap.Address),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.instanceAt (Γ := Γ) G a) := by
  intro E Γ mode G a
  unfold Solidity.Source.instanceAt
  apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.st mode
  · intro state
    split <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _

theorem emitEvent_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (event : Solidity.Roadmap.Event),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.emitEvent (E := E) (Γ := Γ) event) := by
  intro E Γ mode event; exact Solidity.Lowering.Readonly.SourceHistory.Effect.modSt mode _ (fun _ => rfl)

theorem mark_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.mark (E := E) (Γ := Γ)) := by
  intro E Γ mode; unfold Solidity.Source.mark; exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.st mode) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)

theorem reraise_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (out : Solidity.Roadmap.Outcome),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.reraise (E := E) (Γ := Γ) out) := by
  intro E Γ mode out; cases out; exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _; exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _

end Solidity.Lowering.Readonly.SourceHistory
