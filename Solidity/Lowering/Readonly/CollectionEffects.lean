import Solidity.Lowering.Readonly.EvalEffectsBase

/-! Actual Source monadic collection and lifted-result effects, including
partial failure state. This does not validate ABI values or input admission. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem Effect.map : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {α β : Type} (mode : Bool) (f : α → β) (m : Solidity.Source.EM E Γ α),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode m → Solidity.Lowering.Readonly.SourceHistory.Effect mode (f <$> m) := by
  intro E Γ α β mode f m h
  intro locals state
  change Solidity.Lowering.Readonly.StaticJournal.History state.ex mode
    ((m >>= fun x => (Pure.pure (f x) : Solidity.Source.EM E Γ β)).run (locals, state)).2.2.ex
  exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind mode m _ h (fun x => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _) locals state

theorem Effect.mapM : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {α β : Type} (mode : Bool) (f : α → Solidity.Source.EM E Γ β),
 (∀ x, Solidity.Lowering.Readonly.SourceHistory.Effect mode (f x)) → ∀ xs, Solidity.Lowering.Readonly.SourceHistory.Effect mode (List.mapM f xs) := by
  intro E Γ α β mode f hf xs
  suffices h : ∀ acc, Solidity.Lowering.Readonly.SourceHistory.Effect mode (List.mapM.loop f xs acc) from h []
  induction xs with
  | nil => intro acc; exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  | cons x xs ih =>
    intro acc
    exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (hf x) (fun y => ih (y :: acc))

theorem getV_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (mode : Bool) (v : Solidity.Source.RVal E.layout τ),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.getV (Γ := Γ) v) := by
  intro E Γ τ mode v; exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _

theorem indexNat_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (mode : Bool) (v : Solidity.Source.RVal E.layout τ),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.indexNat (Γ := Γ) v) := by
  intro E Γ τ mode v; exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _

end Solidity.Lowering.Readonly.SourceHistory
