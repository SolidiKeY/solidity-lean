import Solidity.Lowering.Readonly.CollectionEffects

/-! Journal-only effects of existing Source reference/conversion helpers.
No ABI value correctness, new accepted type or native provenance is asserted. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem bytesOfRV_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (v : Solidity.Source.RVal E.layout τ),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.bytesOfRV (Γ := Γ) F n v) := by
  intro E Γ τ mode F n v
  unfold Solidity.Source.bytesOfRV
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.heapBytes_effect mode _
  · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact (Solidity.Lowering.Readonly.SourceHistory.load_histories mode F n).1 _ _
    · intro data
      cases data <;> first
      | exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
      | exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _

theorem cdToMem_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (F : Solidity.Source.Fr) (τ : Solidity.Source.STy) (off len : Nat),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.cdToMem (E := E) (Γ := Γ) F τ off len) := by
  intro E Γ mode F τ off len
  unfold Solidity.Source.cdToMem
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  · split
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.allocRef_effect mode _) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.allocRef_effect mode _) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.mapM mode _ (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _) _) (fun _ =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.allocRef_effect mode _) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _))
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _

theorem convRV_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {σ : Solidity.Source.STy} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (τ : Solidity.Source.STy) (v : Solidity.Source.RVal E.layout σ),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.convRV (Γ := Γ) F n τ v) := by
  intro E Γ σ mode F n τ v
  unfold Solidity.Source.convRV
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect mode _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.cdToMem_effect mode F _ _ _)
   | (with_reducible exact (Solidity.Lowering.Readonly.SourceHistory.load_histories mode F n).1 _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem convExplicitRV_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {σ : Solidity.Source.STy} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (τ : Solidity.Source.STy) (v : Solidity.Source.RVal E.layout σ), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.convExplicitRV (Γ := Γ) F n τ v) := by
  intro E Γ σ mode F n τ v
  unfold Solidity.Source.convExplicitRV
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.heapBytes_effect mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect mode F n _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.convRV_effect mode F n _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

end Solidity.Lowering.Readonly.SourceHistory
