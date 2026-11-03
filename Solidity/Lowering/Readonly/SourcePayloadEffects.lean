import Solidity.Lowering.Readonly.CallSupportEffects
import Solidity.Lowering.Readonly.KeyStepEffects

/-! Journal effects of the EXISTING Source payload helpers, including allocation
and every refusal. No ABI value/encoding/decoding correctness, added supported
type, profile admission, or target/native correspondence is asserted. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem tailBytes_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (data : Solidity.Roadmap.Bytes) (i : Nat), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.tailBytes (E := E) (Γ := Γ) data i) := by
  intro E Γ mode data i
  unfold Solidity.Source.tailBytes
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
   | split
   | dsimp only

theorem encodeOne_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (packed : Bool) {τ : Solidity.Source.STy} (v : Solidity.Source.RVal E.layout τ), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.encodeOne (Γ := Γ) F n packed v) := by
  intro E Γ mode F n packed τ v
  unfold Solidity.Source.encodeOne
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect mode F n _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem encodeParts_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (packed : Bool) {τs : List Solidity.Source.STy} (vs : Solidity.Source.RVals E.layout τs), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.encodeParts (Γ := Γ) F n packed vs) := by
  intro E Γ mode F n packed τs
  induction τs with
  | nil =>
    intro vs
    cases vs
    exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  | cons τ τs ih =>
    intro vs
    cases vs with
    | cons v vs =>
      exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.encodeOne_effect mode F n packed v) (fun part =>
        Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (ih vs) (fun parts => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _))

theorem encodeVals_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (F : Solidity.Source.Fr) (n : Nat) (packed : Bool) {τs : List Solidity.Source.STy} (vs : Solidity.Source.RVals E.layout τs), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.encodeVals (Γ := Γ) F n packed vs) := by
  intro E Γ mode F n packed τs vs
  unfold Solidity.Source.encodeVals
  apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
  · exact Solidity.Lowering.Readonly.SourceHistory.encodeParts_effect mode F n packed vs
  · intro parts
    split <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _

end Solidity.Lowering.Readonly.SourceHistory
