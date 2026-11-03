import Solidity.Lowering.Readonly.SourcePayloadEffects

/-! Constructor cuts for journal effects of existing Source payload decoding.
These do not prove ABI correctness, admission or newly supported types. -/
namespace Solidity.Lowering.Readonly.SourceHistory

theorem decodeArg_bytes_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (data : Solidity.Roadmap.Bytes) (i : Nat) (l : Solidity.Source.DataLoc), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.decodeArg (E := E) (Γ := Γ) data i (.bytes l)) := by
  intro E Γ mode data i l
  cases l <;> unfold Solidity.Source.decodeArg
  all_goals repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.tailBytes_effect mode _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.mapM mode _ (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _) _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem decodeArg_string_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (data : Solidity.Roadmap.Bytes) (i : Nat) (l : Solidity.Source.DataLoc), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.decodeArg (E := E) (Γ := Γ) data i (.string l)) := by
  intro E Γ mode data i l
  cases l <;> unfold Solidity.Source.decodeArg
  all_goals repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.tailBytes_effect mode _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect mode _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.mapM mode _ (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _) _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem decodeArg_array_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (data : Solidity.Roadmap.Bytes) (i : Nat) (l : Solidity.Source.DataLoc) (σ : Solidity.Source.STy) (len : Option Nat), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.decodeArg (E := E) (Γ := Γ) data i (.array l σ len)) := by
  intro E Γ mode data i l σ len
  cases l with
  | memory =>
    cases len with
    | some len => exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
    | none =>
      unfold Solidity.Source.decodeArg
      dsimp only
      split
      · split
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
        · split
          · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
          · split
            · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
              · exact Solidity.Lowering.Readonly.SourceHistory.Effect.mapM mode _ (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _) _
              · intro xs
                exact Solidity.Lowering.Readonly.SourceHistory.allocRef_effect mode _
            · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
  | storage =>
    cases len <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
  | calldata =>
    cases len with
    | some len => exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
    | none =>
      unfold Solidity.Source.decodeArg
      dsimp only
      split
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _

theorem decodeArg_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (data : Solidity.Roadmap.Bytes) (i : Nat) (τ : Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.decodeArg (E := E) (Γ := Γ) data i τ) := by
  intro E Γ mode data i τ
  cases τ <;> first
  | exact Solidity.Lowering.Readonly.SourceHistory.decodeArg_bytes_effect mode data i _
  | exact Solidity.Lowering.Readonly.SourceHistory.decodeArg_string_effect mode data i _
  | exact Solidity.Lowering.Readonly.SourceHistory.decodeArg_array_effect mode data i _ _ _
  | exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _

theorem extReturn_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (rs : List Solidity.Source.STy) (out : Solidity.Roadmap.Outcome), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.extReturn (E := E) (Γ := Γ) rs out) := by
  intro E Γ mode rs out
  unfold Solidity.Source.extReturn
  apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
  · exact Solidity.Lowering.Readonly.SourceHistory.reraise_effect mode out
  · intro data
    repeat' first
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _)
     | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
     | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
     | split
     | dsimp only

theorem decodeArgs_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (data : Solidity.Roadmap.Bytes) (τs : List Solidity.Source.STy) (i : Nat), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.decodeArgs (E := E) (Γ := Γ) data τs i) := by
  intro E Γ mode data τs
  induction τs with
  | nil => intro i; exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  | cons τ τs ih =>
    intro i
    exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.decodeArg_effect mode data i τ) (fun value =>
      Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (ih (i+1)) (fun values => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _))

theorem abiDecodeData_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (data : Solidity.Roadmap.Bytes) (τs : List Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.abiDecodeData (E := E) (Γ := Γ) data τs) := by
  intro E Γ mode data τs
  unfold Solidity.Source.abiDecodeData
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.decodeArgs_effect mode data τs 0) (fun values => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)

end Solidity.Lowering.Readonly.SourceHistory
