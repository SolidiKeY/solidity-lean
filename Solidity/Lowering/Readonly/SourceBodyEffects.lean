import Solidity.Lowering.Readonly.SourceExpressionEffects
import Solidity.Lowering.Readonly.LocalInitializationEffects

/-! Actual body-history induction components. Hypotheses remain at the strictly
smaller bound; checked arithmetic updates do not clear inherited static mode. -/
namespace Solidity.Lowering.Readonly.SourceHistory
theorem callInternal_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (d : Solidity.Source.Decl) {ps : List Solidity.Source.STy} (vs : Solidity.Source.Vals E.layout ps) (rs : List Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.callInternal G F (n+1) d vs rs) := by
  intro E G F n h d ps vs rs
  simp only [Solidity.Source.callInternal]
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact Solidity.Lowering.Readonly.SourceHistory.zeroVals_effect F.static n rs
    · intro defaults
      dsimp only
      split
      · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
        · exact h.runMods {F with checked := true} _ _ _
        · intro locals
          exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _) (fun returns => Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
theorem execItems_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (nps : Nat) (ph : Option (Solidity.Source.Ph E)) {R : List Solidity.Source.STy} {M : Bool} {k : Solidity.Source.SCtx} {Γ Γ' : Solidity.Source.RCtx} (b : Solidity.Source.RItems E R M k Γ Γ') (l : Solidity.Source.Locals E.layout Γ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.execItems G F (n+1) nps ph b l) := by
  intro E G F n h nps ph R M k Γ Γ' b l
  cases b
  case nil => exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
  case stmt =>
    unfold Solidity.Source.execItems
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact h.execS F _ _ _ _
    · intro out
      cases out
      case normal =>
        exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (h.execItems F _ _ _ _) (fun result => Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
      all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
  case unchecked =>
    unfold Solidity.Source.execItems
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact h.execItems {F with checked := false} _ _ _ _
    · intro out
      cases out
      case normal =>
        exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _) (fun restored => h.execItems F _ _ _ restored)
      all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _

theorem runMods_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (b : Solidity.Source.RBody E) (mods : List (Solidity.Source.RModInv E b.locals)) (l : Solidity.Source.Locals E.layout b.locals), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.runMods G F (n+1) b mods l) := by
  intro E G F n h b mods l
  cases mods with
  | nil =>
    unfold Solidity.Source.runMods
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact h.execItems F _ _ _ _
    · intro out
      cases out
      case normal => exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _
      case ret => exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
      all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  | cons modifier rest =>
    unfold Solidity.Source.runMods
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · apply Solidity.Lowering.Readonly.SourceHistory.Effect.sub
      exact h.evalConvArgs F _
    · intro pair
      rcases pair with ⟨vs, updated⟩
      cases chosen : G.prog.body (G.dispatchMod F.contract modifier.modifier) with
      | none => exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
      | some body =>
        dsimp only
        split
        · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
          · exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static
          · intro saved
            apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
            · exact Solidity.Lowering.Readonly.SourceHistory.Effect.modSt F.static _ (fun _ => rfl)
            · intro done
              apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
              · apply Solidity.Lowering.Readonly.SourceHistory.Effect.attempt
                exact h.execItems F _ _ _ _
              · intro caught
                apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
                · exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static
                · intro reached
                  cases current : reached.fnLocals with
                  | mk context values =>
                    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
                    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.modSt F.static _ (fun _ => rfl)
                    · intro restored
                      cases caught
                      all_goals repeat' first
                       | exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
                       | exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
                       | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
                       | split
                       | dsimp only
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _

end Solidity.Lowering.Readonly.SourceHistory
