import Solidity.Lowering.Readonly.SourceLoopEffects

/-! Actual dispatch branches at the successor bound. Source admission, runtime values and every refusal are unchanged. -/
namespace Solidity.Lowering.Readonly.SourceHistory
theorem dispatch_function_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (input : Solidity.Roadmap.Bytes) (d : Solidity.Source.Decl), G.pickFn F input = some d → input.isEmpty = false → Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.dispatch G F (n+1) input) := by
  intro E G F n h input d selected nonempty
  simp only [Solidity.Source.dispatch, selected, nonempty]
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.decodeArgs_effect F.static _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F n _ _)
   | (with_reducible apply Solidity.Lowering.Readonly.SourceHistory.Effect.sub; exact h.callInternal F _ _ _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only
theorem dispatch_getter_no_function_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (input : Solidity.Roadmap.Bytes) (d : Solidity.Source.Decl) (ps : List Solidity.Source.STy) (r : Solidity.Source.STy), G.pickFn F input = none → G.pickGetter F input = some (d, ps, r) → Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.dispatch G F (n+1) input) := by
  intro E G F n h input d ps r absent selected
  simp only [Solidity.Source.dispatch, absent, selected]
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F n _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getterPath_effect F.static F n _ _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
   | (with_reducible apply Solidity.Lowering.Readonly.SourceHistory.Effect.sub; exact h.evalE F _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem dispatch_getter_empty_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (input : Solidity.Roadmap.Bytes) (fd d : Solidity.Source.Decl) (ps : List Solidity.Source.STy) (r : Solidity.Source.STy), G.pickFn F input = some fd → input.isEmpty = true → G.pickGetter F input = some (d, ps, r) → Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.dispatch G F (n+1) input) := by
  intro E G F n h input fd d ps r present empty selected
  simp only [Solidity.Source.dispatch, present, empty, selected]
  repeat' first
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.encodeVals_effect F.static F n _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getterPath_effect F.static F n _ _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect F.static F _ _)
   | (with_reducible apply Solidity.Lowering.Readonly.SourceHistory.Effect.sub; exact h.evalE F _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem dispatch_special_no_function_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (input : Solidity.Roadmap.Bytes), G.pickFn F input = none → G.pickGetter F input = none → Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.dispatch G F (n+1) input) := by
  intro E G F n h input absent selected
  simp only [Solidity.Source.dispatch, absent, selected]
  repeat' first
   | (with_reducible exact h.runMods F _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.zeroVals_effect F.static n _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F n _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem dispatch_special_empty_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (input : Solidity.Roadmap.Bytes) (fd : Solidity.Source.Decl), G.pickFn F input = some fd → input.isEmpty = true → G.pickGetter F input = none → Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.dispatch G F (n+1) input) := by
  intro E G F n h input fd present empty selected
  simp only [Solidity.Source.dispatch, present, empty, selected]
  repeat' first
   | (with_reducible exact h.runMods F _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.zeroVals_effect F.static n _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.bytesOfRV_effect F.static F n _)
   | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
   | split
   | dsimp only

theorem dispatch_succ : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (_h : Solidity.Lowering.Readonly.SourceHistory.At G n) (input : Solidity.Roadmap.Bytes), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.dispatch G F (n+1) input) := by
  intro E G F n h input
  cases selected : G.pickFn F input with
  | none =>
    cases getter : G.pickGetter F input with
    | none => exact Solidity.Lowering.Readonly.SourceHistory.dispatch_special_no_function_succ G F n h input selected getter
    | some result =>
      rcases result with ⟨d, ps, r⟩
      exact Solidity.Lowering.Readonly.SourceHistory.dispatch_getter_no_function_succ G F n h input d ps r selected getter
  | some fd =>
    cases empty : input.isEmpty with
    | false => exact Solidity.Lowering.Readonly.SourceHistory.dispatch_function_succ G F n h input fd selected empty
    | true =>
      cases getter : G.pickGetter F input with
      | none => exact Solidity.Lowering.Readonly.SourceHistory.dispatch_special_empty_succ G F n h input fd selected empty getter
      | some result =>
        rcases result with ⟨d, ps, r⟩
        exact Solidity.Lowering.Readonly.SourceHistory.dispatch_getter_empty_succ G F n h input fd d ps r selected empty getter
end Solidity.Lowering.Readonly.SourceHistory
