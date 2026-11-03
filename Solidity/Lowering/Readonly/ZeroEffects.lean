import Solidity.Lowering.Readonly.ReadEffects

/-! Actual Source zero-initialization histories. Allocating memory remains
permitted in either mode; missing defaults and exhausted bounds retain their
actual halts. No layout-validity or successful-initialization premise is used. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ : RCtx}

/-- Closed mutual induction for all four zero-initialization functions. -/
theorem zero_histories (mode : Bool) (n : Nat) :
    (∀ τ, Effect mode (zeroData (E := E) (Γ := Γ) n τ)) ∧
    (∀ τ, Effect mode (zeroVal (E := E) (Γ := Γ) n τ)) ∧
    (∀ σ m, Effect mode (zeroElems (E := E) (Γ := Γ) n σ m)) ∧
    (∀ τs, Effect mode (zeroFields (E := E) (Γ := Γ) n τs)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro τ; exact Effect.halt mode _
    · intro τ; exact Effect.halt mode _
    · intro σ m; cases m <;> exact Effect.halt mode _
    · intro τs; cases τs <;> exact Effect.halt mode _
  | succ n ih =>
    rcases ih with ⟨data, values, elems, fields⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro τ
      cases τ
      case bytes loc => exact Effect.pure mode _
      case string loc => exact Effect.pure mode _
      case array loc σ size =>
        cases size with
        | none => exact Effect.pure mode _
        | some m => exact Effect.bind _ _ _ (elems σ m) (fun xs => Effect.pure mode _)
      case struct loc d => exact Effect.bind _ _ _ (fields _) (fun xs => Effect.pure mode _)
      all_goals exact Effect.bind _ _ _ (values _) (fun value => Effect.pure mode _)
    · intro τ
      simp only [zeroVal]
      split
      · exact Effect.pure mode _
      · split
        · exact Effect.bind _ _ _ (data τ) (fun x => allocRef_effect mode x)
        · exact Effect.halt mode _
    · intro σ m
      cases m with
      | zero => exact Effect.pure mode _
      | succ m =>
        exact Effect.bind _ _ _ (values σ) (fun x =>
          Effect.bind _ _ _ (elems σ m) (fun f => Effect.pure mode _))
    · intro τs
      cases τs with
      | nil => exact Effect.pure mode _
      | cons τ τs =>
        exact Effect.bind _ _ _ (values τ) (fun x =>
          Effect.bind _ _ _ (fields τs) (fun xs => Effect.pure mode _))

end Solidity.Lowering.Readonly.SourceHistory
