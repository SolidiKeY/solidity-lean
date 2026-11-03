import Solidity.Lowering.Readonly.ReadEffects

/-! Recursive Source deletion histories. The step follows the actual type
branches, including mapping no-op and dynamic write refusal. It assumes only
the smaller-bound mutually recursive histories until the induction closes. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ : RCtx}

theorem deleteStor_step (F : Fr) (n : Nat)
    (range : ∀ τ p i k, Effect F.static (deleteRange (E := E) (Γ := Γ) F n τ p i k))
    (fields : ∀ τs p i, Effect F.static (deleteFields (E := E) (Γ := Γ) F n τs p i)) :
    ∀ τ p, Effect F.static (deleteStor (E := E) (Γ := Γ) F (n + 1) τ p) := by
  intro τ p
  have cell : ∀ p (value : Option (Val E.layout (E.cellTy p))),
      Effect F.static (setCell (Γ := Γ) F p value) :=
    fun p value locals state => JournalLeaves.cell_history F p value locals state
  cases τ
  case bytes loc =>
    exact Effect.bind _ _ _ (readLen_effect F.static F p)
      (fun len => Effect.bind _ _ _ (range _ p 0 len) (fun _ => cell p none))
  case string loc =>
    exact Effect.bind _ _ _ (readLen_effect F.static F p)
      (fun len => Effect.bind _ _ _ (range _ p 0 len) (fun _ => cell p none))
  case array loc σ size =>
    cases size with
    | none =>
      exact Effect.bind _ _ _ (readLen_effect F.static F p)
        (fun len => Effect.bind _ _ _ (range σ p 0 len) (fun _ => cell p none))
    | some m => exact range σ p 0 m
  case struct loc d => exact fields _ p 0
  case mapping key value => exact Effect.pure F.static ()
  all_goals exact cell p none


/-- All three mutually recursive Source deletion functions produce guarded
histories at every bound, including exhaustion and refused writes. -/
theorem delete_histories (F : Fr) (n : Nat) :
    (∀ τ p, Effect F.static (deleteStor (E := E) (Γ := Γ) F n τ p)) ∧
    (∀ τ p i k, Effect F.static (deleteRange (E := E) (Γ := Γ) F n τ p i k)) ∧
    (∀ τs p i, Effect F.static (deleteFields (E := E) (Γ := Γ) F n τs p i)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro τ p; exact Effect.halt F.static _
    · intro τ p i k; cases k <;> exact Effect.halt F.static _
    · intro τs p i; cases τs <;> exact Effect.halt F.static _
  | succ n ih =>
    rcases ih with ⟨stor, range, fields⟩
    refine ⟨deleteStor_step F n range fields, ?_, ?_⟩
    · intro τ p i k
      cases k with
      | zero => exact Effect.pure F.static _
      | succ k => exact Effect.bind _ _ _ (stor _ _) (fun _ => range _ _ _ _)
    · intro τs p i
      cases τs with
      | nil => exact Effect.pure F.static _
      | cons τ τs => exact Effect.bind _ _ _ (stor _ _) (fun _ => fields _ _ _)

end Solidity.Lowering.Readonly.SourceHistory
