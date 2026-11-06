import Solidity.Lowering.Readonly.ReadEffects

/-! Actual Source storage-to-memory histories. Reading and allocating memory
are permitted in either mode. Refused reads and exhausted bounds retain their
actual states; no successful-copy or valid-layout premise is introduced. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ : RCtx}

theorem load_histories (mode : Bool) (F : Fr) (n : Nat) :
    (∀ τ p, Effect mode (loadMem (E := E) (Γ := Γ) F n τ p)) ∧
    (∀ τ p, Effect mode (loadElem (E := E) (Γ := Γ) F n τ p)) ∧
    (∀ τ p i m, Effect mode (loadElems (E := E) (Γ := Γ) F n τ p i m)) ∧
    (∀ τs p i, Effect mode (loadFields (E := E) (Γ := Γ) F n τs p i)) ∧
    (∀ p i k, Effect mode (loadBytes (E := E) (Γ := Γ) F n p i k)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ p; exact Effect.halt mode _
    · intro τ p; exact Effect.halt mode _
    · intro τ p i m; cases m <;> exact Effect.halt mode _
    · intro τs p i; cases τs <;> exact Effect.halt mode _
    · intro p i k; cases k <;> exact Effect.halt mode _
  | succ n ih =>
    rcases ih with ⟨memory, element, elems, fields, bytes⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ p
      cases τ
      case bytes loc =>
        exact Effect.bind _ _ _ (readLen_effect mode F p) (fun len =>
          Effect.bind _ _ _ (bytes p 0 len) (fun bs => Effect.pure mode _))
      case string loc =>
        exact Effect.bind _ _ _ (readLen_effect mode F p) (fun len =>
          Effect.bind _ _ _ (bytes p 0 len) (fun bs => Effect.pure mode _))
      case array loc σ size =>
        cases size with
        | none =>
          exact Effect.bind _ _ _ (readLen_effect mode F p) (fun len =>
            Effect.bind _ _ _ (elems σ p 0 len) (fun xs => Effect.pure mode _))
        | some m => exact Effect.bind _ _ _ (elems σ p 0 m) (fun xs => Effect.pure mode _)
      case struct loc d => exact Effect.bind _ _ _ (fields _ p 0) (fun fs => Effect.pure mode _)
      case mapping key value => exact Effect.halt mode _
      all_goals exact Effect.bind _ _ _ (readAt_effect mode F p _) (fun v => Effect.pure mode _)
    · intro τ p
      simp only [loadElem]
      split
      · exact Effect.bind _ _ _ (memory τ p) (fun x => allocRef_effect mode x)
      · exact readAt_effect mode F p τ
    · intro τ p i m
      cases m with
      | zero => exact Effect.pure mode _
      | succ m => exact Effect.bind _ _ _ (element τ (p.go (.index i))) (fun x =>
          Effect.bind _ _ _ (elems τ p (i+1) m) (fun xs => Effect.pure mode _))
    · intro τs p i
      cases τs with
      | nil => exact Effect.pure mode _
      | cons τ τs => exact Effect.bind _ _ _ (element τ (p.go (.field i))) (fun x =>
          Effect.bind _ _ _ (fields τs p (i+1)) (fun xs => Effect.pure mode _))
    · intro p i k
      cases k with
      | zero => exact Effect.pure mode _
      | succ k =>
        apply Effect.bind
        · exact readAt_effect mode F _ _
        · intro value
          cases value <;> first
          | exact Effect.bind _ _ _ (bytes p (i+1) k) (fun bs => Effect.pure mode _)
          | contradiction

end Solidity.Lowering.Readonly.SourceHistory
