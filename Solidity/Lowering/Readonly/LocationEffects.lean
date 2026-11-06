import Solidity.Lowering.Readonly.EvalEffectsBase

/-! Journal effects for actual Source locations. Memory/local mutation remains
permitted in static mode; storage writes retain the real dynamic guard. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source


theorem memElem_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} (mode : Bool) (a i : Nat) (τ : Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.memElem (E := E) (Γ := Γ) a i τ) := by
  intro E Γ mode a i τ
  unfold Solidity.Source.memElem
  apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
  · exact Solidity.Lowering.Readonly.SourceHistory.heapObj_effect mode a
  · rintro ⟨σ, x⟩
    cases x
    case array =>
      dsimp only
      split
      · split
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
    case struct =>
      exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _)
    all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _

theorem memSet_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (mode : Bool) (a i : Nat) (v : Solidity.Source.Val E.layout τ), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.memSet (Γ := Γ) a i v) := by
  intro E Γ τ mode a i v
  unfold Solidity.Source.memSet
  apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
  · exact Solidity.Lowering.Readonly.SourceHistory.heapObj_effect mode a
  · rintro ⟨σ, x⟩
    cases x
    case array =>
      dsimp only
      split
      · split
        · exact Solidity.Lowering.Readonly.SourceHistory.heapPut_effect mode a _
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
    case struct =>
      exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _) (fun _ => Solidity.Lowering.Readonly.SourceHistory.heapPut_effect mode a _)
    all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _


theorem readLoc_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (mode : Bool) (F : Solidity.Source.Fr) (loc : Solidity.Source.Loc E.layout Γ τ),
 Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.readLoc F loc) := by
  intro E Γ τ mode F loc
  cases loc
  case «local» i =>
    exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.locals mode) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _)
  case stor p =>
    simp only [Solidity.Source.readLoc]
    split
    · exact Solidity.Lowering.Readonly.SourceHistory.storRef_effect mode τ p
    · exact Solidity.Lowering.Readonly.SourceHistory.readAt_effect mode F p τ
  case mem a i => exact Solidity.Lowering.Readonly.SourceHistory.memElem_effect mode a i τ
  case memByte a i =>
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact Solidity.Lowering.Readonly.SourceHistory.heapBytes_effect mode a
    · intro bs
      split
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _
  case cd off => exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _


theorem writeLoc_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (F : Solidity.Source.Fr) (n : Nat)
 (loc : Solidity.Source.Loc E.layout Γ τ) (v : Solidity.Source.Val E.layout τ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.writeLoc F n loc v) := by
  intro E Γ τ F n loc v
  cases loc
  case «local» i =>
    exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.locals F.static) (fun _ => Solidity.Lowering.Readonly.SourceHistory.Effect.setLocals F.static _)
  case stor p =>
    simp only [Solidity.Source.writeLoc]
    split
    · exact (Solidity.Lowering.Readonly.SourceHistory.store_histories F n).2.1 τ p v
    · exact Solidity.Lowering.Readonly.SourceHistory.writeAt_effect F p v
  case mem a i => exact Solidity.Lowering.Readonly.SourceHistory.memSet_effect F.static a i v
  case memByte a i =>
    cases v
    case fixedBytes =>
      apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
      · exact Solidity.Lowering.Readonly.SourceHistory.heapObj_effect F.static a
      · rintro ⟨σ, x⟩
        cases x
        case bytes =>
          dsimp only
          split
          · exact Solidity.Lowering.Readonly.SourceHistory.heapPut_effect F.static a _
          · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _
        case string =>
          dsimp only
          split
          · exact Solidity.Lowering.Readonly.SourceHistory.heapPut_effect F.static a _
          · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _
        all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
    all_goals contradiction
  case cd off => exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _

theorem lengthOf_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (mode : Bool) (F : Solidity.Source.Fr) (v : Solidity.Source.Val E.layout τ), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.lengthOf (Γ := Γ) F v) := by
  intro E Γ τ mode F v
  unfold Solidity.Source.lengthOf
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.readLen_effect mode F _
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact Solidity.Lowering.Readonly.SourceHistory.heapObj_effect mode _
    · rintro ⟨σ, data⟩
      cases data <;> first
      | exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
      | exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt mode _


theorem deleteLoc_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {τ : Solidity.Source.STy} (F : Solidity.Source.Fr) (n : Nat) (loc : Solidity.Source.Loc E.layout Γ τ),
 Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.deleteLoc F n loc) := by
  intro E Γ τ F n loc
  cases loc
  case stor p =>
    simp only [Solidity.Source.deleteLoc]
    split
    · exact (Solidity.Lowering.Readonly.SourceHistory.delete_histories F n).1 τ p
    · intro locals state
      exact Solidity.Lowering.Readonly.JournalLeaves.cell_history F p none locals state
  all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ((Solidity.Lowering.Readonly.SourceHistory.zero_histories F.static n).2.1 _) (fun v => Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect F n _ v)

theorem indexLoc_effect : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx} {l : Solidity.Source.DataLoc} {σ : Solidity.Source.STy} {k : Option Nat} (mode : Bool) (F : Solidity.Source.Fr)
 (a : Solidity.Source.Val E.layout (.array l σ k)) (i : Nat), Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.indexLoc (Γ := Γ) F a i) := by
  intro E Γ l σ k mode F a i
  unfold Solidity.Source.indexLoc
  apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
  · exact Solidity.Lowering.Readonly.SourceHistory.lengthOf_effect mode F a
  · intro len
    split
    · cases a <;> exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure mode _
    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift mode _

end Solidity.Lowering.Readonly.SourceHistory
