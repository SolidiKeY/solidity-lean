import Solidity.Lowering.Readonly.MachineEffects

/-! Actual Source read/reference histories. Both successful and refused reads
are retained; no type, heap-validity or storage-totality premise is added. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env} {Γ : RCtx}

theorem readCell_effect (mode : Bool) (F : Fr) (p : SPath) :
    Effect mode (readCell (E := E) (Γ := Γ) F p) := by
  unfold readCell
  apply Effect.bind
  · exact Effect.st mode
  · intro state
    repeat' first
    | exact Effect.pure mode _
    | exact Effect.halt mode _
    | split
    | dsimp only

theorem heapObj_effect (mode : Bool) (a : Nat) :
    Effect mode (heapObj (E := E) (Γ := Γ) a) := by
  unfold heapObj
  apply Effect.bind
  · exact Effect.st mode
  · intro state
    repeat' first
    | exact Effect.pure mode _
    | exact Effect.halt mode _
    | split
    | dsimp only

theorem storRef_effect (mode : Bool) (τ : STy) (p : SPath) :
    Effect mode (storRef (E := E) (Γ := Γ) τ p) := by
  unfold storRef
  split
  · exact Effect.pure mode _
  · exact Effect.halt mode _


theorem readAt_effect (mode : Bool) (F : Fr) (p : SPath) (τ : STy) :
    Effect mode (readAt (E := E) (Γ := Γ) F p τ) := by
  unfold readAt
  apply Effect.bind
  · exact readCell_effect mode F p
  · intro value
    split
    · exact Effect.pure mode _
    · exact Effect.halt mode _


theorem readLen_effect (mode : Bool) (F : Fr) (p : SPath) :
    Effect mode (readLen (E := E) (Γ := Γ) F p) := by
  unfold readLen
  apply Effect.bind
  · exact readAt_effect mode F p _
  · intro value
    cases value <;> first
    | exact Effect.pure mode _
    | contradiction

theorem writeAt_effect {τ : STy} (F : Fr) (p : SPath) (value : Val E.layout τ) :
    Effect F.static (writeAt (Γ := Γ) F p value) := by
  unfold writeAt
  split
  · intro locals state
    exact JournalLeaves.cell_history F p _ locals state
  · exact Effect.halt F.static _

theorem heapAt_effect (mode : Bool) (a : Nat) (τ : STy) :
    Effect mode (heapAt (E := E) (Γ := Γ) a τ) := by
  unfold heapAt
  apply Effect.bind
  · exact heapObj_effect mode a
  · rintro ⟨σ, x⟩
    repeat' first
    | exact Effect.pure mode _
    | exact Effect.halt mode _
    | split
    | dsimp only

theorem heapBytes_effect (mode : Bool) (a : Nat) :
    Effect mode (heapBytes (E := E) (Γ := Γ) a) := by
  unfold heapBytes
  apply Effect.bind
  · exact heapObj_effect mode a
  · rintro ⟨σ, x⟩
    cases x <;> first
    | exact Effect.pure mode _
    | exact Effect.halt mode _

theorem allocRef_effect {τ : STy} (mode : Bool) (x : Data E.layout τ) :
    Effect mode (allocRef (Γ := Γ) x) := by
  unfold allocRef
  apply Effect.bind
  · exact alloc_effect mode x
  · intro a
    split
    · exact Effect.pure mode _
    · exact Effect.halt mode _

end Solidity.Lowering.Readonly.SourceHistory
