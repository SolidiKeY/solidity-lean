import Solidity.Backend.MemoryCopies.SourceFramesInterface

/-! Allocation-frame specializations of the existing Source run/bind rules.
No interpreter or alternative heap representation is introduced. -/
namespace Solidity.Backend.MemoryCopies

namespace AllocationExtension

theorem refl {E : Source.Env} {Γ : Source.RCtx} (state : Source.EMState E Γ) :
    AllocationExtension state state :=
  ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem trans {E : Source.Env} {Γ : Source.RCtx} {first middle last : Source.EMState E Γ}
    (left : AllocationExtension first middle) (right : AllocationExtension middle last) :
    AllocationExtension first last := by
  refine ⟨?_, Nat.le_trans left.growth right.growth, ?_⟩
  · rw [right.frame, left.frame]
  · intro address older
    exact (right.old address (Nat.lt_of_lt_of_le older left.growth)).trans (left.old address older)

end AllocationExtension

namespace AllocatesOnly

variable {E : Source.Env} {Γ : Source.RCtx} {α β : Type}

theorem pure' (value : α) : AllocatesOnly (pure value : Source.EM E Γ α) :=
  fun before => AllocationExtension.refl before

theorem halt (reason : Source.Halt) :
    AllocatesOnly (Source.EM.halt reason : Source.EM E Γ α) :=
  fun before => AllocationExtension.refl before

theorem lift (outcome : Source.R α) :
    AllocatesOnly (Source.EM.lift outcome : Source.EM E Γ α) := by
  cases outcome <;> exact fun before => AllocationExtension.refl before

theorem bind {operation : Source.EM E Γ α} {next : α → Source.EM E Γ β}
    (first : AllocatesOnly operation) (rest : ∀ value : α, AllocatesOnly (next value)) :
    AllocatesOnly (operation >>= next) := by
  intro before
  rw [Source.Hoare.run_bind]
  have preserved : AllocationExtension before (operation.run before).2 := first before
  rcases execution : operation.run before with ⟨outcome, reached⟩
  rw [execution] at preserved
  cases outcome with
  | ok value => exact preserved.trans (rest value reached)
  | error reason => exact preserved

theorem st : AllocatesOnly (Source.EM.st : Source.EM E Γ (Source.St E)) :=
  fun before => AllocationExtension.refl before

theorem alloc {τ : Source.STy} (data : Source.Data E.layout τ) :
    AllocatesOnly (Source.alloc (E := E) (Γ := Γ) data) := by
  intro before
  change AllocationExtension before
    (before.1, {before.2 with heap := (before.2.heap.alloc ⟨τ, data⟩).1})
  refine ⟨rfl, Nat.le_succ _, ?_⟩
  intro address older
  exact Source.Heap.alloc_other before.2.heap ⟨τ, data⟩ (Nat.ne_of_lt older)

theorem allocRef {τ : Source.STy} (data : Source.Data E.layout τ) :
    AllocatesOnly (Source.allocRef (E := E) (Γ := Γ) data) := by
  unfold Source.allocRef
  apply bind (alloc data)
  intro address
  split
  · exact pure' _
  · exact halt _

theorem readCell (frame : Source.Fr) (path : Source.SPath) :
    AllocatesOnly (Source.readCell (E := E) (Γ := Γ) frame path) := by
  unfold Source.readCell
  apply bind st
  intro state
  split
  · dsimp only
    split
    · exact pure' _
    · exact halt _
  · dsimp only
    split
    · exact pure' _
    · exact halt _

theorem readAt (frame : Source.Fr) (path : Source.SPath) (τ : Source.STy) :
    AllocatesOnly (Source.readAt (E := E) (Γ := Γ) frame path τ) := by
  unfold Source.readAt
  apply bind (readCell frame path)
  intro value
  split
  · exact pure' _
  · exact halt _

theorem readLen (frame : Source.Fr) (path : Source.SPath) :
    AllocatesOnly (Source.readLen (E := E) (Γ := Γ) frame path) := by
  unfold Source.readLen
  apply bind (readAt frame path (.int .u256))
  intro value
  cases value with
  | int integer bound => exact pure' _
  | memRef impossible _ => cases impossible
  | storRef impossible _ => cases impossible
  | cdRef impossible _ _ => cases impossible

end AllocatesOnly
end Solidity.Backend.MemoryCopies
