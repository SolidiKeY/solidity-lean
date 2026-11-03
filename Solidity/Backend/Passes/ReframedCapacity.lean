import Solidity.Backend.Passes.ReframedSequence

/-! Actual allocator capacity transport when a physical local reservation
shrinks. Cursor, zero tail, live intervals and all object identities stay fixed.
The positive new reservation is explicit; positive allocation cannot use frame0. -/
namespace Solidity.Backend.Passes
open Evm Evm.Memory

theorem allocator_reservation_shrink {H : HTy} {hp : Heap H}
    {base : Nat → Fin W} {m : Machine} {cursor : Fin W} {before after : Nat}
    (h : StructAllocatorRepr hp base before cursor m)
    (smaller : after ≤ before) (positive : 0 < after) :
    StructAllocatorRepr hp base after cursor m :=
  ⟨⟨⟨h.arrays.heap.arrays,fun r => Nat.le_trans smaller (h.arrays.heap.above r),
      h.arrays.heap.separated⟩,
    ⟨positive,Nat.le_trans smaller h.arrays.free.above,h.arrays.free.cell,h.arrays.free.zero⟩,
    h.arrays.live⟩,
   ⟨h.structs.objects,fun r => Nat.le_trans smaller (h.structs.above r),h.structs.separated⟩,
   h.separated,h.live⟩

theorem allocation_input_reservation_shrink {C : Contract} {Γ : Ctx}
    {b before after amount : Nat} {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : AllocationInput b before amount σ base m)
    (smaller : after ≤ before) (positive : 0 < after) :
    AllocationInput b after amount σ base m := by
  rcases h with zero | ⟨hb,cursor,allocator,fit⟩
  · exact .inl zero
  · exact .inr ⟨hb,cursor,allocator_reservation_shrink allocator smaller positive,fit⟩

theorem positive_allocation_refuses_zero_frame {C : Contract} {Γ : Ctx}
    {b amount : Nat} {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (nonzero : amount ≠ 0) :
    ¬ AllocationInput b 0 amount σ base m := by
  rintro (zero | ⟨_,cursor,allocator,_⟩)
  · exact nonzero zero
  · exact Nat.not_lt_zero _ allocator.arrays.free.reserved
end Solidity.Backend.Passes
