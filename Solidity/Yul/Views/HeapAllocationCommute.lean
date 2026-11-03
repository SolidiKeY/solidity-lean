import Solidity.Yul.Views.HeapByteAllocation
import Solidity.Yul.Views.JointPlacement

namespace Solidity.Yul.Views

theorem heap_type_present {D} (h : Source.Heap D) (a : Nat) (τ : Source.STy)
    (typed : h.ty a=some τ) : (h.cells a).isSome := by
  have present := congrArg Option.isSome typed
  simpa only [Source.Heap.ty,Option.isSome_map] using present

theorem heap_alloc_old_type {D} (h : Source.Heap D) (x : Σ τ,Source.Data D τ) (a : Nat) (τ : Source.STy)
    (typed : h.ty a=some τ) : (h.alloc x).1.ty a=some τ := by
  change ((h.alloc x).1.get a).map Sigma.fst=some τ
  rw [Source.Heap.alloc_other h x (occupied_ne_next h a (heap_type_present h a τ typed))]
  exact typed

/-- Actual whole-heap commutation. The write target is an old typed cell,
never the freshly allocated logical identity. No disjointness law is assumed. -/
theorem heap_write_alloc {D} (h : Source.Heap D) (x : Σ τ,Source.Data D τ)
    (a : Nat) {τ} (d : Source.Data D τ) (typed : h.ty a=some τ) :
    ((h.write a d typed).alloc x).1=(h.alloc x).1.write a d (heap_alloc_old_type h x a τ typed) := by
  have different := occupied_ne_next h a (heap_type_present h a τ typed)
  apply heap_cells_ext ((h.write a d typed).alloc x).1
    ((h.alloc x).1.write a d (heap_alloc_old_type h x a τ typed)) ?_ rfl
  funext b
  by_cases fresh : b=h.next
  · subst b
    simp only [Source.Heap.alloc,Source.Heap.write,if_true,if_neg (Ne.symm different)]
  · by_cases target : b=a
    · subst b
      simp only [Source.Heap.alloc,Source.Heap.write,if_true,if_neg different]
    · simp only [Source.Heap.alloc,Source.Heap.write,if_neg fresh,if_neg target]

/-- These witnesses describe ACTUAL typed writes, hence keep logical next.
The proof does not infer allocation history from geometry alone. -/
theorem RetainedAllocation.next {D} {origin h : Source.Heap D} {allocated : Placement origin}
    {current : Placement h} (history : RetainedAllocation allocated current) : h.next=origin.next := by
  induction history with
  | initial => rfl
  | written current geometry prior a d typed shape shaped capacity ih => exact ih

theorem RetainedAllocation.types {D} {origin h : Source.Heap D} {allocated : Placement origin}
    {current : Placement h} (history : RetainedAllocation allocated current) : h.ty=origin.ty := by
  induction history with
  | initial => rfl
  | written current geometry prior a d typed shape shaped capacity ih =>
    exact (funext (fun b => Source.Heap.write_ty _ _ b _ _)).trans ih

theorem placement_cast_choices {D} {h k : Source.Heap D} (same : h=k) (p : Placement h) :
    (same ▸ p).address=p.address ∧ (same ▸ p).shape=p.shape ∧ (same ▸ p).free=p.free := by
  cases same
  exact ⟨rfl,rfl,rfl⟩

theorem retainedAllocation_cast {D} {origin h k : Source.Heap D} {allocated : Placement origin}
    (same : h=k) (p : Placement h) (history : RetainedAllocation allocated p) :
    RetainedAllocation allocated (same ▸ p) := by
  cases same
  exact history

end Solidity.Yul.Views
