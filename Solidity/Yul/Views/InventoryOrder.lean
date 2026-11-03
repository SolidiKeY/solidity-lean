import Solidity.Yul.Views.InventoryRealization

namespace Solidity.Yul.Views

theorem runInventoryUpdates_swap {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} (u v : OwnedInventoryUpdate allocated p)
    (rest : List (OwnedInventoryUpdate allocated p)) (s : Source.EMState E Γ) (types : s.2.heap.ty = h.ty)
    (distinct : u.entry.id ≠ v.entry.id) :
    (runInventoryUpdates (u::v::rest)).run s = (runInventoryUpdates (v::u::rest)).run s := by
  have hu : s.2.heap.ty u.entry.id = some u.entry.ty := types ▸ heap_ty_of_get h u.entry.id _ _ u.entry.found
  have hv : s.2.heap.ty v.entry.id = some v.entry.ty := types ▸ heap_ty_of_get h v.entry.id _ _ v.entry.found
  have first : (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run s =
    (.ok (),withSourceHeap s (s.2.heap.write u.entry.id u.object.data hu)) := heapPutConcrete_run s _ _ hu
  have second : (Source.heapPut v.entry.id ⟨v.entry.ty,v.object.data⟩ : Source.EM E Γ Unit).run s =
    (.ok (),withSourceHeap s (s.2.heap.write v.entry.id v.object.data hv)) := heapPutConcrete_run s _ _ hv
  simp only [runInventoryUpdates,Source.Hoare.run_bind]
  rw [first,second]
  simp only []
  rw [heapPutConcrete_run _ _ _ (by change (s.2.heap.write u.entry.id u.object.data hu).ty v.entry.id = some v.entry.ty; rw [Source.Heap.write_ty]; exact hv)]
  simp only []
  rw [heapPutConcrete_run _ _ _ (by change (s.2.heap.write v.entry.id v.object.data hv).ty u.entry.id = some u.entry.ty; rw [Source.Heap.write_ty]; exact hu)]
  simp only []
  change (runInventoryUpdates rest).run (withSourceHeap s ((s.2.heap.write u.entry.id u.object.data hu).write v.entry.id v.object.data _)) =
    (runInventoryUpdates rest).run (withSourceHeap s ((s.2.heap.write v.entry.id v.object.data hv).write u.entry.id u.object.data _))
  rw [heap_writes_commute _ _ _ _ _ hu hv distinct]

/-- Distinct actual root IDs, not pointer values or local variable names,
justify arbitrary permutations. Same-root aliases are handled separately. -/
theorem runInventoryUpdates_perm {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} {us vs : List (OwnedInventoryUpdate allocated p)}
    (perm : us.Perm vs) (distinct : (us.map (fun u => u.entry.id)).Nodup)
    (s : Source.EMState E Γ) (types : s.2.heap.ty = h.ty) :
    (runInventoryUpdates us).run s = (runInventoryUpdates vs).run s := by
  induction perm generalizing s with
  | nil => rfl
  | @cons u us vs perm ih =>
    have nd := (List.nodup_cons.mp distinct).2
    have ht : s.2.heap.ty u.entry.id = some u.entry.ty := types ▸ heap_ty_of_get h u.entry.id _ _ u.entry.found
    simp only [runInventoryUpdates,Source.Hoare.run_bind,heapPutConcrete_run s u.entry.id u.object.data ht]
    exact ih nd _ ((funext (fun a => Source.Heap.write_ty s.2.heap u.entry.id a u.object.data ht)).trans types)
  | swap u v rest =>
    have no := (List.nodup_cons.mp distinct).1
    exact runInventoryUpdates_swap _ _ rest s types (fun eq => no (List.mem_cons.mpr (Or.inl eq)))
  | @trans us vs ws one two ih1 ih2 =>
    exact (ih1 distinct s types).trans (ih2 ((one.map (fun u => u.entry.id)).nodup distinct) s types)

/-- Repeating the SAME decoded owned candidate is a real idempotent shared
object write. Different same-root values are NOT claimed to commute. -/
theorem runInventoryUpdates_repeat {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} (u : OwnedInventoryUpdate allocated p)
    (rest : List (OwnedInventoryUpdate allocated p)) (s : Source.EMState E Γ) (types : s.2.heap.ty = h.ty) :
    (runInventoryUpdates (u::u::rest)).run s = (runInventoryUpdates (u::rest)).run s := by
  have ht : s.2.heap.ty u.entry.id = some u.entry.ty := types ▸ heap_ty_of_get h u.entry.id _ _ u.entry.found
  let next := withSourceHeap s (s.2.heap.write u.entry.id u.object.data ht)
  have again : (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run next = (.ok (),next) := by
    rw [heapPutConcrete_run next u.entry.id u.object.data (by change (s.2.heap.write u.entry.id u.object.data ht).ty u.entry.id = some u.entry.ty; rw [Source.Heap.write_ty]; exact ht)]
    rw [heap_write_unchanged next.2.heap u.entry.id u.entry.ty u.object.data (Source.Heap.write_get s.2.heap u.entry.id u.object.data ht),withSourceHeap_unchanged]
  simp only [runInventoryUpdates,Source.Hoare.run_bind,heapPutConcrete_run s u.entry.id u.object.data ht]
  rw [again]

end Solidity.Yul.Views
