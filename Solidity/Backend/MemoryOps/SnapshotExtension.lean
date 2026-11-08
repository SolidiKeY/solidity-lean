import Solidity.Backend.MemoryOps.HeapSnapshot

/-! Naturality of the actual heap overwrite adapter under preserving growth. -/
namespace Solidity.Backend.MemoryOps

theorem replaceSlice_map {α β : Type} (f : α → β) (xs payload : List α) (dst : Nat) :
    replaceSlice (xs.map f) dst (payload.map f) = (replaceSlice xs dst payload).map f := by
  simp only [replaceSlice, List.map_take, List.map_drop, List.length_map, List.map_append]

theorem withElems_wk {H H' : HTy} {R : RefTy} {E : Ty} (e : H <+: H')
    (a : ArrTy R E) (o : MObj H R) (xs : List (MVal H E))
    (hl : xs.length = (MObj.elems a o).length) :
    MObj.wk e R (withElems a o xs hl) =
      withElems a (MObj.wk e R o) (xs.map (MVal.wk e E))
        (by rw [List.length_map, MObj.elems_wk, List.length_map]; exact hl) := by
  cases a <;> apply Subtype.ext <;> rfl

/-- Capacity is transported, not assumed again, for the weakened overwrite. -/
theorem overwriteSlice_space {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (dst : Nat) (payload : List (MVal H E))
    (h : dst + payload.length ≤ hp.len r a) :
    dst + (payload.map (MVal.wk e E)).length ≤ hp'.len (r.wk e) a := by
  simpa only [Heap.len, hk r, MObj.elems_wk, List.length_map] using h

/-- Overwrite and heap extension commute at every older object, retaining
reference-containing shapes and all nested child identities. -/
theorem overwriteSlice_keeps {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (dst : Nat) (payload : List (MVal H E))
    (h : dst + payload.length ≤ hp.len r a) :
    Heap.Keeps e (overwriteSlice hp r a dst payload h)
      (overwriteSlice hp' (r.wk e) a dst (payload.map (MVal.wk e E))
        (overwriteSlice_space e hk r a dst payload h)) := by
  intro Q q
  by_cases he : r.id = q.id
  · obtain ⟨rfl, hh⟩ := HRef.heq_of_id r q he
    cases hh
    simp only [overwriteSlice, Heap.get_set_same, hk r, MObj.elems_wk, replaceSlice_map]
    exact (withElems_wk e a (hp.get r)
      (replaceSlice (MObj.elems a (hp.get r)) dst payload)
      (replaceSlice_length _ _ _ h)).symm
  · simp only [overwriteSlice]
    rw [Heap.get_set_ne hp' (r.wk e) (q.wk e) he, Heap.get_set_ne hp r q he]
    exact hk q

/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_keeps
/-- info: 'Solidity.Backend.MemoryOps.withElems_wk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms withElems_wk

end Solidity.Backend.MemoryOps
