import Solidity.Backend.MemoryOps.CalldataNestedChildren

/-! Context/heap extension of actual child-table correspondence. The initial
Keeps fact is supplied by published allocation in controls. Only old represented
objects are transported; fresh-object representation is not assumed. -/
namespace Solidity.Backend.MemoryOps

set_option backward.isDefEq.respectTransparency false in
theorem BoolChildRepr.grow {D : Source.Layout} {H H' : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H} {hp' : Heap H'}
    {s : Source.Data D BoolChildTy} {r : HRef H BoolChildRef}
    (hr : BoolChildRepr c address hp s r) (e : H <+: H') (hk : Heap.Keeps e hp hp') :
    BoolChildRepr c address hp' s (r.wk e) := by
  refine ⟨hr.1, ?_⟩
  rw [hk r, MObj.elems_wk,
    List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
  exact hr.2

private theorem array_none_congr {D : Source.Layout} {τ : Source.STy} {n m : Nat}
    (h : n = m) (xs : Fin n → Source.Data D τ) (ys : Fin m → Source.Data D τ)
    (he : ∀ i (hi : i < n) (hj : i < m), xs ⟨i, hi⟩ = ys ⟨i, hj⟩) :
    (Source.Data.array n (fun _ h => by cases h) xs : Source.Data D (.array .calldata τ none)) =
      Source.Data.array m (fun _ h => by cases h) ys := by
  cases h
  have hf : xs = ys := by
    funext j
    exact he j.val j.isLt j.isLt
  cases hf
  rfl

/-- Existing child identities retain the same decoded pointer fields when the
intrinsic heap typing grows. No decoder or memory allocation is defined here. -/
theorem decodedChildRefs_wk {D : Source.Layout} {H H' : HTy} (e : H <+: H')
    (address : Nat → Nat) (rs : List (HRef H BoolChildRef)) :
    (decodedChildRefs (D := D) address (rs.map (HRef.wk e))) = decodedChildRefs address rs := by
  apply array_none_congr (List.length_map (HRef.wk e))
  intro i hi hj
  change (Source.Data.val (.cdRef rfl (address ((rs.map (HRef.wk e))[i]'hi).id) 0) : Source.Data D BoolChildTy) =
    .val (.cdRef rfl (address (rs[i]'hj).id) 0)
  rw [List.getElem_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem RefChildRepr.grow {D : Source.Layout} {H H' : HTy}
    {c : Source.Calldata D} {address : Nat → Nat} {hp : Heap H} {hp' : Heap H'}
    {s : Source.Data D RefChildTy} {r : HRef H RefChildRef}
    (hr : RefChildRepr c address hp s r) (e : H <+: H') (hk : Heap.Keeps e hp hp') :
    RefChildRepr c address hp' s (r.wk e) := by
  have he : MObj.elems .dyn (hp'.get (r.wk e)) =
      (MObj.elems .dyn (hp.get r)).map (HRef.wk e) := by
    rw [hk r, MObj.elems_wk]
    rfl
  refine ⟨hr.1, ?_, ?_⟩
  · rw [he, decodedChildRefs_wk]
    exact hr.2.1
  · intro q hq
    rw [he] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (hr.2.2 p hp).grow e hk

/-- info: 'Solidity.Backend.MemoryOps.BoolChildRepr.grow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms BoolChildRepr.grow
/-- info: 'Solidity.Backend.MemoryOps.decodedChildRefs_wk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decodedChildRefs_wk
/-- info: 'Solidity.Backend.MemoryOps.RefChildRepr.grow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RefChildRepr.grow
end Solidity.Backend.MemoryOps
