import Solidity.Evm.MemoryObjectFlatStruct

/-! Primitive fixed-array defaults reuse the actual typed source copy fold;
the target is headerless and reserves one padding cell for an empty object. -/
namespace Solidity.Evm.Memory.Objects

def defaultFixed {H : HTy} (p : PrimTy) (n : Nat) : MObj H (.fixed (.prim p) n) :=
  ⟨List.replicate n p.dflt, List.length_replicate ..⟩

private theorem copyPrimitiveDefaults {H : HTy} (hp : Heap H) (p : PrimTy) (n : Nat) :
    (SVec.replicate (SVal.prim p.dflt) n).copyStToM hp rfl =
      ⟨List.prefix_refl H, hp, ⟨List.replicate n p.dflt, List.length_replicate ..⟩⟩ := by
  induction n with
  | zero => simp only [SVec.replicate, SVec.copyStToM_nil, List.replicate_zero]
  | succ n ih =>
    simp only [SVec.replicate, SVec.copyStToM_cons, SVal.copyStToM_prim, List.replicate_succ]
    with_unfolding_all exact (Grown.prims_cons hp p.dflt (List.replicate n p.dflt)
      _ (List.length_replicate ..) ih _ _ _)

theorem defaultFixed_copy {H : HTy} (hp : Heap H) (p : PrimTy) (n : Nat) :
    hp.allocDefault (.fixed (.prim p) n) rfl =
      Grown.alloc ⟨List.prefix_refl H, hp, defaultFixed p n⟩ := by
  rw [Heap.allocDefault, SVal.dflt_fixed, SVal.dflt_prim, SVal.copyStToM_fixed,
    copyPrimitiveDefaults]
  rfl

/-- Full object ownership survives a fresh primitive fixed-array default. -/
theorem AllocatorRepr.allocateFixedPrimitive {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (p : PrimTy) (n : Nat)
    (hs : cursor.val + max 1 n < W) :
    AllocatorRepr (hp.alloc (R := .fixed (.prim p) n) (defaultFixed (H := H) p n)).1
      (upd base H.length cursor) frame ⟨cursor.val + max 1 n, hs⟩
      (allocateStructMachine m cursor (max 1 n)) := by
  let o : MObj H (.fixed (.prim p) n) := defaultFixed p n
  let size := max 1 n
  have hz : 0 < cursor.val := Nat.lt_of_lt_of_le h.free.reserved h.free.above
  have hf : ArrayRepr (hp.alloc o).1 (hp.alloc o).2 .fixed (upd base H.length cursor)
      (allocateStructMachine m cursor size) := by
    refine ⟨?_, ?_, ?_⟩
    · change (upd base H.length cursor H.length).val + max 1 n ≤ W
      rw [upd_same]
      omega
    · intro hh
      cases hh
    · intro i v hv
      simp only [Heap.get_alloc, MObj.elems_fixed, MObj.wk, o, defaultFixed,
        List.map_replicate] at hv
      obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hv
      simp only [List.getElem_replicate, MVal.wk] at he
      subst v
      change ReprV p p.dflt ((allocateStructMachine m cursor size).mem
        ((upd base H.length cursor H.length).val + 0 + i))
      rw [upd_same, Nat.add_zero, allocateStructMachine_other m cursor size _ (by omega),
        h.free.zero _ (by omega)]
      exact ReprV.dflt_zero p
  have hh : HeapRepr hp base frame (allocateStructMachine m cursor size) := by
    apply h.heap.writeOutside 0 _
    intro Q q
    have hq := h.heap.owner.above q
    have hf := h.free.reserved
    exact .inl (by omega)
  refine ⟨hh.adoptArray .fixed o cursor h.free.above hf (fun q => .inl (h.live q)),
    h.free.allocateStruct size hs, ?_⟩
  let e := List.prefix_append H [.fixed (.prim p) n]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  intro Q q
  rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
  · change (upd base H.length cursor q.id).val + cells (hp.alloc o).1 (q.wk e) ≤ cursor.val + size
    rw [allocationBase_old base cursor q, cells_keeps e hk]
    exact Nat.le_trans (h.live q) (by omega)
  · cases ht; cases he
    change (upd base H.length cursor H.length).val + max 1 n ≤ cursor.val + size
    rw [upd_same]
    exact Nat.le_refl _

end Solidity.Evm.Memory.Objects
