import Solidity.Evm.MemoryDefaultChildrenSim

/-! Actual source equations for arrays of typed reference defaults. -/
namespace Solidity.Evm.Memory.Objects

private theorem vectors_heq : {E : Ty} → {n m : Nat} →
    (xs : SVec E n) → (ys : SVec E m) → xs.toList = ys.toList → HEq xs ys
  | _, _, _, .nil, .nil, _ => HEq.rfl
  | _, _, _, .nil, .cons _ _, h => by
    rw [SVec.toList_nil, SVec.toList_cons] at h
    cases h
  | _, _, _, .cons _ _, .nil, h => by
    rw [SVec.toList_cons, SVec.toList_nil] at h
    cases h
  | _, _, _, .cons x xs, .cons y ys, h => by
    rw [SVec.toList_cons, SVec.toList_cons] at h
    have hx : x = y := (List.cons.inj h).1
    have hs : xs.toList = ys.toList := (List.cons.inj h).2
    subst y
    have hn := (SVec.length_toList xs).symm.trans
      ((congrArg List.length hs).trans (SVec.length_toList ys))
    cases hn
    have he : xs = ys := eq_of_heq (vectors_heq xs ys hs)
    cases he
    exact HEq.rfl
termination_by structural _E _n _m xs _ys _h => xs

private theorem arrays_eq_of_vectors {E : Ty} {n m : Nat} (xs : SVec E n) (ys : SVec E m)
    (he : n = m) (hv : HEq xs ys) (hn : n < W) (hm : m < W) :
    (SVal.array xs .nil hn : SVal (.ref (.array E))) = .array ys .nil hm := by
  cases he
  have hxy : xs = ys := eq_of_heq hv
  cases hxy
  rfl

theorem array_replicate_eq {E : Ty} (v : SVal E) (n : Nat)
    (hn : (List.replicate n v).length < W) (hm : n < W) :
    (SVal.array (SVec.ofList (List.replicate n v)) .nil hn : SVal (.ref (.array E))) =
      .array (SVec.replicate v n) .nil hm := by
  apply arrays_eq_of_vectors _ _ (List.length_replicate ..)
  apply vectors_heq
  rw [SVec.toList_ofList, SVec.toList_replicate]

def referenceArrayCopy {H : HTy} (hp : Heap H) (R : RefTy)
    (hm : (Ty.ref R).mapFree = true) (size : Fin W) :
    Grown H (MVal · (.ref (.array (.ref R)))) :=
  let g := defaultChildrenCopy hp R hm size.val
  Grown.alloc ⟨g.ext, g.heap, ⟨g.val.1, by rw [g.val.2]; exact size.isLt⟩⟩

theorem referenceArrayCopy_source {H : HTy} (hp : Heap H) (R : RefTy) (size : Fin W)
    (hn : (RefTy.array (.ref R)).newArrOk = true) (hm : (Ty.ref R).mapFree = true) :
    (newArrT (.array (.ref R)) (indexValue size) hn).copyStToM hp
      (RefTy.mapFree_of_newArrOk hn) = referenceArrayCopy hp R hm size := by
  rw [newArrT]
  simp only [indexValue, Int.toNat_natCast]
  rw [array_replicate_eq _ _ _ size.isLt, SVal.copyStToM_array]
  rfl

def referenceFixedCopy {H : HTy} (hp : Heap H) (R : RefTy)
    (hm : (Ty.ref R).mapFree = true) (n : Nat) :
    Grown H (MVal · (.ref (.fixed (.ref R) n))) :=
  Grown.alloc (defaultChildrenCopy hp R hm n)

theorem referenceFixedCopy_source {H : HTy} (hp : Heap H) (R : RefTy) (n : Nat)
    (hm : (Ty.ref R).mapFree = true) :
    hp.allocDefault (.fixed (.ref R) n) hm = referenceFixedCopy hp R hm n := by
  rw [Heap.allocDefault, SVal.dflt_fixed, SVal.copyStToM_fixed]
  rfl

/-- Reserve a headerless fixed parent without pretending it is already in the source heap. -/
theorem AllocatorRepr.reserveFixed {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (n : Nat)
    (hs : cursor.val + max 1 n < W) :
    AllocatorRepr hp base frame ⟨cursor.val + max 1 n, hs⟩
      (allocateStructMachine m cursor (max 1 n)) ∧
      Gap hp base cursor.val (cursor.val + max 1 n) := by
  refine ⟨⟨?_, h.free.allocateStruct (max 1 n) hs, ?_⟩, fun r => .inl (h.live r)⟩
  · apply h.heap.writeOutside 0 _
    intro Q q
    have hq := h.heap.owner.above q
    have hf := h.free.reserved
    exact .inl (by omega)
  · intro Q q
    change (base q.id).val + cells hp q ≤ cursor.val + max 1 n
    exact Nat.le_trans (h.live q) (by omega)

end Solidity.Evm.Memory.Objects
