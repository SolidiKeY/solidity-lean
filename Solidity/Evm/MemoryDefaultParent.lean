import Solidity.Evm.MemoryDefaultArraySource

/-! Late adoption of a typed dynamic or fixed reference parent after its actual
source children have been copied and their target pointers stored. -/
namespace Solidity.Evm.Memory.Objects

theorem objectCells_array {H : HTy} {A : RefTy} {E : Ty}
    (a : ArrTy A E) (o : MObj H A) :
    objectCells o = max 1 (header a + (MObj.elems a o).length) := by
  cases a with
  | dyn =>
    rw [MObj.elems_dyn]
    change 1 + o.val.length = max 1 (1 + o.val.length)
    omega
  | @fixed E n =>
    rw [MObj.elems_fixed]
    change max 1 n = max 1 (0 + o.val.length)
    rw [o.property, Nat.zero_add]

/-- This helper assumes the actual typed child list, not primitive-only contents. -/
theorem AllocatorRepr.adoptDefaultParent {H : HTy} {R : RefTy} {n : Nat}
    (g : Grown H (fun H' => {ls : List (HRef H' R) // ls.length = n}))
    {base : Nat → Fin W} {frame : Nat} {cursor parent : Fin W} {m : Machine}
    (ha : AllocatorRepr g.heap base frame cursor m) {A : RefTy}
    (a : ArrTy A (.ref R)) (o : MObj g.H' A) (ho : MObj.elems a o = g.val.1)
    (hpframe : frame ≤ parent.val)
    (hg : Gap g.heap base parent.val (parent.val + max 1 (header a + n)))
    (hspace : parent.val + max 1 (header a + n) ≤ cursor.val)
    (hheader : header a = 1 → m.mem parent.val = .val (wmod n))
    (helems : ∀ i v, g.val.1[i]? = some v →
      m.mem (parent.val + header a + i) = .val (base v.id)) :
    AllocatorRepr (g.heap.alloc o).1 (upd base g.H'.length parent) frame cursor m := by
  have hc : cells (g.heap.alloc o).1 (g.heap.alloc o).2 = max 1 (header a + n) := by
    rw [cells_alloc_fresh, objectCells_array a o, ho, g.val.2]
  have hn : (g.heap.alloc o).1.len (g.heap.alloc o).2 a = n := by
    simp only [Heap.len, Heap.get_alloc, MObj.elems_wk, List.length_map, ho, g.val.2]
  have hf : ArrayRepr (g.heap.alloc o).1 (g.heap.alloc o).2 a (upd base g.H'.length parent) m := by
    refine ⟨?_, ?_, ?_⟩
    · change (upd base g.H'.length parent g.H'.length).val + cells (g.heap.alloc o).1 (g.heap.alloc o).2 ≤ W
      rw [upd_same, hc]
      exact Nat.le_trans hspace (Nat.le_of_lt cursor.isLt)
    · intro hh
      change m.mem (upd base g.H'.length parent g.H'.length).val = _
      rw [upd_same, hn]
      exact hheader hh
    · intro i v hv
      simp only [Heap.get_alloc, MObj.elems_wk, ho, List.getElem?_map] at hv
      let e := List.prefix_append g.H' [A]
      change (g.val.1[i]?).map (HRef.wk e) = some v at hv
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hv
      change m.mem ((upd base g.H'.length parent g.H'.length).val + header a + i) =
        .val (upd base g.H'.length parent x.id)
      rw [upd_same, allocationBase_old base parent x]
      exact helems i x hx
  apply ha.adoptReservedArray a o parent hpframe hf
  · simpa only [hc] using hspace
  · intro Q q
    simpa only [hc] using hg q

/-- A finite loop witness gives the actual target outcome before its two control pops. -/
theorem defaultLoop_exit {body : List Instr} {m m' : Machine} {k : Nat}
    (h : loopIterN (run childrenCondition) (run body) k m = .inr (.ok m' 0)) :
    run [.loop childrenCondition body, .pop, .pop] m = run [.pop, .pop] m' := by
  change (loopRun (run childrenCondition) (run body) m).bind _ = _
  rw [loopRun_of_iterN h]
  rfl

end Solidity.Evm.Memory.Objects
