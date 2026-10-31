import Solidity.Evm.MemoryObjectEmpty

/-! Parent reservations are gaps in the typed heap until children have been
constructed. Actual objects remain disjoint from the whole reserved interval. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

def Gap {H : HTy} (hp : Heap H) (base : Nat → Fin W) (lo hi : Nat) : Prop :=
  ∀ {R : RefTy} (r : HRef H R),
    (base r.id).val + cells hp r ≤ lo ∨ hi ≤ (base r.id).val

/-- Reserve the parent before source children, without inventing a typed parent. -/
theorem AllocatorRepr.reserveArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (n : Fin W)
    (hs : cursor.val + n.val + 1 < W) :
    AllocatorRepr hp base frame ⟨cursor.val + n.val + 1, hs⟩
      (allocateMachine m cursor n) ∧ Gap hp base cursor.val (cursor.val + n.val + 1) := by
  refine ⟨⟨h.headerOutside n, h.free.allocate n hs, ?_⟩, fun r => .inl (h.live r)⟩
  intro R r
  change (base r.id).val + cells hp r ≤ cursor.val + n.val + 1
  exact Nat.le_trans (h.live r) (by omega)

/-- Writing a pointer into a reserved parent touches no represented object. -/
theorem AllocatorRepr.writeGap {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) {lo hi addr : Nat}
    (hg : Gap hp base lo hi) (ha : lo ≤ addr) (hb : addr < hi)
    (hz : 0 < addr) (hc : hi ≤ cursor.val) (w : Word) :
    AllocatorRepr hp base frame cursor (writeMachine m addr w) := by
  refine ⟨h.heap.writeOutside addr w ?_, ?_, h.live⟩
  · intro R r
    rcases hg r with hr | hr
    · exact .inr (by omega)
    · exact .inl (by omega)
  · refine ⟨h.free.reserved, h.free.above, ?_, ?_⟩
    · exact (upd_other _ _ (by omega)).trans h.free.cell
    · intro a he
      exact (upd_other _ _ (by omega)).trans (h.free.zero a he)

/-- Fresh empty children are beyond the reserved parent; old bases are retained. -/
theorem Gap.allocateEmpty {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {lo hi : Nat} (h : Gap hp base lo hi) (E : Ty) (cursor : Fin W)
    (hc : hi ≤ cursor.val) :
    Gap (hp.alloc (emptyArray E)).1 (upd base H.length cursor) lo hi := by
  let o := emptyArray (H := H) E
  let e := List.prefix_append H [.array E]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  intro R r
  rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
  · change (upd base H.length cursor q.id).val + cells (hp.alloc o).1 (q.wk e) ≤ lo ∨
      hi ≤ (upd base H.length cursor q.id).val
    rw [upd_other base cursor (Nat.ne_of_lt q.id_lt), cells_keeps e hk]
    exact h q
  · cases ht; cases he
    exact .inr (by simpa only [Heap.alloc, HRef.id, upd_same] using hc)

/-- Adopt the parent after its children, keeping the already advanced cursor. -/
theorem AllocatorRepr.adoptReservedArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) {A : RefTy} {E : Ty}
    (a : ArrTy A E) (o : MObj H A) (addr : Fin W) (ha : frame ≤ addr.val)
    (hf : ArrayRepr (hp.alloc o).1 (hp.alloc o).2 a (upd base H.length addr) m)
    (hl : addr.val + cells (hp.alloc o).1 (hp.alloc o).2 ≤ cursor.val)
    (hg : Gap hp base addr.val (addr.val + cells (hp.alloc o).1 (hp.alloc o).2)) :
    AllocatorRepr (hp.alloc o).1 (upd base H.length addr) frame cursor m := by
  let e := List.prefix_append H [A]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  refine ⟨h.heap.adoptArray a o addr ha hf hg, h.free, ?_⟩
  intro R r
  rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
  · change (upd base H.length addr q.id).val + cells (hp.alloc o).1 (q.wk e) ≤ cursor.val
    rw [upd_other base addr (Nat.ne_of_lt q.id_lt), cells_keeps e hk]
    exact h.live q
  · cases ht; cases he
    simpa only [Heap.alloc, HRef.id, upd_same] using hl

end Solidity.Evm.Memory.Objects
