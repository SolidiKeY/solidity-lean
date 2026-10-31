import Solidity.Evm.MemoryObjectReserve
import Solidity.Evm.MemoryStructDefault

/-! Single primitive-member struct defaults under complete object ownership.
Reference-bearing struct construction is deliberately excluded. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

def objectCells {H : HTy} : {R : RefTy} → MObj H R → Nat
  | .array _, o => 1 + o.val.length
  | .fixed _ n, _ => max 1 n
  | .struct s, _ => max 1 (structDef s).length
  | .mapping .., _ => 1

theorem cells_alloc_fresh {H : HTy} (hp : Heap H) {R : RefTy} (o : MObj H R) :
    cells (hp.alloc o).1 (hp.alloc o).2 = objectCells o := by
  cases R with
  | array E => simp only [cells, objectCells, Heap.len, Heap.get_alloc, MObj.elems_dyn,
      MObj.wk, List.length_map]
  | fixed E n => rfl
  | struct s => rfl
  | mapping k E => rfl

theorem Ownership.adopt {H : HTy} {hp : Heap H} {base : Nat → Fin W} {frame : Nat}
    (h : Ownership hp base frame) {R : RefTy} (o : MObj H R) (addr : Fin W)
    (ha : frame ≤ addr.val) (hs : addr.val + objectCells o ≤ W)
    (hd : ∀ {Q : RefTy} (q : HRef H Q), (base q.id).val + cells hp q ≤ addr.val ∨
      addr.val + objectCells o ≤ (base q.id).val) :
    Ownership (hp.alloc o).1 (upd base H.length addr) frame := by
  let e := List.prefix_append H [R]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  have oldbase {Q : RefTy} (q : HRef H Q) : upd base H.length addr (q.wk e).id = base q.id :=
    allocationBase_old base addr q
  have fresh : (hp.alloc o).2.id = H.length := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro Q q
    rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
    · rw [oldbase]; exact h.above q
    · cases ht; cases he; simpa only [fresh, upd_same] using ha
  · intro Q q
    rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
    · rw [oldbase, cells_keeps e hk]; exact h.space q
    · cases ht; cases he; simpa only [fresh, upd_same, cells_alloc_fresh] using hs
  · intro Q T q t hn
    rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
    · rcases allocRef_split hp o t with ⟨t, rfl⟩ | ⟨ht, he⟩
      · simpa only [oldbase, cells_keeps e hk] using h.separated q t hn
      · cases ht; cases he
        simpa only [oldbase, cells_keeps e hk, fresh, upd_same, cells_alloc_fresh] using hd q
    · cases ht; cases he
      rcases allocRef_split hp o t with ⟨t, rfl⟩ | ⟨ht, he⟩
      · simpa only [oldbase, cells_keeps e hk, fresh, upd_same, cells_alloc_fresh] using (hd t).symm
      · cases ht; cases he; exact (hn rfl).elim

/-- Fresh objects at or after a gap's end retain that gap. -/
theorem Gap.adoptSingle {H : HTy} {hp : Heap H} {base : Nat → Fin W} {lo hi : Nat}
    (h : Gap hp base lo hi) {R : RefTy} (o : MObj H R) (addr : Fin W) (ha : hi ≤ addr.val) :
    Gap (hp.alloc o).1 (upd base H.length addr) lo hi := by
  let e := List.prefix_append H [R]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  intro Q q
  rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
  · change (upd base H.length addr q.id).val + cells (hp.alloc o).1 (q.wk e) ≤ lo ∨
      hi ≤ (upd base H.length addr q.id).val
    rw [allocationBase_old base addr q, cells_keeps e hk]
    exact h q
  · cases ht; cases he; simpa only [Heap.alloc, HRef.id, upd_same] using Or.inr ha

/-- Existing arrays of either element sort and kind survive primitive struct adoption. -/
theorem HeapRepr.adoptPrimitiveStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) {s : Name}
    (o : MObj H (.struct s)) (hpfields : primitiveMembers (structDef s) = true) (addr : Fin W)
    (ha : frame ≤ addr.val) (hs : addr.val + objectCells o ≤ W)
    (hf : StructRepr (hp.alloc o).1 (hp.alloc o).2 addr m)
    (hd : ∀ {Q : RefTy} (q : HRef H Q), (base q.id).val + cells hp q ≤ addr.val ∨
      addr.val + objectCells o ≤ (base q.id).val) :
    HeapRepr (hp.alloc o).1 (upd base H.length addr) frame m := by
  let e := List.prefix_append H [.struct s]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  have hb : BaseExtends H base (upd base H.length addr) := fun r => allocationBase_old base addr r
  refine ⟨h.owner.adopt o addr ha hs hd, ?_, ?_, ?_⟩
  · intro A E a r
    rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
    · exact (h.arrays a q).keeps e hk hb
    · exact (a.ne_struct s ht).elim
  · intro t r
    rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
    · change StructRepr (hp.alloc o).1 (q.wk e) (upd base H.length addr q.id) m
      rw [allocationBase_old base addr q]
      exact (h.structs q).keeps e hk
    · cases ht; cases he
      simpa only [Heap.alloc, HRef.id, upd_same] using hf
  · exact RefFieldsRepr.alloc h.refs o addr (fun _ _ => rfl)
      (fun ht hf => by cases ht; exact primitiveMembers_noRef hpfields hf)

/-- The existing primitive-struct default object is allocated with positive padding. -/
theorem AllocatorRepr.allocatePrimitiveStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) {s : Name}
    (hprim : primitiveMembers (structDef s) = true) (hm : (Ty.ref (.struct s)).mapFree = true)
    (hs : cursor.val + structAllocationSize s < W) :
    AllocatorRepr (hp.alloc (R := .struct s) (defaultFields (H := H) (structDef s) hprim)).1 (upd base H.length cursor)
      frame ⟨cursor.val + structAllocationSize s, hs⟩ (allocateStructMachine m cursor (structAllocationSize s)) := by
  let o : MObj H (.struct s) := defaultFields (structDef s) hprim
  let size := structAllocationSize s
  have hz : 0 < cursor.val := Nat.lt_of_lt_of_le h.free.reserved h.free.above
  have hfields : (structDef s).length ≤ size := Nat.le_max_right _ _
  have hf₀ := h.free.struct hp o (defaultFields_defaults hp hprim hm) (by omega)
  have hf : StructRepr (hp.alloc o).1 (hp.alloc o).2 cursor (allocateStructMachine m cursor size) := by
    refine ⟨hf₀.space, ?_⟩
    intro f p ht
    have haddr : 0 < cursor.val + fieldOffset (structDef s) f := by omega
    have he : (allocateStructMachine m cursor size).mem (cursor.val + fieldOffset (structDef s) f) =
        (allocateStructMachine m cursor (structDef s).length).mem (cursor.val + fieldOffset (structDef s) f) :=
      (allocateStructMachine_other _ _ _ _ (by omega)).trans
        (allocateStructMachine_other _ _ _ _ (by omega)).symm
    change ReprV p _ ((allocateStructMachine m cursor size).mem _)
    rw [he]
    exact hf₀.fields ht
  have hheap : HeapRepr hp base frame (allocateStructMachine m cursor size) := by
    apply h.heap.writeOutside 0 _
    intro Q q
    have hb := h.heap.owner.above q
    have hf := h.free.reserved
    exact .inl (by omega)
  refine ⟨hheap.adoptPrimitiveStruct o hprim cursor h.free.above (by
      change cursor.val + size ≤ W; omega) hf (fun q => .inl (h.live q)),
    h.free.allocateStruct size hs, ?_⟩
  let e := List.prefix_append H [.struct s]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  intro Q q
  rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
  · change (upd base H.length cursor q.id).val + cells (hp.alloc o).1 (q.wk e) ≤ cursor.val + size
    rw [allocationBase_old base cursor q, cells_keeps e hk]
    exact Nat.le_trans (h.live q) (by omega)
  · cases ht; cases he
    change (upd base H.length cursor H.length).val + cells (hp.alloc o).1 (hp.alloc o).2 ≤ cursor.val + size
    rw [upd_same, cells_alloc_fresh]
    exact Nat.le_refl _

end Solidity.Evm.Memory.Objects
