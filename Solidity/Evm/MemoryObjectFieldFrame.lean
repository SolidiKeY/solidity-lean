import Solidity.Evm.MemoryObjectValues
import Solidity.Evm.MemoryStructSource

/-! Primitive struct field writes frame every represented array kind and
reference element, including parents pointing at the updated struct. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

theorem cells_setStruct {H : HTy} (hp : Heap H) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) {Q : RefTy} (q : HRef H Q) :
    cells (hp.setField r hf v) q = cells hp q := by
  cases Q with
  | array E =>
    have he : r.id ≠ q.id := by intro he; cases (HRef.heq_of_id r q he).1
    simp only [cells, Heap.len, Heap.setField, Heap.get_set_ne hp r q he]
  | fixed E n => rfl
  | struct t => rfl
  | mapping k E => rfl

theorem HeapRepr.setStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    HeapRepr (hp.setField r hf v) base frame
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  have hoff := fieldOffset_bound hf
  have hsize : (structDef s).length ≤ cells hp r := Nat.le_max_right _ _
  refine ⟨⟨h.owner.above, ?_, ?_⟩, ?_, (h.structHeap.set r hf v w hw).objects,
    RefFieldsRepr.setPrimitive h.refs h.structHeap r hf v w⟩
  · intro Q q
    simpa only [cells_setStruct] using h.owner.space q
  · intro Q T q t hn
    simpa only [cells_setStruct] using h.owner.separated q t hn
  · intro A E a q
    have he : r.id ≠ q.id := by
      intro he
      exact (a.ne_struct s (HRef.heq_of_id r q he).1.symm).elim
    have hq := h.arrays a q
    have hd := h.owner.separated r q he
    have hpos := cells_pos hp q
    refine ⟨?_, ?_, ?_⟩
    · simpa only [cells_setStruct] using hq.space
    · intro hh
      change upd m.mem _ _ (base q.id).val = _
      rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
      simpa only [Heap.len, Heap.setField, Heap.get_set_ne hp r q he] using hq.length hh
    · intro i x hx
      simp only [Heap.setField, Heap.get_set_ne hp r q he] at hx
      have hi : i < hp.len q a := (List.getElem?_eq_some_iff.mp hx).1
      have hs := header_len_le_cells hp a q
      change ValueRepr base E x (upd m.mem _ _ _)
      rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
      exact hq.elements i x hx

variable {C : Contract}

theorem StateRepr.setStruct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {p : PrimTy}
    (r : HRef σ.H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StateRepr L b frame F (σ.withHeap (σ.heap.setField r hf v)) base
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  have old := h.legacy.setStruct r hf v w hw
  exact ⟨old.core, h.heap.setStruct r hf v w hw, old.pointers, old.locals⟩

theorem AllocatorRepr.setStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    AllocatorRepr (hp.setField r hf v) base frame cursor
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  refine ⟨h.heap.setStruct r hf v w hw, (h.legacy.setStruct r hf v w hw).arrays.free, ?_⟩
  intro Q q
  simpa only [cells_setStruct] using h.live q

end Solidity.Evm.Memory.Objects
