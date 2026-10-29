import Solidity.Evm.MemoryObjectFrame

/-! The bump allocator owns every live typed object interval. In particular,
a zero-length reference array cannot occupy the supposedly free zero tail.
The old primitive/struct allocator is recovered as a proved projection. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

theorem HeapRepr.mem_eq {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m m' : Machine} (h : HeapRepr hp base frame m) (hm : m'.mem = m.mem) :
    HeapRepr hp base frame m' := by
  refine ⟨h.owner, ?_, ?_, RefFieldsRepr.mem_eq h.refs hm⟩
  · intro A E a r
    refine ⟨(h.arrays a r).space, ?_, ?_⟩
    · intro hh
      exact (congrFun hm _).trans ((h.arrays a r).length hh)
    · intro i v hv
      change ValueRepr base E v (m'.mem _)
      rw [hm]
      exact (h.arrays a r).elements i v hv
  · intro s r
    refine ⟨(h.structs r).space, ?_⟩
    intro f p hf
    change ReprV p _ (m'.mem _)
    rw [hm]
    exact (h.structs r).fields hf

structure AllocatorRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (m : Machine) : Prop where
  heap : HeapRepr hp base frame m
  free : FreeMemory frame cursor m
  live : ∀ {R : RefTy} (r : HRef H R), (base r.id).val + cells hp r ≤ cursor.val

/-- All older primitive/struct allocator APIs remain available. -/
theorem AllocatorRepr.legacy {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) :
    StructAllocatorRepr hp base frame cursor m := by
  refine ⟨⟨h.heap.primitive, h.free, ?_⟩, h.heap.structHeap,
    h.heap.structArraySeparated, ?_⟩
  · intro p r
    simpa only [cells, Nat.add_assoc] using h.live r
  · intro s r
    have hr := h.live r
    have hs : (structDef s).length ≤ max 1 (structDef s).length := Nat.le_max_right _ _
    simp only [cells] at hr
    omega

theorem AllocatorRepr.mem_eq {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m m' : Machine}
    (h : AllocatorRepr hp base frame cursor m) (hm : m'.mem = m.mem) :
    AllocatorRepr hp base frame cursor m' :=
  ⟨h.heap.mem_eq hm,
    ⟨h.free.reserved, h.free.above, (congrFun hm _).trans h.free.cell,
      fun addr ha => (congrFun hm _).trans (h.free.zero addr ha)⟩, h.live⟩

theorem AllocatorRepr.stack {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (st : List Word) :
    AllocatorRepr hp base frame cursor {m with stack := st} := h.mem_eq rfl

theorem AllocatorRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (l : Nat) (hz : 0 < l)
    (hl : l < frame) (w : Word) :
    AllocatorRepr hp base frame cursor (writeMachine m l w) := by
  refine ⟨h.heap.localWrite l hl w, ?_, h.live⟩
  refine ⟨h.free.reserved, h.free.above, ?_, ?_⟩
  · exact (upd_other _ _ (by omega)).trans h.free.cell
  · intro addr ha
    have hb := h.free.above
    exact (upd_other _ _ (by omega)).trans (h.free.zero addr ha)

/-- Both array layouts, at either element sort, preserve the cursor and free tail. -/
theorem AllocatorRepr.setArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) {A : RefTy} {E : Ty}
    (r : HRef H A) (a : ArrTy A E) (i : Nat) (hi : i < hp.len r a)
    (v : MVal H E) (w : Word) (hw : ValueRepr base E v w) :
    AllocatorRepr (hp.set r (MObj.setElem a (hp.get r) i v)) base frame cursor
      (writeMachine m ((base r.id).val + header a + i) w) := by
  have hb := h.heap.owner.above r
  have hz := h.free.reserved
  have hs := header_len_le_cells hp a r
  have hl := h.live r
  refine ⟨h.heap.setArray r a i hi v w hw, ?_, ?_⟩
  · refine ⟨h.free.reserved, h.free.above, ?_, ?_⟩
    · exact (upd_other _ _ (by omega)).trans h.free.cell
    · intro addr ha
      exact (upd_other _ _ (by omega)).trans (h.free.zero addr ha)
  · intro Q q
    simpa only [cells_set] using h.live q

/-- The reservation of an old object prevents a fresh header from touching it. -/
theorem AllocatorRepr.headerOutside {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (size : Fin W) :
    HeapRepr hp base frame (allocateMachine m cursor size) := by
  apply (h.heap.writeOutside cursor.val (.val size) (fun r => .inr (h.live r))).writeOutside
    0 (.val (wmod (cursor.val + size.val + 1)))
  intro R r
  have hb := h.heap.owner.above r
  have hz := h.free.reserved
  exact .inl (by omega)

variable {C : Contract}

/-- Capacity is needed only for a reached allocation, as in the existing compiler. -/
def AllocationInput {Γ : Ctx} (b frame cost : Nat) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) : Prop :=
  cost = 0 ∨ (0 < b ∧ ∃ cursor, AllocatorRepr σ.heap base frame cursor m ∧
    cursor.val + cost < W)

/-- Exact cursor growth uses the complete object allocator, including fixed arrays. -/
def GrowsAllocator {Γ Δ : Ctx} (b frame cost : Nat) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (τ : State C Δ)
    (base' : Nat → Fin W) (m' : Machine) : Prop :=
  ∀ cursor, 0 < b → AllocatorRepr σ.heap base frame cursor m →
    ∀ hspace : cursor.val + cost < W,
      AllocatorRepr τ.heap base' frame ⟨cursor.val + cost, hspace⟩ m'

/-- Nonallocating code preserves a supplied complete allocator. -/
def KeepsAllocator {Γ Δ : Ctx} (b frame : Nat) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (τ : State C Δ) (m' : Machine) : Prop :=
  ∀ cursor, 0 < b → AllocatorRepr σ.heap base frame cursor m →
    AllocatorRepr τ.heap base frame cursor m'

theorem AllocationInput.of_le {Γ : Ctx} {b frame cost budget : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : AllocationInput b frame budget σ base m) (hle : cost ≤ budget) :
    AllocationInput b frame cost σ base m := by
  rcases h with h | ⟨hb, c, ha, hs⟩
  · exact .inl (by omega)
  · exact .inr ⟨hb, c, ha, by omega⟩

theorem GrowsAllocator.comp {Γ Δ Ξ : Ctx} {b frame head tail : Nat}
    {σ : State C Γ} {τ : State C Δ} {υ : State C Ξ}
    {base base' base'' : Nat → Fin W} {m m' m'' : Machine}
    (h : GrowsAllocator b frame head σ base m τ base' m')
    (h' : GrowsAllocator b frame tail τ base' m' υ base'' m'') :
    GrowsAllocator b frame (head + tail) σ base m υ base'' m'' := by
  intro c hb ha hs
  have hh : c.val + head < W := by omega
  have ht : (c.val + head) + tail < W := by omega
  simpa only [Nat.add_assoc] using h' ⟨c.val + head, hh⟩ hb (h c hb ha hh) ht

theorem GrowsAllocator.nextInput {Γ Δ : Ctx} {b frame head tail : Nat}
    {σ : State C Γ} {τ : State C Δ} {base base' : Nat → Fin W} {m m' : Machine}
    (h : GrowsAllocator b frame head σ base m τ base' m')
    (hi : AllocationInput b frame (head + tail) σ base m) :
    AllocationInput b frame tail τ base' m' := by
  rcases hi with hz | ⟨hb, c, ha, hs⟩
  · exact .inl (by omega)
  · have hh : c.val + head < W := by omega
    exact .inr ⟨hb, ⟨c.val + head, hh⟩, h c hb ha hh, by simpa only [Nat.add_assoc] using hs⟩

end Solidity.Evm.Memory.Objects
