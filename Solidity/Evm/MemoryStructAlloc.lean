import Solidity.Evm.MemoryStructHeap
import Solidity.Evm.MemoryAlloc

/-!
# Allocator ownership of represented structs

An array-only allocator may regard a zero-valued struct as unused zero tail.
Before compiling struct writes, its live intervals must therefore include
structs as well. This stronger relation preserves both layouts, their cross-
separation and the zero tail across local, array and struct-field writes.
Typed allocation and the source compiler build on this representation layer.
-/
namespace Solidity.Evm.Memory
open Semantics

structure StructAllocatorRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (m : Machine) : Prop where
  arrays : AllocatorRepr hp base frame cursor m
  structs : StructHeapRepr hp base frame m
  separated : StructArraySeparated hp base
  live : ∀ {s : Name} (r : HRef H (.struct s)),
    (base r.id).val + (structDef s).length ≤ cursor.val

/-- Storage and stack changes keep all represented memory and ownership. -/
theorem StructAllocatorRepr.mem_eq {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m m' : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) (hm : m'.mem = m.mem) :
    StructAllocatorRepr hp base frame cursor m' := by
  refine ⟨h.arrays.mem_eq hm, ⟨?_, h.structs.above, h.structs.separated⟩, h.separated, h.live⟩
  intro s r
  exact ⟨(h.structs.objects r).space, fun hf => hm ▸ (h.structs.objects r).fields hf⟩

/-- Array-only initial heaps inhabit the stronger invariant without struct regions. -/
theorem AllocatorRepr.withoutStructs {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m)
    (hn : ∀ {s : Name}, HRef H (.struct s) → False) :
    StructAllocatorRepr hp base frame cursor m :=
  ⟨h, ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r => (hn r).elim⟩,
    fun _ r => (hn r).elim, fun r => (hn r).elim⟩

theorem StructAllocatorRepr.stack {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) (st : List Word) :
    StructAllocatorRepr hp base frame cursor {m with stack := st} :=
  ⟨⟨⟨fun r => (h.arrays.heap.arrays r).stack st,
      h.arrays.heap.above, h.arrays.heap.separated⟩,
      ⟨h.arrays.free.reserved, h.arrays.free.above, h.arrays.free.cell, h.arrays.free.zero⟩, h.arrays.live⟩, h.structs.stack st, h.separated, h.live⟩

theorem StructAllocatorRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) (l : Nat) (hz : 0 < l)
    (hl : l < frame) (w : Word) :
    StructAllocatorRepr hp base frame cursor (writeMachine m l w) :=
  ⟨h.arrays.localWrite l hz hl w, h.structs.localWrite l hl w, h.separated, h.live⟩

/-- A live struct write keeps the allocator's cursor and zero tail. -/
theorem StructAllocatorRepr.setStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StructAllocatorRepr (hp.setField r hf v) base frame cursor
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
  have hl : (base r.id).val + (structDef s).length ≤ cursor.val := h.live r
  have hb : frame ≤ (base r.id).val := h.structs.above r
  have hz : 0 < frame := h.arrays.free.reserved
  refine ⟨⟨h.arrays.heap.structWrite h.separated r hf v w, ?_, ?_⟩,
    h.structs.set r hf v w hw, StructArraySeparated.setStruct h.separated r hf v, h.live⟩
  · refine ⟨h.arrays.free.reserved, h.arrays.free.above, ?_, ?_⟩
    · change upd m.mem ((base r.id).val + fieldOffset (structDef s) f) w 0 = .val cursor
      rw [upd_other _ _ (by omega)]
      exact h.arrays.free.cell
    · intro addr ha
      change upd m.mem ((base r.id).val + fieldOffset (structDef s) f) w addr = w[0]
      rw [upd_other _ _ (by omega)]
      exact h.arrays.free.zero addr ha
  · intro q a
    simpa only [arrayLen_setField] using h.arrays.live a

/-- A live array write keeps every represented struct and its ownership. -/
theorem StructAllocatorRepr.setArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) {p : PrimTy}
    (a : HRef H (.array (.prim p))) (i : Nat) (hi : i < hp.len a .dyn)
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StructAllocatorRepr (hp.set a (MObj.setElem .dyn (hp.get a) i v)) base frame cursor
      (writeMachine m ((base a.id).val + 1 + i) w) :=
  ⟨h.arrays.set a i hi v w hw, h.structs.arraySet h.separated a i hi v w,
    StructArraySeparated.setArray h.separated a i v, h.live⟩

end Solidity.Evm.Memory
