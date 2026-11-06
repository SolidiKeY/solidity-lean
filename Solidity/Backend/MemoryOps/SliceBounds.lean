import Solidity.Semantics.Heap

/-!
# Bounds for typed heap slice adapters

These certificates concern the existing heap element lists. They neither
compile a copy loop nor replace the independent source semantics. Endpoints
are runtime naturals, with no additional payload or recursion bound.
-/
namespace Solidity.Backend.MemoryOps

/-- A half-open source interval, including its exact endpoint checks. -/
structure SliceBounds (size start stop : Nat) : Prop where
  ordered : start ≤ stop
  bounded : stop ≤ size

namespace SliceBounds

theorem index {size start stop i : Nat} (h : SliceBounds size start stop)
    (hi : i < stop - start) : start + i < size := by
  have ho := h.ordered
  have hb := h.bounded
  omega

theorem compose {size start stop lo hi : Nat} (h : SliceBounds size start stop)
    (k : SliceBounds (stop - start) lo hi) :
    SliceBounds size (start + lo) (start + hi) := by
  have ho := h.ordered
  have hb := h.bounded
  have ko := k.ordered
  have kb := k.bounded
  constructor <;> omega

theorem length {α : Type} {xs : List α} {start stop : Nat}
    (h : SliceBounds xs.length start stop) :
    ((xs.drop start).take (stop - start)).length = stop - start := by
  rw [List.length_take, List.length_drop]
  have ho := h.ordered
  have hb := h.bounded
  exact Nat.min_eq_left (by omega)

theorem read {α : Type} {xs : List α} {start stop i : Nat}
    (hi : i < stop - start) :
    ((xs.drop start).take (stop - start))[i]? = xs[start + i]? := by
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

end SliceBounds

/-- A slice of an existing typed object; reference elements retain their types.
This is a read adapter, not a fresh deep copy certificate. -/
def sliceElems {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (start stop : Nat) : List (MVal H E) :=
  ((MObj.elems a (hp.get r)).drop start).take (stop - start)

theorem sliceElems_length {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) {start stop : Nat}
    (h : SliceBounds (hp.len r a) start stop) :
    (sliceElems hp r a start stop).length = stop - start :=
  h.length

theorem sliceElems_read {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) {start stop i : Nat}
    (h : SliceBounds (hp.len r a) start stop) (hi : i < stop - start) :
    (sliceElems hp r a start stop)[i]? = (MObj.elems a (hp.get r))[start + i]? ∧
      start + i < hp.len r a :=
  ⟨SliceBounds.read hi, h.index hi⟩

/-- Nested view coordinates compose exactly; both ranges may be runtime values. -/
theorem sliceElems_compose {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) {start stop lo hi : Nat}
    (h : SliceBounds (hp.len r a) start stop)
    (k : SliceBounds (stop - start) lo hi) :
    ((sliceElems hp r a start stop).drop lo).take (hi - lo) =
      sliceElems hp r a (start + lo) (start + hi) := by
  have ho := h.ordered
  have ko := k.ordered
  have kb := k.bounded
  simp only [sliceElems, List.drop_take, List.take_take, List.drop_drop,
    Nat.min_eq_left (show hi - lo ≤ stop - start - lo by omega)]
  congr 1
  omega

/-- Empty at the source end is legal, including the empty source. -/
theorem empty_at_end (size : Nat) : SliceBounds size size size := ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Reversed bounds and overrun endpoints cannot supply a certificate. -/
theorem reversed_invalid {size start stop : Nat} (h : stop < start) :
    ¬ SliceBounds size start stop := fun k => Nat.not_le_of_lt h k.ordered

theorem overrun_invalid {size start stop : Nat} (h : size < stop) :
    ¬ SliceBounds size start stop := fun k => Nat.not_le_of_lt h k.bounded

/-- Element-index boundary crossing with a nonzero source offset. -/
theorem boundary : SliceBounds 65 31 64 ∧ 31 + 32 < 65 ∧ ¬ SliceBounds 65 31 66 := by
  constructor
  · exact ⟨by decide, by decide⟩
  · constructor
    · decide
    · exact overrun_invalid (by decide)

/-- info: 'Solidity.Backend.MemoryOps.SliceBounds.index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SliceBounds.index
/-- info: 'Solidity.Backend.MemoryOps.SliceBounds.compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms SliceBounds.compose
/-- info: 'Solidity.Backend.MemoryOps.sliceElems_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sliceElems_length
/-- info: 'Solidity.Backend.MemoryOps.sliceElems_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sliceElems_read

end Solidity.Backend.MemoryOps
