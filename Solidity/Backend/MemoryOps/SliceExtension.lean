import Solidity.Backend.MemoryOps.SliceBounds
import Solidity.Theory.Typed.Mem

/-!
# Slice reads across published heap extension

`Heap.Keeps` is a premise for general growth, and is discharged by the
published allocator theorem for the allocation corollary. Reference elements
are weakened, not deep-copied; no fresh identity is claimed for slice views.
-/
namespace Solidity.Backend.MemoryOps

/-- The slice commutes with heap extension, even for reference elements. -/
theorem sliceElems_keeps {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) (start stop : Nat) :
    sliceElems hp' (r.wk e) a start stop =
      (sliceElems hp r a start stop).map (MVal.wk e E) := by
  simp only [sliceElems, hk r, MObj.elems_wk, List.map_drop, List.map_take]

/-- Validity of the exact endpoint checks survives a preserving extension. -/
theorem sliceBounds_keeps {H H' : HTy} {R : RefTy} {E : Ty}
    {hp : Heap H} {hp' : Heap H'} (e : H <+: H') (hk : Heap.Keeps e hp hp')
    (r : HRef H R) (a : ArrTy R E) {start stop : Nat}
    (h : SliceBounds (hp.len r a) start stop) :
    SliceBounds (hp'.len (r.wk e) a) start stop := by
  simpa only [Heap.len, hk r, MObj.elems_wk, List.length_map] using h

/-- Actual allocation discharges the preservation premise for every old slice. -/
theorem sliceElems_alloc {H : HTy} {R A : RefTy} {E : Ty}
    (hp : Heap H) (o : MObj H A) (r : HRef H R) (a : ArrTy R E)
    (start stop : Nat) :
    sliceElems (hp.alloc o).1 (r.wk (List.prefix_append H [A])) a start stop =
      (sliceElems hp r a start stop).map (MVal.wk (List.prefix_append H [A]) E) :=
  sliceElems_keeps _ (Heap.keeps_alloc hp o) r a start stop

/-- Aliases stay aliases, and distinct identities stay distinct, under growth. -/
theorem alias_iff_wk {H H' : HTy} {R Q : RefTy} (e : H <+: H')
    (r : HRef H R) (q : HRef H Q) :
    (r.wk e).id = (q.wk e).id ↔ r.id = q.id := Iff.rfl

/-- No old reference becomes the fresh allocation, even when the types agree. -/
theorem old_ne_fresh {H : HTy} {R A : RefTy} (hp : Heap H) (o : MObj H A)
    (r : HRef H R) :
    (r.wk (List.prefix_append H [A])).id ≠ (hp.alloc o).2.id :=
  Nat.ne_of_lt r.id_lt

/-- info: 'Solidity.Backend.MemoryOps.sliceElems_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sliceElems_keeps
/-- info: 'Solidity.Backend.MemoryOps.sliceBounds_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sliceBounds_keeps
/-- info: 'Solidity.Backend.MemoryOps.sliceElems_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sliceElems_alloc
/-- info: 'Solidity.Backend.MemoryOps.alias_iff_wk' depends on axioms: [propext] -/
#guard_msgs in #print axioms alias_iff_wk
/-- info: 'Solidity.Backend.MemoryOps.old_ne_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms old_ne_fresh

end Solidity.Backend.MemoryOps
