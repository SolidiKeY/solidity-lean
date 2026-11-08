import Solidity.Backend.MemoryOps.Snapshot
import Solidity.Backend.MemoryOps.SliceExtension

/-!
# Snapshot overwrite adapter over the published intrinsic heap

This adapter updates an existing array object, using `Heap.set`; it does not
allocate children or emit a loop. References are shallow values retaining
identity. Target simulation and source-language copy classification stay open.
-/
namespace Solidity.Backend.MemoryOps

/-- Repackage element data of unchanged length in the existing object type. -/
def withElems {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E) :
    (o : MObj H R) → (xs : List (MVal H E)) →
      xs.length = (MObj.elems a o).length → MObj H R :=
  @ArrTy.casesOn (fun R E a => (o : MObj H R) → (xs : List (MVal H E)) →
    xs.length = (MObj.elems a o).length → MObj H R) R E a
    (fun {_} o xs hl => ⟨xs, by rw [hl, MObj.elems_dyn]; exact o.property⟩)
    (fun {_} {_} o xs hl => ⟨xs, by rw [hl, MObj.elems_fixed]; exact o.property⟩)

-- Retain typed object-alias matching only for this existing projection proof.
set_option backward.isDefEq.respectTransparency false in
theorem elems_withElems {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E)
    (o : MObj H R) (xs : List (MVal H E)) (hl : xs.length = (MObj.elems a o).length) :
    MObj.elems a (withElems a o xs hl) = xs := by
  cases a <;> simp only [withElems, MObj.elems_dyn, MObj.elems_fixed]

/-- Install a captured payload in an existing typed array, preserving its size. -/
def overwriteSlice {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (dst : Nat) (payload : List (MVal H E))
    (h : dst + payload.length ≤ hp.len r a) : Heap H :=
  hp.set r (withElems a (hp.get r)
    (replaceSlice (MObj.elems a (hp.get r)) dst payload)
    (replaceSlice_length _ _ _ h))

/-- The actual destination object's elements are exactly the replacement. -/
theorem overwriteSlice_elems {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (dst : Nat) (payload : List (MVal H E))
    (h : dst + payload.length ≤ hp.len r a) :
    MObj.elems a ((overwriteSlice hp r a dst payload h).get r) =
      replaceSlice (MObj.elems a (hp.get r)) dst payload := by
  rw [overwriteSlice, Heap.get_set_same, elems_withElems]

/-- Every different typed object, including a nested child, is unchanged. -/
theorem overwriteSlice_frame {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (q : HRef H Q) (a : ArrTy R E) (dst : Nat)
    (payload : List (MVal H E)) (h : dst + payload.length ≤ hp.len r a)
    (hne : r.id ≠ q.id) :
    (overwriteSlice hp r a dst payload h).get q = hp.get q := by
  exact Heap.get_set_ne hp r q hne _

/-- Interior reads use the captured payload; overlap imposes no extra premise. -/
theorem overwriteSlice_inside {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (dst i : Nat) (payload : List (MVal H E))
    (h : dst + payload.length ≤ hp.len r a) (hi : i < payload.length) :
    (MObj.elems a ((overwriteSlice hp r a dst payload h).get r))[dst + i]? = payload[i]? := by
  rw [overwriteSlice_elems]
  exact replaceSlice_inside _ _ _ _ h hi

/-- Destination reads outside the written interval retain their old values. -/
theorem overwriteSlice_outside {H : HTy} {R : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H R) (a : ArrTy R E) (dst i : Nat) (payload : List (MVal H E))
    (h : dst + payload.length ≤ hp.len r a)
    (hi : i < dst ∨ dst + payload.length ≤ i) :
    (MObj.elems a ((overwriteSlice hp r a dst payload h).get r))[i]? =
      (MObj.elems a (hp.get r))[i]? := by
  rw [overwriteSlice_elems]
  rcases hi with hi | hi
  · exact replaceSlice_before _ _ _ _ h hi
  · exact replaceSlice_after _ _ _ _ h hi

/-- Source is captured from the original heap, even when source and destination
are the same object and the intervals overlap. -/
def captureOverwrite {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset : Nat) (hs : SliceBounds (hp.len src sa) start stop)
    (hd : offset + (stop - start) ≤ hp.len dst da) : Heap H :=
  overwriteSlice hp dst da offset (sliceElems hp src sa start stop)
    (by rw [sliceElems_length hp src sa hs]; exact hd)

theorem captureOverwrite_read {H : HTy} {R Q : RefTy} {E : Ty} (hp : Heap H)
    (src : HRef H R) (sa : ArrTy R E) (dst : HRef H Q) (da : ArrTy Q E)
    (start stop offset i : Nat) (hs : SliceBounds (hp.len src sa) start stop)
    (hd : offset + (stop - start) ≤ hp.len dst da) (hi : i < stop - start) :
    (MObj.elems da ((captureOverwrite hp src sa dst da start stop offset hs hd).get dst))[offset + i]? = (MObj.elems sa (hp.get src))[start + i]? := by
  rw [captureOverwrite, overwriteSlice_inside]
  · exact (sliceElems_read hp src sa hs hi).1
  · rw [sliceElems_length hp src sa hs]
    exact hi

/-- info: 'Solidity.Backend.MemoryOps.captureOverwrite_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms captureOverwrite_read

/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_elems' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_elems
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_frame
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_inside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_inside
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_outside

end Solidity.Backend.MemoryOps
