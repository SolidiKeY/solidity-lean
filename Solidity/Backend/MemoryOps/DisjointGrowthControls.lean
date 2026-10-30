import Solidity.Backend.MemoryOps.DisjointExtension

/-! Allocation creates a parent whose fields retain old identities while the
referenced children actually change. Structural framing is not deep liveness. -/
namespace Solidity.Backend.MemoryOps.GrowthControls
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B, B]
private def r : HRef H B := ⟨0, rfl⟩
private def q : HRef H B := ⟨1, rfl⟩
private def hp : Heap H := (⟨[true, true], by decide⟩, ⟨[false, false], by decide⟩, ())
private def parent : MObj H P := ⟨[r, q], rfl⟩
private def e := List.prefix_append H [P]
private theorem hr : 1 + [false].length ≤ hp.len r .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
private theorem hq : 0 + [true].length ≤ hp.len q .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
private theorem sep : r.id ≠ q.id := by decide
private def old := overwriteTwo hp r .dyn 1 [false] hr q .dyn 0 [true] hq sep
private def grown := overwriteTwo (hp.alloc parent).1 (r.wk e) .dyn 1
  ([false].map (MVal.wk e (.prim .bool)))
  (overwriteSlice_space e (Heap.keeps_alloc hp parent) r .dyn 1 [false] hr)
  (q.wk e) .dyn 0 ([true].map (MVal.wk e (.prim .bool)))
  (overwriteSlice_space e (Heap.keeps_alloc hp parent) q .dyn 0 [true] hq) sep

/-- The initial growth premise is discharged by the actual allocator. -/
theorem allocator_transport : Heap.Keeps e old grown :=
  overwriteTwo_alloc hp parent r .dyn 1 [false] hr q .dyn 0 [true] hq sep

/-- Every old typed object has the actual overwritten contents after growth. -/
theorem old_observations :
    MObj.elems .dyn (grown.get (r.wk e)) = [true, false] ∧
    MObj.elems .dyn (grown.get (q.wk e)) = [true, false] := by
  constructor
  · rw [allocator_transport, MObj.elems_wk]
    rw [List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    change MObj.elems .dyn (old.get r) = [true, false]
    rw [old, overwriteTwo_first, overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · rw [allocator_transport, MObj.elems_wk]
    rw [List.map_id'' (f := MVal.wk e (.prim .bool)) (fun _ => rfl)]
    change MObj.elems .dyn (old.get q) = [true, false]
    rw [old, overwriteTwo_comm, overwriteTwo_first, overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl

/-- A nonprimitive fresh parent keeps both old child identities. -/
theorem fresh_parent_frame :
    grown.get (hp.alloc parent).2 = (hp.alloc parent).1.get (hp.alloc parent).2 ∧
    (MObj.elems .fixed (grown.get (hp.alloc parent).2)).map HRef.id = [0, 1] := by
  have hf : grown.get (hp.alloc parent).2 = (hp.alloc parent).1.get (hp.alloc parent).2 :=
    overwriteTwo_alloc_frame hp parent r .dyn 1 [false] hr q .dyn 0 [true] hq sep
  refine ⟨hf, ?_⟩
  rw [hf, Heap.get_alloc, MObj.elems_wk, List.map_map]
  simp only [MObj.elems_fixed]
  rfl

/-- Fresh structural framing does not imply that its old children are unchanged. -/
theorem child_content_negative :
    grown.get (r.wk e) ≠ (hp.alloc parent).1.get (r.wk e) := by
  intro he
  have ho := congrArg (MObj.elems .dyn) he
  rw [old_observations.1, Heap.keeps_alloc hp parent, MObj.elems_wk] at ho
  simp only [MObj.elems_dyn] at ho
  change [true, false] = [true, true] at ho
  cases ho

/-- info: 'Solidity.Backend.MemoryOps.GrowthControls.allocator_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocator_transport
/-- info: 'Solidity.Backend.MemoryOps.GrowthControls.old_observations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms old_observations
/-- info: 'Solidity.Backend.MemoryOps.GrowthControls.fresh_parent_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_parent_frame
/-- info: 'Solidity.Backend.MemoryOps.GrowthControls.child_content_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms child_content_negative
end Solidity.Backend.MemoryOps.GrowthControls
