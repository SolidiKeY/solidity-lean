import Solidity.Backend.MemoryCopies.TraversalFootprint
import Solidity.Backend.MemoryCopies.HeapContents

/-! Exact intrinsic footprint controls for nested copies, shadow and equal trees. -/
namespace Solidity.Backend.MemoryCopies.TraversalFootprintControls
private def leafType : Ty := .ref (.array (.prim .uint))
private def branchType : Ty := .ref (.fixed leafType 2)
private def seven : SVal (.prim .uint) := .prim ⟨7,by decide⟩
private def eleven : SVal (.prim .uint) := .prim ⟨11,by decide⟩
private def leaf : SVal leafType :=
  .array (.cons seven (.cons eleven .nil)) (.cons seven .nil) (by decide)
private def branch : SVal branchType := .fixed (.cons leaf (.cons leaf .nil))
private def tree : SVal (.ref (.array branchType)) :=
  .array (.cons branch (.cons branch .nil)) (.cons branch .nil) (by decide)
private def empty : SVal (.ref (.array branchType)) := .array .nil (.cons branch .nil) (by decide)
private def long : SVal (.ref (.array branchType)) :=
  .array (SVec.replicate branch 64) (.cons branch .nil) (by decide)
private def basket : SVal (.ref (.struct "Basket")) := .struct (.cons leaf .nil)
private def initial : Heap [] := ()
private def seed := leaf.copyStToM initial rfl
private def grown := tree.copyStToM seed.heap rfl
private def second := tree.copyStToM grown.heap rfl

theorem live_counts : liveObjectCount leaf = 1 ∧ liveObjectCount branch = 3 ∧
    liveObjectCount tree = 7 ∧ liveObjectCount empty = 1 ∧ liveObjectCount basket = 2 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem certificates_inhabited :
    TraversalFootprintCertificate seed.heap tree rfl 7 ∧
      TraversalFootprintCertificate seed.heap basket rfl 2 ∧
      TraversalPairFootprint seed.heap tree tree rfl rfl 7 7 :=
  ⟨traversalFootprint tree rfl seed.heap,traversalFootprint basket rfl seed.heap,
    traversalPairFootprint tree tree rfl rfl seed.heap⟩

theorem root_and_count : grown.val.id = 7 ∧ grown.H'.length = 8 ∧
    second.val.id = 14 ∧ second.H'.length = 15 := by decide +kernel

/-- Duplicate equal stored trees allocate separate complete descendant blocks. -/
theorem descendant_ids :
    (MObj.elems .dyn (grown.heap.get grown.val)).map (fun branch =>
      (MObj.elems .fixed (grown.heap.get branch)).map (fun reference => reference.id)) = [[1,2],[4,5]] := by
  decide +kernel

theorem descendant_contents :
    (MObj.elems .dyn (grown.heap.get grown.val)).map (fun (branch : HRef grown.H' (.fixed leafType 2)) =>
      (MObj.elems .fixed (grown.heap.get branch)).map (fun (reference : HRef grown.H' (.array (.prim .uint))) =>
        (MObj.elems .dyn (grown.heap.get reference)).map (fun (value : PrimTy.uint.Denote) => value.val))) =
      [[[7,11],[7,11]],[[7,11],[7,11]]] := by decide +kernel

theorem old_object_retained :
    (MObj.elems .dyn (grown.heap.get (seed.val.wk grown.ext))).map (fun value => value.val) = [7,11] := by
  decide +kernel

theorem empty_shadow :
    (empty.copyStToM seed.heap rfl).H'.length = 2 ∧
      (empty.copyStToM seed.heap rfl).val.id = 1 ∧
      (empty.copyStToM seed.heap rfl).heap.len (empty.copyStToM seed.heap rfl).val .dyn = 0 := by
  decide +kernel

/--64 complete branch copies consume193 new identities, independent of old heap size. -/
theorem long_count {H : HTy} (heap : Heap H) :
    (long.copyStToM heap rfl).H'.length = H.length + 193 ∧
      (long.copyStToM heap rfl).val.id = H.length + 193 - 1 := by
  have measure : liveObjectCount long = 193 := by decide +kernel
  constructor
  · simpa only [measure] using valueCopy_count long rfl heap
  · simpa only [measure] using copy_root_index long rfl heap

theorem roundtrip : MVal.copyMToSt grown.heap grown.val = tree.strip :=
  (storageHeapContents tree rfl).contents seed.heap

theorem wrong_shared_tree_rejected : second.val.id ≠ grown.val.id := by
  have first : grown.val.id = 7 := root_and_count.1
  have later : second.val.id = 14 := root_and_count.2.2.1
  rw [first,later]
  decide

/-- The nonempty storage-only shadow is not another live branch allocation. -/
theorem wrong_shadow_count_rejected : grown.H'.length ≠ 11 := by
  rw [root_and_count.2.1]
  decide

#print axioms live_counts
#print axioms certificates_inhabited
#print axioms root_and_count
#print axioms descendant_ids
#print axioms descendant_contents
#print axioms old_object_retained
#print axioms empty_shadow
#print axioms long_count
#print axioms roundtrip
#print axioms wrong_shared_tree_rejected
#print axioms wrong_shadow_count_rejected
end Solidity.Backend.MemoryCopies.TraversalFootprintControls
