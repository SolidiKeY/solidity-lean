import Solidity.Backend.MemoryCopies.CopyPaths

/-! Actual nested/fixed/struct copy observations, live bounds and separate descendant copies. -/
namespace Solidity.Backend.MemoryCopies.CopyPathControls
private def leafType : Ty := .ref (.array (.prim .uint))
private def branchType : Ty := .ref (.fixed leafType 2)
private def treeType : Ty := .ref (.array branchType)
private def seven : SVal (.prim .uint) := .prim ⟨7,by decide⟩
private def eleven : SVal (.prim .uint) := .prim ⟨11,by decide⟩
private def ninetyNine : SVal (.prim .uint) := .prim ⟨99,by decide⟩
private def leaf : SVal leafType := .array (.cons seven (.cons eleven .nil)) (.cons ninetyNine .nil) (by decide)
private def emptyLeaf : SVal leafType := .array .nil (.cons ninetyNine .nil) (by decide)
private def branch : SVal branchType := .fixed (.cons leaf (.cons emptyLeaf .nil))
private def tree : SVal treeType := .array (.cons branch (.cons branch .nil)) (.cons branch .nil) (by decide)
private def empty : SVal treeType := .array .nil (.cons branch .nil) (by decide)
private def long : SVal (.ref (.array leafType)) := .array (SVec.replicate leaf 64) .nil (by decide)
private def basket : SVal (.ref (.struct "Basket")) := .struct (.cons leaf .nil)
private def initial : Heap [] := ()
private def seed := leaf.copyStToM initial rfl
private def first := tree.copyStToM seed.heap rfl
private def second := tree.copyStToM first.heap rfl
private def i0 : PrimTy.uint.Denote := ⟨0,by decide⟩
private def i1 : PrimTy.uint.Denote := ⟨1,by decide⟩
private def i2 : PrimTy.uint.Denote := ⟨2,by decide⟩
private def i63 : PrimTy.uint.Denote := ⟨63,by decide⟩
private def refPath (outer inner : PrimTy.uint.Denote) : Path treeType leafType := .at outer (.atF inner .nil)
private def wordPath (outer inner item : PrimTy.uint.Denote) : Path treeType (.prim .uint) :=
  .at outer (.atF inner (.at item .nil))
private noncomputable def wordObservation (path : Path treeType (.prim .uint)) : Option Int :=
  (copyPathObserver first.heap path first.val).map (fun (value : PrimTy.uint.Denote) => value.val)
private noncomputable def refObservation (path : Path treeType leafType) : Option Nat :=
  (copyPathObserver first.heap path first.val).map (fun (reference : HRef first.H' (.array (.prim .uint))) => reference.id)

theorem certificate_inhabited : CopiedPathCertificate copyPathObserver := copiedPaths

theorem reference_ids : refObservation (refPath i0 i0) = some 1 ∧
    refObservation (refPath i0 i1) = some 2 ∧ refObservation (refPath i1 i0) = some 4 := by decide +kernel

theorem word_observations : wordObservation (wordPath i0 i0 i1) = some 11 ∧
    wordObservation (wordPath i1 i0 i0) = some 7 ∧ wordObservation (wordPath i0 i1 i0) = none := by decide +kernel

theorem full_child_contents :
    (copyPathObserver first.heap (refPath i0 i0) first.val).map (MVal.copyMToSt first.heap) = some leaf.strip :=
  by
    have contents :
        (copyPathObserver first.heap (refPath i0 i0) first.val).map (MVal.copyMToSt first.heap) =
          (tree.findLiveM (refPath i0 i0)).map SVal.strip :=
      copy_path_contents seed.heap tree rfl (refPath i0 i0)
    exact contents.trans (by decide +kernel)

theorem reference_bounds {R : RefTy} (path : Path treeType (.ref R)) (reference : HRef first.H' R)
    (observed : copyPathObserver first.heap path first.val = some reference) : 1 ≤ reference.id ∧ reference.id < 8 :=
  by
    have bounds : seed.H'.length ≤ reference.id ∧
        reference.id < seed.H'.length + liveObjectCount tree :=
      copy_path_bounds seed.heap tree rfl path reference observed
    have start : seed.H'.length = 1 := by decide +kernel
    have finish : seed.H'.length + liveObjectCount tree = 8 := by decide +kernel
    rw [finish, start] at bounds
    exact bounds

theorem fixed_overrun : wordObservation (wordPath i0 i2 i0) = none := by decide +kernel

theorem dynamic_overrun : wordObservation (wordPath i2 i0 i0) = none := by decide +kernel

/-- Storage-only shadow data exists, but the same live-memory path is absent. -/
theorem shadow_is_not_live :
    (tree.findM (wordPath i0 i0 i2)).map (fun value => value.view.val) = some 99 ∧
      wordObservation (wordPath i0 i0 i2) = none := by decide +kernel

theorem empty_copy :
    let grown := empty.copyStToM seed.heap rfl
    (copyPathObserver grown.heap (refPath i0 i0) grown.val).map
      (fun (reference : HRef grown.H' (.array (.prim .uint))) => reference.id) = none := by decide +kernel

theorem long_copy :
    let grown := long.copyStToM seed.heap rfl
    (copyPathObserver grown.heap (.at i63 (.at i1 .nil)) grown.val).map
      (fun (value : PrimTy.uint.Denote) => value.val) = some 11 ∧
    (copyPathObserver grown.heap (.at i63 .nil) grown.val).map
      (fun (reference : HRef grown.H' (.array (.prim .uint))) => reference.id) = some 64 := by decide +kernel

theorem struct_path :
    let grown := basket.copyStToM seed.heap rfl
    (copyPathObserver grown.heap
      (.field (s := "Basket") (f := "items") (T := leafType) (by decide) (.at i1 .nil)) grown.val).map
      (fun (value : PrimTy.uint.Denote) => value.val) = some 11 := by decide +kernel

theorem path_preserved_after_second (path : Path treeType leafType) :
    copyPathObserver second.heap path (MVal.wk second.ext treeType first.val) =
      (copyPathObserver first.heap path first.val).map (MVal.wk second.ext leafType) :=
  copyPathObserver_keeps second.ext first.heap second.heap (SVal.keeps_copyStToM tree rfl first.heap) path first.val

theorem contents_preserved_after_second {U : Ty} (path : Path treeType U) :
    (copyPathObserver second.heap path (MVal.wk second.ext treeType first.val)).map (MVal.copyMToSt second.heap) =
      (tree.findLiveM path).map SVal.strip :=
  copy_path_contents_keeps seed.heap tree rfl second.ext second.heap (SVal.keeps_copyStToM tree rfl first.heap) path

theorem all_reference_paths_separated {R Q : RefTy} (leftPath : Path treeType (.ref R))
    (rightPath : Path treeType (.ref Q)) (left : HRef second.H' R) (right : HRef second.H' Q)
    (observedLeft : copyPathObserver second.heap leftPath (MVal.wk second.ext treeType first.val) = some left)
    (observedRight : copyPathObserver second.heap rightPath second.val = some right) : left.id < right.id :=
  copy_paths_separated seed.heap tree tree rfl rfl leftPath rightPath left right observedLeft observedRight

theorem descendant_ids_after_second :
    (copyPathObserver second.heap (refPath i0 i0) (MVal.wk second.ext treeType first.val)).map
      (fun (reference : HRef second.H' (.array (.prim .uint))) => reference.id) = some 1 ∧
    (copyPathObserver second.heap (refPath i0 i0) second.val).map
      (fun (reference : HRef second.H' (.array (.prim .uint))) => reference.id) = some 8 := by decide +kernel

theorem wrong_word_rejected : wordObservation (wordPath i0 i0 i1) ≠ some 99 := by
  rw [word_observations.1]
  decide

theorem absence_matches_live_path :
    copyPathObserver first.heap (wordPath i0 i0 i2) first.val = none ↔ tree.findLiveM (wordPath i0 i0 i2) = none :=
  copy_path_absent_iff seed.heap tree rfl (wordPath i0 i0 i2)

#print axioms certificate_inhabited
#print axioms reference_ids
#print axioms word_observations
#print axioms full_child_contents
#print axioms reference_bounds
#print axioms fixed_overrun
#print axioms dynamic_overrun
#print axioms shadow_is_not_live
#print axioms empty_copy
#print axioms long_copy
#print axioms struct_path
#print axioms path_preserved_after_second
#print axioms contents_preserved_after_second
#print axioms all_reference_paths_separated
#print axioms descendant_ids_after_second
#print axioms wrong_word_rejected
#print axioms absence_matches_live_path
end Solidity.Backend.MemoryCopies.CopyPathControls
