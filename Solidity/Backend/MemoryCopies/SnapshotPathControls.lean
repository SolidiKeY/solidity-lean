import Solidity.Backend.MemoryCopies.SnapshotPaths

/-! Nested live snapshot paths versus actual alias writes in both overlap
directions; reached failure prefixes retain effects rather than rolling back. -/
namespace Solidity.Backend.MemoryCopies.SnapshotPathControls
open Backend.MemoryOps
private def leafType : Ty := .ref (.array (.prim .uint))
private def branchType : Ty := .ref (.fixed leafType 2)
private def treeType : Ty := .ref (.array branchType)
private def seven : PrimTy.uint.Denote := ⟨7,by decide⟩
private def eleven : PrimTy.uint.Denote := ⟨11,by decide⟩
private def thirteen : PrimTy.uint.Denote := ⟨13,by decide⟩
private def seventeen : PrimTy.uint.Denote := ⟨17,by decide⟩
private def leaf : SVal leafType := .array
  (.cons (.prim seven) (.cons (.prim eleven) (.cons (.prim thirteen) (.cons (.prim seventeen) .nil)))) .nil (by decide)
private def emptyLeaf : SVal leafType := .array .nil .nil (by decide)
private def branch : SVal branchType := .fixed (.cons leaf (.cons emptyLeaf .nil))
private def tree : SVal treeType := .array (.cons branch (.cons branch .nil)) .nil (by decide)
private def initial := tree.copyStToM (H := []) () rfl
private def old : HRef initial.H' (.array (.prim .uint)) := ⟨0,by decide +kernel⟩
private def snapshot := MVal.copyMToSt initial.heap (T := treeType) initial.val
private def grown := snapshot.copyStToM initial.heap rfl
private def right : Heap initial.H' := initial.heap.set old ⟨[seven,seven,eleven,thirteen],by decide⟩
private def left : Heap initial.H' := initial.heap.set old ⟨[eleven,thirteen,seventeen,seventeen],by decide⟩
private def rightAfter : Heap grown.H' := grown.heap.set (old.wk grown.ext) ⟨[seven,seven,eleven,thirteen],by decide⟩
private def leftAfter : Heap grown.H' := grown.heap.set (old.wk grown.ext) ⟨[eleven,thirteen,seventeen,seventeen],by decide⟩
private def i0 : PrimTy.uint.Denote := ⟨0,by decide +kernel⟩
private def i1 : PrimTy.uint.Denote := ⟨1,by decide⟩
private def i4 : PrimTy.uint.Denote := ⟨4,by decide⟩
private def wordPath (index : PrimTy.uint.Denote) : Path treeType (.prim .uint) := .at i0 (.atF i0 (.at index .nil))
private noncomputable def word (heap : Heap grown.H') (index : PrimTy.uint.Denote) : Option Int :=
  (copyPathObserver heap (wordPath index) grown.val).map (fun (value : PrimTy.uint.Denote) => value.val)
private def oldWords (heap : Heap grown.H') : List Int :=
  (heap.get (old.wk grown.ext)).val.map (fun value => value.val)

theorem certificate_inhabited : SnapshotPathCertificate := snapshotPaths

theorem old_runs : runCaptures initial.heap old .dyn [(0,3,1)] = some right ∧
    runCaptures initial.heap old .dyn [(1,4,0)] = some left ∧
    runCaptures initial.heap old .dyn [] = some initial.heap ∧
    runCaptures initial.heap old .dyn [(0,5,0)] = none :=
  ⟨by with_unfolding_all rfl,by with_unfolding_all rfl,rfl,by with_unfolding_all rfl⟩

theorem success_inhabited :
    SnapshotPathSuccess initial.heap right initial.val rfl old .dyn [(0,3,1)] ∧
    SnapshotPathSuccess initial.heap left initial.val rfl old .dyn [(1,4,0)] :=
  ⟨snapshot_path_success initial.heap right initial.val rfl old .dyn _ old_runs.1,
   snapshot_path_success initial.heap left initial.val rfl old .dyn _ old_runs.2.1⟩

theorem right_observations :
    runCaptures grown.heap (old.wk grown.ext) .dyn [(0,3,1)] = some rightAfter ∧
    oldWords rightAfter = [7,7,11,13] ∧ word rightAfter i1 = some 11 :=
  ⟨by with_unfolding_all rfl,by decide +kernel⟩

theorem left_observations :
    runCaptures grown.heap (old.wk grown.ext) .dyn [(1,4,0)] = some leftAfter ∧
    oldWords leftAfter = [11,13,17,17] ∧ word leftAfter i1 = some 11 :=
  ⟨by with_unfolding_all rfl,by decide +kernel⟩

theorem all_paths_after_right : SnapshotPathObservation initial.heap initial.val rfl rightAfter :=
  snapshot_paths_of_mirror initial.heap initial.val rfl rightAfter
    (copy_schedule_mirrors initial.heap snapshot rfl old .dyn [(0,3,1)] rightAfter right_observations.1)

theorem bounds_after_right {Q : RefTy} (path : Path treeType (.ref Q)) (reference : HRef grown.H' Q)
    (observed : copyPathObserver rightAfter path grown.val = some reference) : 7 ≤ reference.id ∧ reference.id < 14 := by
  have bounds : initial.H'.length ≤ reference.id ∧ reference.id < initial.H'.length + liveObjectCount snapshot :=
    all_paths_after_right.bounds path reference observed
  have start : initial.H'.length = 7 := by decide +kernel
  have finish : initial.H'.length + liveObjectCount snapshot = 14 := by decide +kernel
  rw [finish,start] at bounds
  exact bounds

theorem old_separation {Q R : RefTy} (path : Path treeType (.ref Q)) (reference : HRef grown.H' Q)
    (older : HRef initial.H' R) (observed : copyPathObserver rightAfter path grown.val = some reference) :
    older.id < reference.id :=
  all_paths_after_right.separate_old initial.heap initial.val rfl rightAfter path reference older observed

theorem empty_path :
    (copyPathObserver rightAfter (.at i0 (.atF i1 (.at i0 .nil))) grown.val).map
      (fun (value : PrimTy.uint.Denote) => value.val) = none := by decide +kernel

theorem failure_run :
    runCaptures grown.heap (old.wk grown.ext) .dyn [(0,3,1),(0,5,0),(1,4,0)] = none := by with_unfolding_all rfl

theorem failure_prefix :
    runCaptures grown.heap (old.wk grown.ext) .dyn [(0,3,1)] = some rightAfter ∧
    checkedCaptureOverwrite rightAfter (old.wk grown.ext) .dyn (old.wk grown.ext) .dyn 0 5 0 = none ∧
    oldWords rightAfter = [7,7,11,13] ∧ word rightAfter i1 = some 11 :=
  ⟨right_observations.1,by with_unfolding_all rfl,right_observations.2⟩

theorem failure_inhabited :
    SnapshotPathFailure initial.heap initial.val rfl old .dyn [(0,3,1),(0,5,0),(1,4,0)] :=
  snapshot_path_failure initial.heap initial.val rfl old .dyn _ failure_run

theorem absence_after_failure : copyPathObserver rightAfter (wordPath i4) grown.val = none ↔
    snapshot.findLiveM (wordPath i4) = none :=
  all_paths_after_right.absent_iff initial.heap initial.val rfl rightAfter (wordPath i4)

theorem long_schedule :
    runCaptures grown.heap (old.wk grown.ext) .dyn
      ((0,3,1) :: List.replicate 64 (4,4,4)) = some rightAfter := by
  apply (runCaptures_cons_some _ _ _ _ _ _).2
  exact ⟨rightAfter,by with_unfolding_all rfl,
    runCaptures_end_replicate rightAfter (old.wk grown.ext) .dyn 4 64 (by decide +kernel)⟩

theorem long_path_preserved :
    SnapshotPathObservation initial.heap initial.val rfl rightAfter :=
  snapshot_paths_of_mirror initial.heap initial.val rfl rightAfter
    (copy_schedule_mirrors initial.heap snapshot rfl old .dyn
      ((0,3,1) :: List.replicate 64 (4,4,4)) rightAfter long_schedule)

theorem wrong_cascade_rejected : oldWords rightAfter ≠ [7,7,7,7] ∧
    word rightAfter i1 ≠ some 7 ∧ oldWords rightAfter ≠ [7,11,13,17] := by
  rw [right_observations.2.1,right_observations.2.2]
  decide

#print axioms certificate_inhabited
#print axioms old_runs
#print axioms success_inhabited
#print axioms right_observations
#print axioms left_observations
#print axioms all_paths_after_right
#print axioms bounds_after_right
#print axioms old_separation
#print axioms empty_path
#print axioms failure_run
#print axioms failure_prefix
#print axioms failure_inhabited
#print axioms absence_after_failure
#print axioms long_schedule
#print axioms long_path_preserved
#print axioms wrong_cascade_rejected
end Solidity.Backend.MemoryCopies.SnapshotPathControls
