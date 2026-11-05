import Solidity.Backend.MemoryCopies.SnapshotPathInterface

/-! Observe the preserved recursive snapshot mirror at every existing typed
path, including after actual old-object writes and reached checked refusals. -/
namespace Solidity.Backend.MemoryCopies
open Backend.MemoryOps

theorem snapshot_paths_of_mirror {H : HTy} {A : RefTy} (heap : Heap H) (input : HRef H A)
    (memory : (Ty.ref A).mapFree = true)
    (after : Heap ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H')
    (mirrored : (MVal.copyMToSt heap (T := .ref A) input).Mirrors after H.length
      ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val) :
    SnapshotPathObservation heap input memory after where
  contents := fun path => (mirror_path after H.length path _ _ mirrored).contents
  bounds := by
    intro Q path reference observed
    have below : CopyPathMirrors after H.length
        ((MVal.copyMToSt heap (T := .ref A) input).findLiveM path)
        (copyPathObserver after path ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val) :=
      mirror_path after H.length path _ _ mirrored
    rw [observed] at below
    cases found : (MVal.copyMToSt heap (T := .ref A) input).findLiveM path with
    | none => rw [found] at below; cases below
    | some child =>
      have childMirror : child.Mirrors after H.length reference := by
        simpa only [found,CopyPathMirrors] using below
      have fresh : H.length ≤ reference.id := SVal.Mirrors.id_ge child reference childMirror
      have bounded : reference.id < ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H'.length :=
        reference.id_lt
      have count : ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H'.length =
          H.length + liveObjectCount (MVal.copyMToSt heap (T := .ref A) input) :=
        valueCopy_count _ memory heap
      exact ⟨fresh,by omega⟩

theorem snapshot_path_success {H : HTy} {A R : RefTy} {E : Ty} (heap reached : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true) (destination : HRef H R)
    (shape : ArrTy R E) (schedule : List SnapshotArgs)
    (execution : runCaptures heap destination shape schedule = some reached) :
    SnapshotPathSuccess heap reached input memory destination shape schedule := by
  obtain ⟨after,ran,kept,mirrored,_⟩ :=
    copy_schedule_transport heap reached (MVal.copyMToSt heap (T := .ref A) input)
      memory destination shape schedule execution
  exact ⟨after,ran,kept,snapshot_paths_of_mirror heap input memory after mirrored⟩

theorem snapshot_path_failure {H : HTy} {A R : RefTy} {E : Ty} (heap : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true) (destination : HRef H R)
    (shape : ArrTy R E) (schedule : List SnapshotArgs)
    (failure : runCaptures ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).heap
      (destination.wk ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).ext) shape schedule = none) :
    SnapshotPathFailure heap input memory destination shape schedule := by
  obtain ⟨pre,step,suffix,mid,split,ran,refused,mirrored⟩ :=
    (copy_schedule_none_first heap (MVal.copyMToSt heap (T := .ref A) input)
      memory destination shape schedule).mp failure
  exact ⟨pre,step,suffix,mid,split,ran,refused,snapshot_paths_of_mirror heap input memory mid mirrored⟩

def snapshotPaths : SnapshotPathCertificate := ⟨snapshot_path_success,snapshot_path_failure⟩

theorem SnapshotPathObservation.absent_iff {H : HTy} {A : RefTy} (heap : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true)
    (after : Heap ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H')
    (observations : SnapshotPathObservation heap input memory after) {U : Ty} (path : Path (.ref A) U) :
    copyPathObserver after path ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val = none ↔
      (MVal.copyMToSt heap (T := .ref A) input).findLiveM path = none := by
  have contents :
      (copyPathObserver after path ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val).map
        (MVal.copyMToSt after) = ((MVal.copyMToSt heap (T := .ref A) input).findLiveM path).map SVal.strip :=
    observations.contents path
  constructor
  · intro absent
    rw [absent,Option.map_none] at contents
    cases found : (MVal.copyMToSt heap (T := .ref A) input).findLiveM path with
    | none => rfl
    | some child => rw [found] at contents; cases contents
  · intro absent
    rw [absent,Option.map_none] at contents
    cases found : copyPathObserver after path
        ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val with
    | none => rfl
    | some child => rw [found] at contents; cases contents

theorem SnapshotPathObservation.separate_old {H : HTy} {A Q R : RefTy} (heap : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true)
    (after : Heap ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H')
    (observations : SnapshotPathObservation heap input memory after)
    (path : Path (.ref A) (.ref Q))
    (reference : HRef ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H' Q)
    (old : HRef H R)
    (observed : copyPathObserver after path
      ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val = some reference) :
    old.id < reference.id := by
  have fresh : H.length ≤ reference.id := (observations.bounds path reference observed).1
  have before : old.id < H.length := old.id_lt
  omega

#print axioms snapshot_paths_of_mirror
#print axioms snapshot_path_success
#print axioms snapshot_path_failure
#print axioms snapshotPaths
#print axioms SnapshotPathObservation.absent_iff
#print axioms SnapshotPathObservation.separate_old
end Solidity.Backend.MemoryCopies
