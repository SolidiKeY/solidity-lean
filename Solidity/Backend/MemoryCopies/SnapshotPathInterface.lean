import Solidity.Backend.MemoryCopies.CopyPaths
import Solidity.Backend.MemoryOps.CopyMirrorSchedule

/-! Typed-path observations of an actual memory snapshot across old-object
capture schedules. None is the existing checked schedule refusal, not panic/gas. -/
namespace Solidity.Backend.MemoryCopies
open Backend.MemoryOps

structure SnapshotPathObservation {H : HTy} {A : RefTy} (heap : Heap H) (input : HRef H A)
    (memory : (Ty.ref A).mapFree = true)
    (after : Heap ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H') : Prop where
  contents : ∀ {U : Ty} (path : Path (.ref A) U),
    (copyPathObserver after path ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val).map
      (MVal.copyMToSt after) = ((MVal.copyMToSt heap (T := .ref A) input).findLiveM path).map SVal.strip
  bounds : ∀ {Q : RefTy} (path : Path (.ref A) (.ref Q))
    (reference : HRef ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).H' Q),
    copyPathObserver after path ((MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory).val = some reference →
      H.length ≤ reference.id ∧ reference.id < H.length + liveObjectCount (MVal.copyMToSt heap (T := .ref A) input)

def SnapshotPathSuccess {H : HTy} {A R : RefTy} {E : Ty} (heap reached : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true) (destination : HRef H R)
    (shape : ArrTy R E) (schedule : List SnapshotArgs) : Prop :=
  let grown := (MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory
  ∃ after, runCaptures grown.heap (destination.wk grown.ext) shape schedule = some after ∧
    Heap.Keeps grown.ext reached after ∧ SnapshotPathObservation heap input memory after

def SnapshotPathFailure {H : HTy} {A R : RefTy} {E : Ty} (heap : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true) (destination : HRef H R)
    (shape : ArrTy R E) (schedule : List SnapshotArgs) : Prop :=
  let grown := (MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory
  ∃ pre step suffix mid, schedule = pre ++ step :: suffix ∧
    runCaptures grown.heap (destination.wk grown.ext) shape pre = some mid ∧
    checkedCaptureOverwrite mid (destination.wk grown.ext) shape (destination.wk grown.ext) shape
      step.1 step.2.1 step.2.2 = none ∧ SnapshotPathObservation heap input memory mid

structure SnapshotPathCertificate : Prop where
  success : ∀ {H : HTy} {A R : RefTy} {E : Ty} (heap reached : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true) (destination : HRef H R)
    (shape : ArrTy R E) (schedule : List SnapshotArgs),
    runCaptures heap destination shape schedule = some reached →
      SnapshotPathSuccess heap reached input memory destination shape schedule
  failure : ∀ {H : HTy} {A R : RefTy} {E : Ty} (heap : Heap H)
    (input : HRef H A) (memory : (Ty.ref A).mapFree = true) (destination : HRef H R)
    (shape : ArrTy R E) (schedule : List SnapshotArgs),
    let grown := (MVal.copyMToSt heap (T := .ref A) input).copyStToM heap memory
    runCaptures grown.heap (destination.wk grown.ext) shape schedule = none →
      SnapshotPathFailure heap input memory destination shape schedule
end Solidity.Backend.MemoryCopies
