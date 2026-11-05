import Solidity.Backend.MemoryCopies.Interface
import Solidity.Backend.MemoryCopies.HeapContents
import Solidity.Backend.MemoryOps.CopyMirrorSchedule

/-! Inhabit the published deep-copy heap interface and preserve its frozen
contents through actual old-object capture schedules. No emitter is added. -/
namespace Solidity.Backend.MemoryCopies
open Backend.MemoryOps

/-- The legacy heap record is supplied by existing framing/freshness laws and
our generic live contents law, without using the legacy word certificate. -/
def storageHeapLegacy {R : RefTy} (value : SVal (.ref R))
    (memory : (Ty.ref R).mapFree = true) : StorageHeapCertificate value memory where
  keeps := fun hp => SVal.keeps_copyStToM value memory hp
  fresh := fun hp => SVal.copyStToM_id_ge hp value memory
  contents := (storageHeapContents value memory).contents

/-- Actual snapshot/deep-copy constructor for the already published interface. -/
def deepCopyHeap {H : HTy} {R : RefTy} (heap : Heap H) (input : HRef H R)
    (memory : (Ty.ref R).mapFree = true) : MemoryDeepCopyHeapCertificate heap input memory where
  snapshot := storageHeapLegacy (MVal.copyMToSt heap (T := .ref R) input) memory
  distinct := by
    have fresh : H.length ≤ ((MVal.copyMToSt heap (T := .ref R) input).copyStToM heap memory).val.id :=
      SVal.copyStToM_id_ge heap _ memory
    have old : input.id < H.length := input.id_lt
    omega

/-- A fresh snapshot keeps INITIAL contents even after overlapping writes to
an older object. The success equation is the actual existing schedule run. -/
theorem deepCopy_schedule_contents {H : HTy} {R A : RefTy} {E : Ty}
    (heap reached : Heap H) (input : HRef H A) (memory : (Ty.ref A).mapFree = true)
    (destination : HRef H R) (shape : ArrTy R E) (schedule : List SnapshotArgs)
    (execution : runCaptures heap destination shape schedule = some reached) :
    let snapshot := MVal.copyMToSt heap (T := .ref A) input
    let grown := snapshot.copyStToM heap memory
    ∃ after, runCaptures grown.heap (destination.wk grown.ext) shape schedule = some after ∧
      Heap.Keeps grown.ext reached after ∧
      MVal.copyMToSt after grown.val = snapshot.strip := by
  dsimp only
  obtain ⟨after, run, keeps, mirrored, _⟩ :=
    copy_schedule_transport heap reached (MVal.copyMToSt heap (T := .ref A) input)
      memory destination shape schedule execution
  exact ⟨after, run, keeps, mirror_contents after _ _ H.length mirrored⟩

namespace Controls
private abbrev R : RefTy := .array (.prim .uint)
private def u7 : PrimTy.uint.Denote := ⟨7, by decide⟩
private def u11 : PrimTy.uint.Denote := ⟨11, by decide⟩
private def u13 : PrimTy.uint.Denote := ⟨13, by decide⟩
private def u17 : PrimTy.uint.Denote := ⟨17, by decide⟩
private def initial : Heap [R] := (⟨[u7,u11,u13,u17],by decide⟩,())
private def old : HRef [R] R := ⟨0,rfl⟩
private def snapshot := MVal.copyMToSt initial (T := .ref R) old
private def grown := snapshot.copyStToM initial rfl
private def right : Heap [R] := (⟨[u7,u7,u11,u13],by decide⟩,())
private def left : Heap [R] := (⟨[u11,u13,u17,u17],by decide⟩,())

/-- A genuinely populated old heap inhabits the published deep-copy record. -/
theorem deep_inhabited : Nonempty (MemoryDeepCopyHeapCertificate initial old rfl) :=
  ⟨deepCopyHeap initial old rfl⟩

/-- Both overlap directions run on actual heaps; an invalid endpoint refuses,
and an empty schedule changes no object. -/
theorem overlap_runs :
    runCaptures initial old .dyn [(0,3,1)] = some right ∧
    runCaptures initial old .dyn [(1,4,0)] = some left ∧
    runCaptures initial old .dyn [(0,5,0)] = none ∧
    runCaptures initial old .dyn [] = some initial :=
  ⟨by with_unfolding_all rfl, by with_unfolding_all rfl,
    by with_unfolding_all rfl, rfl⟩

/-- The actually reached old alias changes, while the fresh root reads the
frozen initial snapshot. The cascading literal is rejected; this does not
execute a separate streaming-copy implementation. -/
theorem alias_and_deep_observations :
    ∃ after, runCaptures grown.heap (old.wk grown.ext) .dyn [(0,3,1)] = some after ∧
      (MObj.elems .dyn (after.get (old.wk grown.ext))).map (fun x => x.val) = [7,7,11,13] ∧
      MVal.copyMToSt after grown.val = snapshot.strip ∧ grown.val.id ≠ old.id ∧
      (MObj.elems .dyn (after.get (old.wk grown.ext))).map (fun x => x.val) ≠ [7,7,7,7] := by
  obtain ⟨after, execution, keeps, contents⟩ :=
    deepCopy_schedule_contents initial right old rfl old .dyn [(0,3,1)] overlap_runs.1
  have observed : (MObj.elems .dyn (after.get (old.wk grown.ext))).map
      (fun x => x.val) = [7,7,11,13] := by
    rw [keeps old]
    decide +kernel
  refine ⟨after, execution, observed, contents, (deepCopyHeap initial old rfl).distinct, ?_⟩
  intro wrong
  have impossible : ¬ (([7,7,11,13] : List Int) = [7,7,7,7]) := by decide
  exact impossible (observed.symm.trans wrong)

/-- An empty live object also receives a genuinely fresh deep-copy identity. -/
theorem empty_deep_inhabited :
    let heap : Heap [R] := (⟨[], by decide⟩,())
    Nonempty (MemoryDeepCopyHeapCertificate heap old rfl) ∧
      ((MVal.copyMToSt heap (T := .ref R) old).copyStToM heap rfl).val.id = 1 := by
  exact ⟨⟨deepCopyHeap _ old rfl⟩, by decide +kernel⟩

end Controls
#print axioms Controls.deep_inhabited
#print axioms Controls.overlap_runs
#print axioms Controls.alias_and_deep_observations
#print axioms Controls.empty_deep_inhabited
#print axioms storageHeapLegacy
#print axioms deepCopyHeap
#print axioms deepCopy_schedule_contents
end Solidity.Backend.MemoryCopies
