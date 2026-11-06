import Solidity.Yul.Views.DynamicJournalCaller

-- Serialize concrete proof elaboration to bound pending computed-state memory.
set_option Elab.async false

namespace Solidity.Yul.Views.Controls
def dynChildRequests : List PackedSlotRequest := [⟨false,account,1000,888⟩,⟨false,account,43,0⟩,
  ⟨true,account,0,⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788,by decide⟩⟩]

theorem dyn_child_ready : (dynChildRequests.mapM (preparePackedSlot dynRegistry dynTempRegistry)).isSome := by decide

def dynChildDataPlan := (preparePackedFrame (ps := dynRegistry) (ts := dynTempRegistry) packedStepFrame false 1000 888).get (by decide)
def dynChildLengthPlan := (preparePackedFrame (ps := dynRegistry) (ts := dynTempRegistry) packedStepFrame false 43 0).get (by decide)
def dynChildTempRaw : Roadmap.Word := ⟨0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd7788,by decide⟩
def dynChildTempPlan := (preparePackedFrame (ps := dynRegistry) (ts := dynTempRegistry) packedStepFrame true 0 dynChildTempRaw).get (by decide)
def dynChildPlans := [dynChildDataPlan,dynChildLengthPlan,dynChildTempPlan]

def dynChild := runPackedSource packedStepFrame dynChildPlans dynCaller.1.2 dynCaller.2
def dynChildCore : ResidualCompanion dynEnv.layout dynEnv.lay dynEnv.lay complementCarrierOwnership := ⟨dynChild.1.2.2.ex,dynChild.2⟩

theorem dyn_actual_child_sequence : dynChildCore = runPackedSlots dynCallerCore dynChildPlans :=
  runPackedSource_companion packedStepFrame dynChildPlans dynCaller.1.2 dynCaller.2 rfl

theorem dyn_child_rollback : companionRollback (companionEnter dynCallerCore account account 0 [] false) dynChildCore = dynCallerCore := by
  rw [dyn_actual_child_sequence]
  exact packed_frame_rollback _ _ _ _ _ _ _

theorem dyn_child_commit_outer_rollback : companionRollback (companionEnter dynCore account account 0 [] false)
    (companionCommit (companionEnter dynCallerCore account account 0 [] false) dynChildCore) = dynCore := by
  rw [dyn_actual_child_sequence,dyn_actual_caller_sequence]
  exact packed_frame_outer_commit _ _ _ _ _ _ _ _

theorem dyn_static_complete_error : runPackedSource {packedStepFrame with static := true} dynChildPlans dynCaller.1.2 dynCaller.2 =
    ((.error (.revert []),dynCaller.1.2),dynCaller.2) := rfl

/-- Actual late source index failure keeps the successfully written prefix;
frame rollback above is a distinct operation, not silent error restoration. -/
theorem dyn_late_index_error_keeps_prefix :
    (Source.indexLoc (E := dynEnv) packedStepFrame dynX.reference 2).run dynCaller.1.2 =
      (.error (.revert (Source.panicData .index)),dynCaller.1.2) := rfl

theorem dyn_frames_every_H (H : Source.HeapTy) (ok : Source.MemOK dynEnv H dynStorageState) :
    Source.MemOK dynEnv H dynChild.1.2 :=
  runPackedSource_MemOK packedStepFrame dynChildPlans dynCaller.1.2 dynCaller.2 H
    (runPackedSource_MemOK packedStepFrame dynPlans dynStorageState dynResidual H ok)

theorem dyn_frames_inhabited_MemOK : Source.MemOK dynEnv dynStorageState.2.heap.ty dynChild.1.2 := dyn_frames_every_H _ dyn_initial_MemOK

end Solidity.Yul.Views.Controls
