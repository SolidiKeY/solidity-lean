import Solidity.Yul.Views.RepeatedCellWrites
import Solidity.Yul.Views.PackedCellUpdateControls
import Solidity.Yul.Views.TransientCellUpdateControls

/-! Repeated real typed writes share one fixed frame and actual bank. Duplicate
writes still journal; equal-value static writes still refuse; empty traces do not.
Seeded retained payload and declared transient-root examples are separate cases. -/
namespace Solidity.Yul.Views.Controls

def rcwValues : List (Source.Val agEnv.layout (agEnv.cellTy pcuPath.path)) :=
  [pcuValue,pcuValue,Source.intWrap rcU16 7]
def rcwRun := (RepeatedCellWrites.program packedStepFrame pcuPath rcwValues).run rccRun.1.2

theorem rcw_reencode : finiteEncode (rccImage.snapshot rhRaw0) (rcwRun.2.2.ex.world.accounts account).storage
    (packedMask (rccImage.snapshot rhRaw0) rhRaw0)=some (RepeatedCellWrites.raw pcuPath rcwValues rhRaw0) :=
  RepeatedCellWrites.reencode packedStepFrame rccRun.1.2 _ pcuPath rlc_payload
    ((packedSeparationCheck_iff _).mp (rai_separated .legacy)) rhRaw0 rcc_view rcwValues rfl

theorem rcw_word : RepeatedCellWrites.raw pcuPath rcwValues rhRaw0 2000=(⟨7+2^240,by decide⟩ : Roadmap.Word) := by decide

theorem rcw_read : (Source.readLoc packedStepFrame (.stor ((agInner 1).go (.index 0)))).run rcwRun.2=
    (.ok (Source.intWrap rcU16 7),rcwRun.2) := rfl

theorem rcw_safe : Source.MemOK agEnv agState.2.heap.ty rcwRun.2 :=
  RepeatedCellWrites.MemOK packedStepFrame rccRun.1.2 pcuPath rcwValues _ ra_initial_safe

/-- Even the duplicate42 write is a real journaled operation. -/
theorem rcw_journal : rcwRun.2.2.ex.journal.length=rccRun.1.2.2.ex.journal.length+3 := by
  unfold rcwRun
  rw [RepeatedCellWrites.run _ _ _ _ rfl]
  exact Source.ExecState.journal_run _ _

theorem rcw_same_value_static :
    (RepeatedCellWrites.program {packedStepFrame with static:=true} pcuPath [Source.intWrap rcU16 99]).run rccRun.1.2=
      (.error (.revert []),rccRun.1.2) := RepeatedCellWrites.static _ _ _ _ [] rfl

theorem rcw_empty_static :
    (RepeatedCellWrites.program {packedStepFrame with static:=true} pcuPath []).run rccRun.1.2=(.ok (),rccRun.1.2) := rfl

def rcwResidual : ResidualJournal complementCarrierOwnership :=
  ⟨fun key => if key.transient then 0 else packedMask (rccImage.snapshot rhRaw0) rhRaw0 key.slot,[]⟩

theorem rcw_rollback : companionRollback
    (companionEnter (⟨rccRun.1.2.2.ex,rcwResidual⟩ : ResidualCompanion agEnv.layout agEnv.lay agEnv.lay complementCarrierOwnership)
      packedStepFrame.this packedStepFrame.sender packedStepFrame.value packedStepFrame.cd packedStepFrame.static)
    ⟨rcwRun.2.2.ex,rcwResidual⟩=⟨rccRun.1.2.2.ex,rcwResidual⟩ := RepeatedCellWrites.rollback _ _ _ _ _ rfl

def rcwTempValues : List (Source.Val rootEnv.layout (rootEnv.cellTy tcuPath.path)) :=
  [tcuValue,tcuValue,Source.intWrap unsigned16 9]
def rcwTempRun := (RepeatedCellWrites.program TransientSlotControls.frame tcuPath rcwTempValues).run TransientSlotControls.child.1.2

theorem rcw_temp_reencode : finiteEncode (rootTempRegistry account) (rcwTempRun.2.2.ex.transient.cells account)
    (packedMask (rootTempRegistry account) tcuRaw)=some (RepeatedCellWrites.raw tcuPath rcwTempValues tcuRaw) :=
  RepeatedCellWrites.reencode TransientSlotControls.frame TransientSlotControls.child.1.2 _ tcuPath tcu_member
    rootTempChecked.separated tcuRaw tcu_before rcwTempValues rfl

theorem rcw_temp_word : RepeatedCellWrites.raw tcuPath rcwTempValues tcuRaw 0=0xb6b60009 := by decide
end Solidity.Yul.Views.Controls
