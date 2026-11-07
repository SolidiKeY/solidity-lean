import Solidity.Yul.Views.ActualScalarFrame
import Solidity.Yul.Views.ActualScalarWriteControls

/-! Fixed retained registry controls tie actual scalar writes to the same
source/residual frame and whole-map encoding. Ownership is unchanged here;
no changing-inventory or heap/caller-local rollback is implied. -/
namespace Solidity.Yul.Views.Controls

def afBefore : ResidualCompanion agEnv.layout agEnv.lay agEnv.lay complementCarrierOwnership :=
  ⟨agShrink.2.2.ex,rhResidual⟩
def afAfter : ResidualCompanion agEnv.layout agEnv.lay agEnv.lay complementCarrierOwnership :=
  ⟨asWrite.1.2.2.ex,rhResidual⟩
def afFrame := companionEnter afBefore packedStepFrame.this packedStepFrame.sender
  packedStepFrame.value packedStepFrame.cd packedStepFrame.static

theorem af_whole_registry : finiteEncode rhOld (afAfter.source.world.accounts account).storage
    (fun q=>afAfter.residual.cells (complementKey false account q))=some asWrite.2 :=
  actualScalarWrite_registry_reencode packedStepFrame agShrink.2 rhOld rhC3
    (by rw [rh_old_list]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    ((packedSeparationCheck_iff _).mp rh_separated) rhRaw0 rh_view (Source.intWrap rcU16 154) rfl rfl rhResidual rfl

theorem af_rollback : companionRollback afFrame afAfter=afBefore :=
  actualScalarWrite_frame_rollback packedStepFrame agShrink.2 rhC3 (Source.intWrap rcU16 154) rhRaw0 rfl rhResidual

theorem af_rollback_raw : finiteEncode rhOld
    ((companionRollback afFrame afAfter).source.world.accounts account).storage
    (fun q=>(companionRollback afFrame afAfter).residual.cells (complementKey false account q))=some rhRaw0 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [af_rollback]
  exact rh_encode

def afSecond := actualScalarWrite packedStepFrame rhC3.path rhC3.codec rhC3.slot
  (Source.intWrap rcU16 308) asWrite.2 asWrite.1.2

theorem af_second_word : (afSecond.2 1000).val=308+88*65536+77*2^32+2^240 := rfl

theorem af_inner_rollback :
    companionRollback (companionEnter afAfter packedStepFrame.this packedStepFrame.sender
      packedStepFrame.value packedStepFrame.cd packedStepFrame.static)
      ⟨afSecond.1.2.2.ex,rhResidual⟩=afAfter :=
  actualScalarWrite_frame_rollback packedStepFrame asWrite.1.2 rhC3 (Source.intWrap rcU16 308) asWrite.2 rfl rhResidual

theorem af_child_commit_outer_rollback :
    companionRollback afFrame
      (companionCommit (companionEnter afAfter packedStepFrame.this packedStepFrame.sender
        packedStepFrame.value packedStepFrame.cd packedStepFrame.static)
        ⟨afSecond.1.2.2.ex,rhResidual⟩)=afBefore :=
  actualScalarWrite_outer_commit_rollback packedStepFrame agShrink.2 rhC3 rhC3
    (Source.intWrap rcU16 154) (Source.intWrap rcU16 308) rhRaw0 rfl rhResidual

theorem af_wrong_unreverted_cell : (afAfter.source.world.accounts account).storage.read rlPath≠
    (afBefore.source.world.accounts account).storage.read rlPath := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro same
  have numeric := congrArg (fun v : Option (Source.Val agEnv.layout (.int rcU16)) =>
    match v with | some (.int x _) => x | _=>0) same
  exact (by decide : (154 : Int)≠77) numeric
end Solidity.Yul.Views.Controls
