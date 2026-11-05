import Solidity.Yul.Views.RetainedLoopBatchRefresh
import Solidity.Yul.Views.RetainedLoopBatchCheckpointControls

/-! A real grow/shrink/regrow batch reconstructs its final six-entry image.
Its reached inventory differs from the five-entry image after explicit rollback;
ordinary halt does not undo the batch. The same final snapshot complement is
used for reconstruction, with no general compiler or residual adequacy claim. -/
namespace Solidity.Yul.Views.Controls

def rflbrRun (G : Source.Glob agEnv) (flag : Bool) :=
  (RetainedLoopBatchCheckpoint.applyOpsThenHalt packedStepFrame rflbcOps .timeout).run (rflswState G flag)

theorem rflbr_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflbrRun G flag).2=
      some ((rfliImage G flag).snapshot rhNextRaw) := by
  exact RetainedLoopBatchRefresh.final_inventory packedStepFrame (rfliImage G flag) rhNextRaw
    (rflswState G flag) [rhOp,rflqOp] rhOp .timeout rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflbr_reencode (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhNextRaw) ((rflbrRun G flag).2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw)=some rhNextRaw := by
  exact RetainedLoopBatchRefresh.final_reencode packedStepFrame (rfliImage G flag) rhNextRaw
    (rflswState G flag) [rhOp,rflqOp] rhOp .timeout rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflbr_not_rolled_back (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflbrRun G flag).2≠
      (rfliImage G flag).sourceInventory? (F:=packedStepFrame)
        (RetainedLoopBatchCheckpoint.rollbackBatch packedStepFrame rflbcOps (rflswState G flag) .timeout).2 := by
  rw [rflbr_inventory,rflbc_restored]
  have old := rfli_source_inventory G flag
  change (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflswState G flag)=_ at old
  rw [old]
  intro same
  exact rflrf_shape_change G flag (Option.some.inj same).symm

end Solidity.Yul.Views.Controls
