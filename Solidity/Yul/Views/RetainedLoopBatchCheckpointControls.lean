import Solidity.Yul.Views.RetainedLoopBatchCheckpoint
import Solidity.Yul.Views.RetainedLoopSequenceControls

/-! Three actual Source writes append three undo entries before ordinary halt;
explicit rollback restores the whole saved state. Nonempty static batches refuse,
while an empty static batch retains the requested halt. No residual or arbitrary
heap/call rollback is inferred. -/
namespace Solidity.Yul.Views.Controls

def rflbcOps : List (Source.Op agEnv.layout agEnv.lay agEnv.lay) := [rhOp,rflqOp,rhOp]

theorem rflbc_journal (G : Source.Glob agEnv) (flag : Bool) :
    ((RetainedLoopBatchCheckpoint.applyOpsThenHalt packedStepFrame rflbcOps .timeout).run
      (rflswState G flag)).2.2.ex.journal.length=(rflswState G flag).2.ex.journal.length+3 := by
  rw [RetainedLoopBatchCheckpoint.run_nonstatic packedStepFrame rflbcOps (rflswState G flag) .timeout rfl]
  rfl

theorem rflbc_restored (G : Source.Glob agEnv) (flag : Bool) :
    RetainedLoopBatchCheckpoint.rollbackBatch packedStepFrame rflbcOps (rflswState G flag) .timeout=
      (.error .timeout,rflswState G flag) := by
  rw [RetainedLoopBatchCheckpoint.rollback_result]
  rfl

theorem rflbc_static (G : Source.Glob agEnv) (flag : Bool) :
    RetainedLoopBatchCheckpoint.rollbackBatch rflswStaticFrame rflbcOps (rflswState G flag) .timeout=
      (.error (.revert []),rflswState G flag) := by
  rw [RetainedLoopBatchCheckpoint.rollback_result]
  rfl

theorem rflbc_empty_static (G : Source.Glob agEnv) (flag : Bool) :
    RetainedLoopBatchCheckpoint.rollbackBatch rflswStaticFrame [] (rflswState G flag) .timeout=
      (.error .timeout,rflswState G flag) := by
  rw [RetainedLoopBatchCheckpoint.rollback_result]
  rfl

end Solidity.Yul.Views.Controls
