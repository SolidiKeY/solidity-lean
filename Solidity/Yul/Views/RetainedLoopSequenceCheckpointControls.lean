import Solidity.Yul.Views.RetainedLoopSequenceCheckpoint
import Solidity.Yul.Views.RetainedLoopSequenceControls

/-! Explicit rollback after actual growth/shrink restores the original Source
state, journal and five-entry inventory. Old-map reconstruction uses the original
saved complement, not an inferred residual rollback. These are fresh primitive
runs and not arbitrary-call/heap rollback or compiler adequacy. -/
namespace Solidity.Yul.Views.Controls

def rflqcRun (G : Source.Glob agEnv) (flag : Bool) :=
  RetainedLoopSequenceCheckpoint.rollbackSequence packedStepFrame rhOp rflqOp (rflswState G flag) .timeout

def rflqcStatic (G : Source.Glob agEnv) (flag : Bool) :=
  RetainedLoopSequenceCheckpoint.rollbackSequence rflswStaticFrame rhOp rflqOp (rflswState G flag) .timeout

theorem rflqc_restored (G : Source.Glob agEnv) (flag : Bool) :
    rflqcRun G flag=(.error .timeout,rflswState G flag) := by
  unfold rflqcRun
  rw [RetainedLoopSequenceCheckpoint.rollback_result]
  rfl

theorem rflqc_static (G : Source.Glob agEnv) (flag : Bool) :
    rflqcStatic G flag=(.error (.revert []),rflswState G flag) := by
  unfold rflqcStatic
  rw [RetainedLoopSequenceCheckpoint.rollback_result]
  rfl

theorem rflqc_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflqcRun G flag).2=
      some ((rfliImage G flag).snapshot rhRaw0) := by
  rw [rflqc_restored]
  exact rfli_source_inventory G flag

/-- The initial complement is an explicit remembered input to old-map encoding. -/
theorem rflqc_old_map (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhRaw0) ((rflqcRun G flag).2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhRaw0) rhRaw0)=some rhRaw0 := by
  rw [rflqc_restored]
  exact rfli_reencode G flag

theorem rflqc_journal (G : Source.Glob agEnv) (flag : Bool) :
    (rflqcRun G flag).2.2.ex.journal=(rflswState G flag).2.ex.journal := by
  rw [rflqc_restored]

theorem rflqc_reject_shrunk_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflqcRun G flag).2≠
      some ((rfliImage G flag).snapshot rflqRaw) := by
  rw [rflqc_inventory]
  intro same
  have counts := congrArg List.length (Option.some.inj same)
  rw [(rflrf_counts G flag).1,rflq_count G flag] at counts
  omega

end Solidity.Yul.Views.Controls
