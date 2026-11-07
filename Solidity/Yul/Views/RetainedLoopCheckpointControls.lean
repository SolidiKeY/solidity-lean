import Solidity.Yul.Views.RetainedLoopCheckpoint
import Solidity.Yul.Views.RetainedLoopRefreshControls

/-! Explicitly rolling back a fresh checked write restores the full retained
endpoint state and its old inventory/map. Ordinary late-halt persistence remains
a separate proved behavior; this adapter adds no automatic rollback semantics. -/
namespace Solidity.Yul.Views.Controls

def rflrbRun (G : Source.Glob agEnv) (flag : Bool) :=
  RetainedLoopCheckpoint.rollbackApply packedStepFrame rhOp (rflswState G flag)

def rflrbStatic (G : Source.Glob agEnv) (flag : Bool) :=
  RetainedLoopCheckpoint.rollbackApply rflswStaticFrame rhOp (rflswState G flag)

theorem rflrb_restored (G : Source.Glob agEnv) (flag : Bool) :
    rflrbRun G flag=(.ok (),rflswState G flag) := by
  unfold rflrbRun
  rw [RetainedLoopCheckpoint.rollback_result]
  rfl

theorem rflrb_static (G : Source.Glob agEnv) (flag : Bool) :
    rflrbStatic G flag=(.error (.revert []),rflswState G flag) := by
  unfold rflrbStatic
  rw [RetainedLoopCheckpoint.rollback_result]
  rfl

theorem rflrb_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflrbRun G flag).2=
      some ((rfliImage G flag).snapshot rhRaw0) := by
  rw [rflrb_restored]
  exact rfli_source_inventory G flag

theorem rflrb_old_map (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhRaw0) ((rflrbRun G flag).2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhRaw0) rhRaw0)=some rhRaw0 := by
  rw [rflrb_restored]
  exact rfli_reencode G flag

theorem rflrb_old_journal (G : Source.Glob agEnv) (flag : Bool) :
    (rflrbRun G flag).2.2.ex.journal=(rflswState G flag).2.ex.journal := by
  rw [rflrb_restored]

/-- The changed inventory cannot be reused after the explicit rollback. -/
theorem rflrb_reject_changed_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflrbRun G flag).2≠
      some ((rfliImage G flag).snapshot rhNextRaw) := by
  rw [rflrb_inventory]
  intro same
  exact rflrf_shape_change G flag (Option.some.inj same)

end Solidity.Yul.Views.Controls
