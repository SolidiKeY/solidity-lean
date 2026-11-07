import Solidity.Yul.Views.RetainedLoopSourceWrite
import Solidity.Yul.Views.RetainedLoopWritebackControls

/-! Separate actual applyOp runs on the retained loop endpoint. Nonstatic writes
reconstruct the changed map; static runs refuse and preserve the whole old state.
These runs do not sequence through the preceding failed loop or establish EVM
execution, allocator provenance, or general capture completeness. -/
namespace Solidity.Yul.Views.Controls

def rflswState (G : Source.Glob agEnv) (flag : Bool) := (rfliRun G flag).1.2

def rflswRun (G : Source.Glob agEnv) (flag : Bool) :=
  (Source.applyOp packedStepFrame rhOp).run (rflswState G flag)

def rflswStaticFrame : Source.Fr := { packedStepFrame with static := true }

def rflswStaticRun (G : Source.Glob agEnv) (flag : Bool) :=
  (Source.applyOp rflswStaticFrame rhOp).run (rflswState G flag)

/-- Full Source administration, including every non-ex field, is preserved. -/
theorem rflsw_success (G : Source.Glob agEnv) (flag : Bool) :
    rflswRun G flag=(.ok (),( (rflswState G flag).1,
      { (rflswState G flag).2 with ex := (rflswState G flag).2.ex.apply rhOp })) := by
  rfl

theorem rflsw_connection (G : Source.Glob agEnv) (flag : Bool) :
    capturedSnapshotWriteback (rfliImage G flag) rhNextRaw ((rflswState G flag).2.ex.world.accounts account).storage=
      some (((rflswRun G flag).2.2.ex.world.accounts account).storage,
        packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw) :=
  RetainedLoopSourceWrite.source_connection packedStepFrame (rfliImage G flag) rhNextRaw (rflswState G flag)
    rhOp rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflsw_reencode (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhNextRaw) ((rflswRun G flag).2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw)=some rhNextRaw :=
  RetainedLoopSourceWrite.source_reencode packedStepFrame (rfliImage G flag) rhNextRaw (rflswState G flag)
    rhOp rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflsw_static (G : Source.Glob agEnv) (flag : Bool) :
    rflswStaticRun G flag=(.error (.revert []),rflswState G flag) := by
  rfl

theorem rflsw_static_old_map (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhRaw0) ((rflswStaticRun G flag).2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhRaw0) rhRaw0)=some rhRaw0 := by
  rw [rflsw_static]
  exact rfli_reencode G flag

end Solidity.Yul.Views.Controls
