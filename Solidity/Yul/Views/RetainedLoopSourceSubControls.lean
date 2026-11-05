import Solidity.Yul.Views.RetainedLoopSourceSub
import Solidity.Yul.Views.RetainedLoopSourceWriteControls

/-! A fresh primitive sub-write run uses empty child locals and saved caller
aliases, then halts with timeout. The write persists and reconstructs the changed
map. Static refusal precedes the later halt and preserves the complete input.
This does not resume the prior failed loop or model transaction rollback. -/
namespace Solidity.Yul.Views.Controls

def rflsubInitial (G : Source.Glob agEnv) (flag : Bool) : Source.EMState agEnv [agAliasTy,agAliasTy] :=
  (agShrink.2.1,(rflswState G flag).2)

def rflsubRun (G : Source.Glob agEnv) (flag : Bool) :=
  (RetainedLoopSourceSub.writeThenHalt (E:=agEnv) (Γ:=[agAliasTy,agAliasTy]) (Δ:=[])
    packedStepFrame rhOp Source.Locals.nil .timeout).run (rflsubInitial G flag)

def rflsubStatic (G : Source.Glob agEnv) (flag : Bool) :=
  (RetainedLoopSourceSub.writeThenHalt (E:=agEnv) (Γ:=[agAliasTy,agAliasTy]) (Δ:=[])
    rflswStaticFrame rhOp Source.Locals.nil .timeout).run (rflsubInitial G flag)

theorem rflsub_result (G : Source.Glob agEnv) (flag : Bool) :
    rflsubRun G flag=(.error .timeout,(agShrink.2.1,
      { (rflswState G flag).2 with ex := (rflswState G flag).2.ex.apply rhOp })) := by
  rfl

theorem rflsub_caller (G : Source.Glob agEnv) (flag : Bool) :
    (rflsubRun G flag).2.1=agShrink.2.1 := by
  rfl

theorem rflsub_reencode (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhNextRaw) ((rflsubRun G flag).2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw)=some rhNextRaw :=
  RetainedLoopSourceSub.halt_reencode packedStepFrame (rfliImage G flag) rhNextRaw agShrink.2.1
    Source.Locals.nil (rflswState G flag).2 rhOp .timeout rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflsub_journal (G : Source.Glob agEnv) (flag : Bool) :
    (rflsubRun G flag).2.2.ex.journal.length=(rflswState G flag).2.ex.journal.length+1 := by
  rfl

theorem rflsub_static (G : Source.Glob agEnv) (flag : Bool) :
    rflsubStatic G flag=(.error (.revert []),rflsubInitial G flag) := by
  rfl

end Solidity.Yul.Views.Controls
