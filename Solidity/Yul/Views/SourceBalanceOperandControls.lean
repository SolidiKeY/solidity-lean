import Solidity.Yul.Views.SourceBalanceOperands
import Solidity.Yul.Views.SourceBalanceControls

namespace Solidity.Yul.Views.Controls

def sboAddress : Roadmap.Address := ⟨6,by decide⟩
def sboAfter : Source.EMState Source.SemanticsExamples.E0 [.address false] :=
  ⟨.cons (.address sboAddress) .nil,sbSystem.2⟩

def sboAssign : Source.RExpr Source.SemanticsExamples.E0 [.address false] (.address false) :=
  .assign (.local .here) (.addressLit [6])

theorem sbo_actual_operand (n : Nat) : (Source.evalE sbGlob sbFrame (n+2) sboAssign).run sbSystem=
    (.ok (.val (.address sboAddress)),sboAfter) := rfl

theorem sbo_effectful_balance (n : Nat) : (Source.evalE sbGlob sbFrame (n+3) (.balance sboAssign)).run sbSystem=
    (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 9)),sboAfter) :=
  sourceBalanceOperand_run sbGlob sbFrame (n+2) sboAssign sbSystem sboAfter sboAddress (sbo_actual_operand n)

theorem sbo_does_not_restore_local : sboAfter.1.get Source.Idx.here≠sbSystem.1.get Source.Idx.here := by
  intro same
  have values := congrArg Source.Val.word same
  exact (by decide : (some (addressInputWord sboAddress))≠some (addressInputWord sbAddress)) values

theorem sbo_does_not_read_old_address : sourceObservedBalance sbGlob sbSystem sbAddress=77 ∧
    sourceObservedBalance sbGlob sboAfter sboAddress=9 := ⟨rfl,rfl⟩

/-- The condition successfully changes a boolean local; the selected deeply
nested address branch times out. No extra horizon is granted to rescue it. -/
def sboLateBefore : Source.EMState Source.SemanticsExamples.E0 [.bool,.address false] :=
  ⟨.cons (.bool false) sbSystem.1,sbSystem.2⟩
def sboLateAfter : Source.EMState Source.SemanticsExamples.E0 [.bool,.address false] :=
  ⟨.cons (.bool true) sbSystem.1,sbSystem.2⟩

def sboLate : Source.RExpr Source.SemanticsExamples.E0 [.bool,.address false] (.address false) :=
  .cond (.assign (.local .here) (.bool true))
    (.assign (.local (.there .here)) (.assign (.local (.there .here)) (.assign (.local (.there .here)) (.addressLit [7]))))
    (.local (.there .here))

theorem sbo_late_operand : (Source.evalE sbGlob sbFrame 4 sboLate).run sboLateBefore=(.error .timeout,sboLateAfter) := rfl

theorem sbo_late_balance : (Source.evalE sbGlob sbFrame 5 (.balance sboLate)).run sboLateBefore=(.error .timeout,sboLateAfter) :=
  sourceBalanceOperand_halt sbGlob sbFrame 4 sboLate sboLateBefore sboLateAfter .timeout sbo_late_operand

theorem sbo_static_local_write (n : Nat) :
    (Source.evalE sbGlob {sbFrame with static:=true} (n+3) (.balance sboAssign)).run sbSystem=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 9)),sboAfter) :=
  sourceBalanceOperand_run sbGlob _ (n+2) sboAssign sbSystem sboAfter sboAddress rfl

theorem sbo_early_timeout : (Source.evalE sbGlob sbFrame 1 (.balance sboAssign)).run sbSystem=(.error .timeout,sbSystem) :=
  sourceBalanceOperand_halt sbGlob sbFrame 0 sboAssign sbSystem sbSystem .timeout rfl

theorem sbo_wrong_late_prefix : sboLateAfter≠sboLateBefore := by
  intro same
  have eq := congrArg (fun s : Source.EMState Source.SemanticsExamples.E0 [.bool,.address false] => s.1.get Source.Idx.here) same
  have impossible : true=false := Source.Val.bool.inj eq
  cases impossible

end Solidity.Yul.Views.Controls
