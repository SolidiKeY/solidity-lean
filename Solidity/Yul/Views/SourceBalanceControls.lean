import Solidity.Yul.Views.SourceBalanceReads
import Solidity.Source.SemanticsExamples

namespace Solidity.Yul.Views.Controls

def sbAddress : Roadmap.Address := ⟨5,by decide⟩
/-- Explicit synthetic event-sensitive input, NOT the approved monetary ledger
or a compiler/reachability witness. Generic theorems do not require this choice. -/
def sbGlob := { Source.SemanticsExamples.G0 .legacy with
  fixed := { Source.SemanticsExamples.toyFixed with ledger := fun initial events address => if events.isEmpty then initial address else 9 }
  balance0 := fun _ => 7 }

def sbBase : Source.EMState Source.SemanticsExamples.E0 [.address false] :=
  ⟨.cons (.address sbAddress) .nil,Source.SemanticsExamples.s0⟩

def sbExternal : Source.EMState Source.SemanticsExamples.E0 [.address false] :=
  ⟨sbBase.1,{sbBase.2 with ex := sbBase.2.ex.apply (.account sbAddress (fun account => {account with balance := 77}))}⟩

def sbHistory : Source.EMState Source.SemanticsExamples.E0 [.address false] :=
  ⟨sbExternal.1,{sbExternal.2 with events := [.credit sbAddress 1]}⟩

def sbSystem : Source.EMState Source.SemanticsExamples.E0 [.address false] :=
  ⟨sbHistory.1,{sbHistory.2 with ex := sbHistory.2.ex.apply (.account sbAddress (fun account => {account with code := some 0}))}⟩

def sbFrame := { Source.SemanticsExamples.F0 with this := sbAddress }

theorem sb_branch_values : sourceObservedBalance sbGlob sbExternal sbAddress=7 ∧
    sourceObservedBalance sbGlob sbHistory sbAddress=9 ∧
    sourceObservedBalance sbGlob sbSystem sbAddress=77 := ⟨rfl,rfl,rfl⟩

theorem sb_actual_external (n : Nat) :
    (Source.evalE sbGlob sbFrame (n+2) (sourceBalanceExpr Source.Idx.here)).run sbExternal=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 7)),sbExternal) :=
  sourceBalanceLocal_run sbGlob sbFrame n sbExternal .here sbAddress rfl

theorem sb_actual_history (n : Nat) :
    (Source.evalE sbGlob sbFrame (n+2) (sourceBalanceExpr Source.Idx.here)).run sbHistory=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 9)),sbHistory) :=
  sourceBalanceLocal_run sbGlob sbFrame n sbHistory .here sbAddress rfl

theorem sb_actual_system (n : Nat) :
    (Source.evalE sbGlob sbFrame (n+2) (sourceBalanceExpr Source.Idx.here)).run sbSystem=
      (.ok (.val (uintValueOfWord Source.SemanticsExamples.E0.layout 77)),sbSystem) :=
  sourceBalanceLocal_run sbGlob sbFrame n sbSystem .here sbAddress rfl

theorem sb_target_self :
    (Backend.Environment.observe (sourceEnvironmentFrame sbGlob sbFrame (sourceObservedFunds sbGlob sbSystem)) .selfBalance).1.toNat=77 := by
  rw [sourceObserved_self_balance,environmentWord_nat]
  rfl

/-- A stored external account balance is NOT the owner's external observation. -/
theorem sb_not_stored_external : sourceObservedBalance sbGlob sbExternal sbAddress≠(sbExternal.2.ex.world.accounts sbAddress).balance := by decide

theorem sb_not_stale_history : sourceObservedBalance sbGlob sbExternal sbAddress≠sourceObservedBalance sbGlob sbHistory sbAddress := by decide

/-- Code presence, not existence in the program catalog, selects the branch. -/
theorem sb_code_not_catalog : sbGlob.prog.contracts=[] ∧ (sbSystem.2.ex.world.accounts sbAddress).code=some 0 := ⟨rfl,rfl⟩

theorem sb_timeout :
    (Source.evalE sbGlob sbFrame 0 (sourceBalanceExpr Source.Idx.here)).run sbSystem=(.error .timeout,sbSystem) := rfl

end Solidity.Yul.Views.Controls
