import Solidity.Yul.ClosedRun
import Solidity.Yul.Checks.ClosedPure

namespace Solidity.Yul.Checks.ClosedRun
open Solidity.Yul.Closed
open Solidity.Yul.Checks.ClosedPure
open Solidity.Yul.Checks.ClosedFunctions

def mulDivRootD : WordStmtD Solidity.Yul.Checks.Static.mulDiv :=
  .functions (.cons mulDivD .nil) (.assign (.call .here (fun _ => .literal)))

example : (evalStmt 10 .nil True.intro Solidity.Yul.Checks.Static.mulDiv mulDivRootD.profile
    (fun _ => word 999)).map (fun out => (out.vars 0).val) = some 70 := by decide

def countdownCall : Stmt [recursiveSig] [] ⟨false, false⟩ 1 :=
  .assign (fun _ => .«local» 0) (.call .here (fun _ => .literal (word 4)))
def countdownCallD : WordStmtD countdownCall := .assign (.call .here (fun _ => .literal))
example : (evalStmt 18 recursiveEnv recursiveD.profile countdownCall countdownCallD.profile
    (fun _ => word 999)).isNone = true := by decide
example : (evalStmt 19 recursiveEnv recursiveD.profile countdownCall countdownCallD.profile
    (fun _ => word 999)).map (fun out => ((out.vars 0).val, out.flow.isNormal)) = some (0, true) := by decide

example : (evalStmt 5 .nil True.intro Solidity.Yul.Checks.Static.loop loopD.profile
    (fun _ => word 0)).isNone = true := by decide
example : (evalStmt 6 .nil True.intro Solidity.Yul.Checks.Static.loop loopD.profile
    (fun _ => word 0)).map (fun out => ((out.vars 0).val, out.flow.isNormal)) = some (1, true) := by decide

def zeroDivCall : Stmt [⟨3, 1⟩] [] ⟨false, false⟩ 1 :=
  .assign (fun _ => .«local» 0) (.call .here
    (fun i => .literal (word (if i.val = 0 then 21 else if i.val = 1 then 10 else 0))))
def zeroDivCallD : WordStmtD zeroDivCall := .assign (.call .here (fun _ => .literal))
example : (evalStmt 10 mulDivEnv mulDivEnvironmentD.profile zeroDivCall zeroDivCallD.profile
    (fun _ => word 999)).map (fun out => ((out.vars 0).val, out.flow.isNormal)) = some (0, true) := by decide

def swapSig : Sig := ⟨2, 2⟩
def swapBody : Stmt [swapSig] [] ⟨true, false⟩ 4 :=
  .seq (.assign (fun _ => .«local» 2) (.«local» 1))
    (.assign (fun _ => .«local» 3) (.«local» 0))
def swapBodyD : WordStmtD swapBody := .seq (.assign (.local 1)) (.assign (.local 0))
def swapEnv : FunctionEnv [swapSig] := .group [swapSig] .nil (.cons swapBody .nil)
def swapEnvD : WordEnvD swapEnv := .group .nil (.cons swapBodyD .nil)
def swapCall : Stmt [swapSig] [] ⟨false, false⟩ 2 :=
  .assign (fun i => .«local» i) (.call .here (fun i => .«local» i))
def swapCallD : WordStmtD swapCall := .assign (.call .here (fun i => .local i))
example : (evalStmt 8 swapEnv swapEnvD.profile swapCall swapCallD.profile
    (fun i => word (if i.val = 0 then 3 else 5))).map
    (fun out => ((out.vars 0).val, (out.vars 1).val)) = some (5, 3) := by decide

def untouchedReturns : Stmt [recursiveSig] [] ⟨true, false⟩ 2 := .leave
def untouchedEnv : FunctionEnv [recursiveSig] := .group [recursiveSig] .nil (.cons untouchedReturns .nil)
def untouchedD : WordEnvD untouchedEnv := .group .nil (.cons .leave .nil)
example : (evalStmt 6 untouchedEnv untouchedD.profile countdownCall countdownCallD.profile
    (fun _ => word 999)).map (fun out => ((out.vars 0).val, out.flow.isNormal)) = some (0, true) := by decide

def divergeSig : Sig := ⟨0, 0⟩
def divergeBody : Stmt [divergeSig] [] ⟨true, false⟩ 0 :=
  .discard (.call .here Fin.elim0)
def divergeBodyD : WordStmtD divergeBody :=
  .discard (.call .here (fun i => Fin.elim0 i))
def divergeEnv : FunctionEnv [divergeSig] := .group [divergeSig] .nil (.cons divergeBody .nil)
def divergeEnvD : WordEnvD divergeEnv := .group .nil (.cons divergeBodyD .nil)
def divergeCall : Expr [divergeSig] [] 0 0 := .call .here Fin.elim0
def divergeCallD : WordExprD divergeCall := .call .here (fun i => Fin.elim0 i)
example : (evalExpr 24 divergeEnv divergeEnvD.profile divergeCall divergeCallD.profile Fin.elim0).isNone = true := by decide

/-- A selected arm must propagate exhaustion rather than taking the fallback. -/
def switchTimeout : Stmt [divergeSig] [] ⟨false, false⟩ 1 :=
  .switch (.literal (word 1))
    (.cons (word 1) (.discard (.call .here Fin.elim0)) .nil)
    (.assign (fun _ => .«local» 0) (.literal (word 99)))
def switchTimeoutD : WordStmtD switchTimeout :=
  .switch .literal (.cons (.discard (.call .here (fun i => Fin.elim0 i))) .nil)
    (.assign .literal)
example : (evalStmt 12 divergeEnv divergeEnvD.profile switchTimeout switchTimeoutD.profile
    (fun _ => word 0)).isNone = true := by decide

def switchValue (selector : Word) : Stmt [] [] ⟨false, false⟩ 1 :=
  .switch (.literal selector)
    (.cons (word 1) (.assign (fun _ => .«local» 0) (.literal (word 7))) .nil)
    (.assign (fun _ => .«local» 0) (.literal (word 99)))
def switchValueD (selector : Word) : WordStmtD (switchValue selector) :=
  .switch .literal (.cons (.assign .literal) .nil) (.assign .literal)
example : (evalStmt 8 .nil True.intro (switchValue (word 1)) (switchValueD _).profile
    (fun _ => word 0)).map (fun out => (out.vars 0).val) = some 7 := by decide
example : (evalStmt 8 .nil True.intro (switchValue (word 2)) (switchValueD _).profile
    (fun _ => word 0)).map (fun out => (out.vars 0).val) = some 99 := by decide

/-- Leave escapes the binder and the following sequence while preserving an old-slot write. -/
def scopedLeave : Stmt [] [] ⟨true, false⟩ 1 :=
  .seq (.let_ 1 (.literal (word 7))
    (.seq (.assign (fun _ => .«local» 1) (.«local» 0)) .leave))
    (.assign (fun _ => .«local» 0) (.literal (word 99)))
def scopedLeaveD : WordStmtD scopedLeave :=
  .seq (.let_ .literal (.seq (.assign (.local 0)) .leave)) (.assign .literal)
example : (evalStmt 10 .nil True.intro scopedLeave scopedLeaveD.profile
    (fun _ => word 0)).map (fun out => ((out.vars 0).val, out.flow.isNormal)) =
      some (7, false) := by decide

def zeroLeave : Stmt [] [] ⟨true, false⟩ 1 :=
  .zero 1 (.seq (.assign (fun _ => .«local» 1) (.literal (word 42))) .leave)
def zeroLeaveD : WordStmtD zeroLeave := .zero (.seq (.assign .literal) .leave)
example : (evalStmt 8 .nil True.intro zeroLeave zeroLeaveD.profile
    (fun _ => word 0)).map (fun out => ((out.vars 0).val, out.flow.isNormal)) =
      some (42, false) := by decide

def voidBody : Stmt [divergeSig] [] ⟨true, false⟩ 0 := .leave
def voidEnv : FunctionEnv [divergeSig] := .group [divergeSig] .nil (.cons voidBody .nil)
def voidEnvD : WordEnvD voidEnv := .group .nil (.cons .leave .nil)
def voidCall : Stmt [divergeSig] [] ⟨false, false⟩ 1 :=
  .discard (.call .here Fin.elim0)
def voidCallD : WordStmtD voidCall := .discard (.call .here (fun i => Fin.elim0 i))
example : (evalStmt 6 voidEnv voidEnvD.profile voidCall voidCallD.profile
    (fun _ => word 123)).map (fun out => ((out.vars 0).val, out.flow.isNormal)) =
      some (123, true) := by decide

/-- This recursive zero-result call never completes at any finite horizon. -/
theorem diverge_all (fuel : Nat) (vars : Values 0) :
    evalExpr fuel divergeEnv divergeEnvD.profile divergeCall divergeCallD.profile vars = none := by
  induction fuel using Nat.strongRecOn generalizing vars with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ k =>
        change Option.bind (Option.bind
          (evalExpr k divergeEnv divergeEnvD.profile divergeCall divergeCallD.profile
            (extendValues Fin.elim0 (fun _ : Fin 0 => word 0))) _) _ = none
        rw [ih k (by omega)]
        rfl

def increment (position : Fin 2) {c : Control} : Stmt [] [] c 2 :=
  .assign (fun _ => .«local» position)
    (.builtin (.pure .«add») (fun i =>
      if i.val = 0 then .«local» position else .literal (word 1)))
def incrementD (position : Fin 2) {c : Control} : WordStmtD (increment (c := c) position) :=
  .assign (.builtin (.pure .«add») (fun i => by
    split
    · exact .local position
    · exact .literal))
/-- The initializer increments slot 0 once; two iterations increment slot 1. -/
def preOnce : Stmt [] [] ⟨false, false⟩ 2 :=
  .for_ (increment 0) (.literal (word 1)) (increment 1)
    (.seq (.if_ (.builtin (.pure .eq) (fun i =>
      if i.val = 0 then .«local» 1 else .literal (word 2))) .break_) .continue_)
def preOnceD : WordStmtD preOnce :=
  .for_ (incrementD 0) .literal (incrementD 1)
    (.seq (.if_ (.builtin (.pure .eq) (fun i => by
      split
      · exact .local 1
      · exact .literal)) .break_) .continue_)
example : (evalStmt 12 .nil True.intro preOnce preOnceD.profile (fun _ => word 0)).map
    (fun out => ((out.vars 0).val, (out.vars 1).val, out.flow.isNormal)) =
      some (1, 2, true) := by decide

def leaveLoop : Stmt [] [] ⟨true, false⟩ 1 :=
  .for_ .skip (.literal (word 1))
    (.assign (fun _ => .«local» 0) (.literal (word 99)))
    (.seq (.assign (fun _ => .«local» 0) (.literal (word 7))) .leave)
def leaveLoopD : WordStmtD leaveLoop :=
  .for_ .skip .literal (.assign .literal) (.seq (.assign .literal) .leave)
example : (evalStmt 10 .nil True.intro leaveLoop leaveLoopD.profile (fun _ => word 0)).map
    (fun out => ((out.vars 0).val, out.flow.isNormal)) = some (7, false) := by decide

end Solidity.Yul.Checks.ClosedRun
