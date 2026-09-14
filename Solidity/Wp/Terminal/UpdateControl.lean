import Solidity.Wp.Terminal.Vocab

/-!
# Terminal-rule updates: control

`revertBox`/`revertDiamond`, `assertSimple`, `requireSimple`,
`transferNoCallback`.  Each theorem is `execStmt s stmt = terminalUpdate r
stmt s` under the rule's guard.
-/

namespace Solidity
namespace Wp

open Semantics Rules

theorem revertBox_update (s : State) (msg : Option WrappedExpr)
    (_hcond : (ruleEffect .revertBox).cond (Stmt.revert msg)) :
    execStmt s (Stmt.revert msg) =
      terminalUpdate .revertBox (Stmt.revert msg) s := by
  rw [execStmt]; rfl

theorem revertDiamond_update (s : State) (msg : Option WrappedExpr)
    (_hcond : (ruleEffect .revertDiamond).cond (Stmt.revert msg)) :
    execStmt s (Stmt.revert msg) =
      terminalUpdate .revertDiamond (Stmt.revert msg) s := by
  rw [execStmt]; rfl

/-- The guard (`isSimple c`) is what makes the condition a pure read. -/
theorem assertSimple_update (s : State) (c : WrappedExpr)
    (hcond : (ruleEffect .assertSimple).cond (Stmt.assertStmt c)) :
    execStmt s (Stmt.assertStmt c) =
      terminalUpdate .assertSimple (Stmt.assertStmt c) s := by
  have hc : isSimple c := hcond
  show execStmt s (Stmt.assertStmt c) = assertUpd c s
  rw [execStmt, evalValue_readVal s c (terminalRhsB_of_simple hc)]
  simp only [assertUpd, bind, Except.bind, Except.map]
  cases readVal s c with
  | error e => rfl
  | ok v =>
      cases v with
      | int n => rfl
      | bool b => cases b <;> rfl

theorem requireSimple_update (s : State) (c : WrappedExpr)
    (hcond : (ruleEffect .requireSimple).cond (Stmt.requireStmt c)) :
    execStmt s (Stmt.requireStmt c) =
      terminalUpdate .requireSimple (Stmt.requireStmt c) s := by
  have hc : isSimple c := hcond
  show execStmt s (Stmt.requireStmt c) = assertUpd c s
  rw [execStmt, evalValue_readVal s c (terminalRhsB_of_simple hc)]
  simp only [assertUpd, bind, Except.bind, Except.map]
  cases readVal s c with
  | error e => rfl
  | ok v =>
      cases v with
      | int n => rfl
      | bool b => cases b <;> rfl

theorem transferNoCallback_update (s : State) (recipient amount : WrappedExpr)
    (hcond : (ruleEffect .transferNoCallback).cond
      (Stmt.transfer recipient amount)) :
    execStmt s (Stmt.transfer recipient amount) =
      terminalUpdate .transferNoCallback (Stmt.transfer recipient amount) s := by
  have hc : isSimple recipient ∧ isSimple amount := hcond
  show execStmt s (Stmt.transfer recipient amount) = transferUpd recipient amount s
  rw [execStmt, evalInt_simple s recipient hc.1]
  simp only [transferUpd, bind, Except.bind, Except.map]
  cases simpleInt s recipient with
  | error e => rfl
  | ok addr =>
      simp only [evalInt_simple s amount hc.2, Except.map]
      cases simpleInt s amount with
      | error e => rfl
      | ok amt => rfl

end Wp
end Solidity
