import Solidity.Wp.Terminal.Vocab

/-!
# Terminal-rule updates: control

`revertBox`/`revertDiamond`, `assertSimple`, `requireSimple`,
`transferNoCallbackBox`/`transferNoCallbackDiamond`.  Each theorem is `execStmt s stmt = terminalUpdate r
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

/-- The interpreter's transfer under the twins' shared guard (`isSimple
sadr ∧ isSimple se`): a negative amount is stuck, an uncovered one reverts,
otherwise the payment is booked. -/
theorem transfer_execStmt_eq_transferUpd (s : State)
    (recipient amount : WrappedExpr)
    (hc : isSimple recipient ∧ isSimple amount) :
    execStmt s (Stmt.transfer recipient amount) =
      transferUpd recipient amount s := by
  rw [execStmt, evalInt_simple s recipient hc.1]
  simp only [transferUpd, bind, Except.bind, Except.map]
  cases simpleInt s recipient with
  | error e => rfl
  | ok addr =>
      simp only [evalInt_simple s amount hc.2, Except.map]
      cases simpleInt s amount with
      | error e => rfl
      | ok amt => rfl

/-- The box twin.  KeY's box rule books the payment *unconditionally* — a
strengthening of the interpreter, which reverts when the balance does not
cover the amount.  This theorem is about the interpreter's behaviour
(`terminalUpdate` is the guarded `transferUpd`), not about the rule's stated
update; the gap is what keeps the rule out of `Update/TacletTable`'s bridges. -/
theorem transferNoCallbackBox_update (s : State) (recipient amount : WrappedExpr)
    (hcond : (ruleEffect .transferNoCallbackBox).cond
      (Stmt.transfer recipient amount)) :
    execStmt s (Stmt.transfer recipient amount) =
      terminalUpdate .transferNoCallbackBox (Stmt.transfer recipient amount) s :=
  transfer_execStmt_eq_transferUpd s recipient amount hcond

/-- The diamond twin: KeY owes the funds check as a separate obligation
(`funded(se)`) and books the payment on the other goal; the interpreter's
guarded update is the two together. -/
theorem transferNoCallbackDiamond_update (s : State) (recipient amount : WrappedExpr)
    (hcond : (ruleEffect .transferNoCallbackDiamond).cond
      (Stmt.transfer recipient amount)) :
    execStmt s (Stmt.transfer recipient amount) =
      terminalUpdate .transferNoCallbackDiamond (Stmt.transfer recipient amount) s :=
  transfer_execStmt_eq_transferUpd s recipient amount hcond

end Wp
end Solidity
