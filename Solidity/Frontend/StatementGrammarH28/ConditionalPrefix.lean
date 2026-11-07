import Solidity.Frontend.StatementGrammarH28.LoopCoverage
import Solidity.Frontend.StatementGrammarH28.NearestElse

/-! Exact parser equation for Boolean if headers, before any body is parsed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem if_bool_prefix (n : Nat) (k : SCtx) (b : Bool) (s : St) :
    stmt (n + 6) k (conditionInput .if_ b s) =
      ((do let body ← stmt (n + 5) k
           if ← eat (.kw .else_) then
             return Syn.ifStmt (.lit (.bool b)) body (.some (← stmt (n + 5) k))
           else return Syn.ifStmt (.lit (.bool b)) body .none) : P (Syn (.stmt k))) s := by
  rw [stmt]
  change (expr (n + 5) (boolBefore b .rparen s)).bind (fun p =>
    ((do expectP .rparen
         let body ← stmt (n + 5) k
         if ← eat (.kw .else_) then
           return Syn.ifStmt p.1 body (.some (← stmt (n + 5) k))
         else return Syn.ifStmt p.1 body .none) : P (Syn (.stmt k))) p.2) = _
  rw [bool_expr_rparen]
  rfl

/-- This is exactly the existing precedence node contract, not an additional
expression-uniqueness or successful-parser assumption. -/
theorem if_some_contract_iff {k : SCtx} (c : Syn .expr) (t e : Syn (.stmt k)) :
    (Syn.ifStmt c t (.some e)).precNode = true ↔ t.openIf = false := by
  change ((!t.openIf) = true) ↔ t.openIf = false
  cases t.openIf <;> decide

#print axioms if_bool_prefix
#print axioms if_some_contract_iff
end Solidity.Frontend.StatementGrammarH28
