import Solidity.Source.TypingExamples
import Solidity.Source.Semantics


namespace Solidity.Source.Ledger

open Solidity.Source Solidity.Source.TypingExamples

inductive SemStatus where
  | evaluated
  | gap (stage reason : String)
  deriving DecidableEq, Repr

def semExprCoverage (k : Ctor) : Option SemStatus :=
  match exprCoverage k with
  | some .typed | some (.operand _ _) => some .evaluated
  | some (.deferred _ _) =>
    match k with
    | .callOptions => some (.gap "S02" "only `{value: v}` on an external call is typed and evaluated (`extCall`)")
    | .metaType => some (.gap "S04.02" "type(T) members read the artifact table")
    | .new => some (.gap "S03" "contract creation is not typed; `new T[](n)` of one-word `T`, `new bytes(n)`, `new string(n)` are (newArray, FU2-B)")
    | _ => some (.gap "S02" "deferred by S01")
  | none => none

def semStmtCoverage (k : Ctor) : Option SemStatus :=
  match stmtCoverage k with
  | some .typed | some (.operand _ _) => some .evaluated
  | some (.deferred stage reason) =>
    match k with
    | .assembly => some (.gap "S00" "excluded; the canonical rethrow is typed and evaluated (`RStmt.rethrow`)")
    | _ => some (.gap stage reason)
  | none => none

theorem semExprCoverage_total (e : Syn .expr) : (semExprCoverage e.ctor).isSome = true := by
  cases e <;> rfl

theorem semStmtCoverage_total {k : SCtx} (s : Syn (.stmt k)) : (semStmtCoverage s.ctor).isSome = true := by
  cases s <;> rfl

theorem semExprCoverage_of_typed (k : Ctor) (h : exprCoverage k = some .typed) :
    semExprCoverage k = some .evaluated := by
  simp only [semExprCoverage, h]

theorem semStmtCoverage_of_typed (k : Ctor) (h : stmtCoverage k = some .typed) :
    semStmtCoverage k = some .evaluated := by
  simp only [semStmtCoverage, h]

theorem semExprCoverage_of_operand (k p : Ctor) (r : String) (h : exprCoverage k = some (.operand p r)) :
    semExprCoverage k = some .evaluated := by
  simp only [semExprCoverage, h]

def semExprGaps : List Ctor :=
  [.callOptions, .metaType, .new]

def deferred (k : Ctor) : Bool :=
  match exprCoverage k with
  | some (.deferred _ _) => true
  | _ => false

theorem semExprGaps_spec (k : Ctor) : semExprGaps.contains k = deferred k := by
  cases k <;> rfl

end Solidity.Source.Ledger
