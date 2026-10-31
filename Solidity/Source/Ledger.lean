import Solidity.Source.TypingExamples
import Solidity.Source.Semantics

/-!
# The source-constructor ledger (S05)

Every expression and statement constructor of the source syntax
(`Syn`, S00) with its semantic status, checked mechanically against S01's
coverage (`TypingExamples.exprCoverage`, `stmtCoverage`, which classify
every constructor without a wildcard):

- a constructor S01 types has an interpreter arm: its derivations
  elaborate to `RExpr`/`RStmt` (`Typed.toR`, `StmtD.toR`, total), and the
  interpreter (`evalE`, `execS`, `Solidity/Source/Eval.lean`) matches every
  constructor of `RExpr`, `RLVal`, `RStmt` and `RItems` without a
  wildcard (Lean's exhaustiveness check).  An arm can still be `stuck` on
  some inputs (dynamic ABI decoding, calldata references, `fallback` with
  parameters, nested-array copies): `semExprCoverage_of_typed` is a
  classification, not a progress theorem;
- a constructor S01 defers stays a recorded gap with its stage, never an
  exclusion (G00's profile still contains it).

`semExprCoverage_of_typed` and `semStmtCoverage_of_typed` prove the first
point; `semExprCoverage_total` and `semStmtCoverage_total` that the ledger
is total; `semExprGaps` lists the gaps.
-/

namespace Solidity.Source.Ledger

open Solidity.Source Solidity.Source.TypingExamples

/-- A constructor's semantic status. -/
inductive SemStatus where
  /-- Typed by S01 and evaluated by S02/S03. -/
  | evaluated
  /-- Not yet typed, so not yet evaluated: a gap with its stage. -/
  | gap (stage reason : String)
  deriving DecidableEq, Repr

/-- The semantic status of an expression constructor. -/
def semExprCoverage (k : Ctor) : Option SemStatus :=
  match exprCoverage k with
  | some .typed => some .evaluated
  | some (.deferred _ _) =>
    match k with
    | .callOptions => some (.gap "S02" "only `{value: v}` on an external call is typed and evaluated (`extCall`)")
    | .slice => some (.gap "S02" "calldata slices: calldata references are not decoded")
    | .metaType => some (.gap "S04.02" "type(T) members read the artifact table")
    | .new => some (.gap "S03" "contract creation and `new T[](n)` are not typed")
    | .inlineArray => some (.gap "S02" "inline arrays are not typed")
    | .elemType => some (.gap "S02" "type names as values (abi.decode) are not typed")
    | _ => some (.gap "S02" "deferred by S01")
  | none => none

/-- The semantic status of a statement constructor. -/
def semStmtCoverage (k : Ctor) : Option SemStatus :=
  match stmtCoverage k with
  | some .typed => some .evaluated
  | some (.deferred stage reason) =>
    match k with
    | .assembly => some (.gap "S00" "excluded; the canonical rethrow is typed and evaluated (`RStmt.rethrow`)")
    | _ => some (.gap stage reason)
  | none => none

/-- **The ledger is total** on expressions. -/
theorem semExprCoverage_total (e : Syn .expr) : (semExprCoverage e.ctor).isSome = true := by
  cases e <;> rfl

/-- **The ledger is total** on statements. -/
theorem semStmtCoverage_total {k : SCtx} (s : Syn (.stmt k)) : (semStmtCoverage s.ctor).isSome = true := by
  cases s <;> rfl

/-- **Every typed expression constructor is evaluated.** -/
theorem semExprCoverage_of_typed (k : Ctor) (h : exprCoverage k = some .typed) :
    semExprCoverage k = some .evaluated := by
  simp only [semExprCoverage, h]

/-- **Every typed statement constructor is executed.** -/
theorem semStmtCoverage_of_typed (k : Ctor) (h : stmtCoverage k = some .typed) :
    semStmtCoverage k = some .evaluated := by
  simp only [semStmtCoverage, h]

/-- The expression constructors still without semantics. -/
def semExprGaps : List Ctor :=
  [.slice, .callOptions, .metaType, .new, .inlineArray, .elemType]

/-- Whether S01 defers a constructor. -/
def deferred (k : Ctor) : Bool :=
  match exprCoverage k with
  | some (.deferred _ _) => true
  | _ => false

/-- The gaps are exactly the constructors S01 defers. -/
theorem semExprGaps_spec (k : Ctor) : semExprGaps.contains k = deferred k := by
  cases k <;> rfl

end Solidity.Source.Ledger
