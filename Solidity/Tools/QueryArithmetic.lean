import Solidity.Calculus.QueryArithmetic
import Solidity.Tools.CompleteVerification

/-!
# Compiled arithmetic selection with finite query replay

The arithmetic certificate includes alias consistency. Compiled exploration
exports finite natural codes; a guarded check decodes typed occurrences and
reconstructs an actual counterstore. The closed query refutation is checked
independently by the kernel before the elaborator returns the witness.
-/

namespace Solidity.Tools

open Lean Meta Elab Term ReadRealization Linear

syntax (name := queryCountermodelTerm) "query_countermodel[" term "]" : term

/-- Replay externally supplied codes with an independent kernel check of
the actual query refutation. Inconsistent aliases cannot pass this gate. -/
def queryCountermodelOfCodes (r : Expr) (xs : List Nat) : MetaM Expr := withCurrHeartbeats do
  let check ← mkAppM ``Query.Arithmetic.checkCodes #[r, toExpr xs]
  let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.false))
    (← mkEq check (mkConst ``Bool.false))
  let cm ← mkAppM ``Query.Arithmetic.countermodelOfCodes #[r, toExpr xs, h]
  let proof ← mkAppM ``Subtype.property #[cm]
  let _ ← checkCertificate (← inferType proof) proof
  return cm

/-- Compute one arithmetic traversal and quote only its finite assignment.
A valid arithmetic sentence has no countermodel to return. -/
def queryCountermodel (r : Expr) : MetaM Expr := withCurrHeartbeats do
  let formula ← mkAppM ``Query.Arithmetic.formula #[r]
  let guarded ← mkAppM ``TypedFormula.guarded #[formula]
  let data ← mkAppM ``arithmeticData #[guarded]
  let result ← unsafe evalExpr (Option (List Nat)) (← inferType data) data
  let some xs := result | throwError "query_countermodel: the certified query is valid"
  queryCountermodelOfCodes r xs

@[term_elab queryCountermodelTerm]
def elabQueryCountermodel : TermElab := fun stx _ => do
  queryCountermodel (← elabTerm stx[1] none)

end Solidity.Tools
