import Solidity.Calculus.LeafArithmetic
import Solidity.Tools.CompleteVerification

/-!
# Compiled dependent-leaf countermodels

The source compiler generates occurrence and alias arithmetic. Compiled
exploration chooses only finite codes; the kernel checks the resulting
original-leaf refutation independently before the witness is returned.
-/

namespace Solidity.Tools

open Lean Meta Elab Term Decide Linear

syntax (name := leafCountermodelTerm) "leaf_countermodel[" term "]" : term

def leafCountermodelOfCodes (r : Expr) (xs : List Nat) : MetaM Expr := withCurrHeartbeats do
  let check ← mkAppM ``FlattenedArithmetic.checkCodes #[r, toExpr xs]
  let h := mkExpectedPropHint (← mkEqRefl (mkConst ``Bool.false))
    (← mkEq check (mkConst ``Bool.false))
  let cm ← mkAppM ``FlattenedArithmetic.countermodelOfCodes #[r, toExpr xs, h]
  let proof ← mkAppM ``FlattenedArithmetic.Countermodel.refutes #[cm]
  let _ ← checkCertificate (← inferType proof) proof
  return cm

def leafCountermodel (r : Expr) : MetaM Expr := withCurrHeartbeats do
  let encoding ← mkAppM ``FlattenedArithmetic.encoding #[r]
  let formula ← mkAppM ``LeafArithmetic.arithmetic #[encoding]
  let guarded ← mkAppM ``TypedFormula.guarded #[formula]
  let data ← mkAppM ``arithmeticData #[guarded]
  let result ← unsafe evalExpr (Option (List Nat)) (← inferType data) data
  let some xs := result | throwError "leaf_countermodel: the source leaf is valid"
  leafCountermodelOfCodes r xs

@[term_elab leafCountermodelTerm]
def elabLeafCountermodel : TermElab := fun stx _ => do
  leafCountermodel (← elabTerm stx[1] none)

end Solidity.Tools
