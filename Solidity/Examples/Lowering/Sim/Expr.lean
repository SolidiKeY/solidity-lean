import Solidity.Correctness.Lowering.Sim.Expr.Strength
import Solidity.Correctness.Lowering.Sim.Expr.Capture
import Solidity.Correctness.Lowering.Sim.Expr.Operand
import Solidity.Correctness.Lowering.Sim.Expr.Scope

/-!
# The expression cases: checks (ls2-expressions)

`Sim.ExprCases` at one concrete arm: the declaration arm of `hoistStmtWith`
at the record `passRec`, whose captures are arbitrary, so the case there is
the site obligation of an arbitrary run. No `expr_cases` exists to use: see
`Sim/Expr/Strength.lean`.
-/
namespace Solidity.Examples.Lowering.Sim.Expr

open Solidity.Correctness.Lowering.Sim
open Solidity.Goals (elabKernelTotal)

/-- The case at the declaration arm, read at the empty contract and the
empty captures: every body whose elaboration is empty and leaves the state
unchanged, from any raw input. -/
example [FreshNames] (kernel : elabKernelTotal) (exprs : ExprCases) (C : Contract)
    (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) : SiteSim C raw sc st [] st :=
  sites_of_exprCases kernel exprs C raw sc st [] st

/-- The frozen case at a concrete arm that is provable: `xs.push()++`. -/
example [FreshNames] (C : Contract) (rc : ElabRec C) (sim : RecSim C rc) (sc : ElabScope)
    (st st' : ECtx × Nat) (out : SProg C × RawStmt)
    (ran : Solidity.Goals.ElabRan
      (hoistStmtWith C rc (.pushIncDec .postInc (.name "xs"))) sc st out st') :
    hoistStmtQ C (.pushIncDec .postInc (.name "xs")) sc st out st' :=
  hoistStmt_pushIncDec_sat C rc sim _ _ sc st out st' ran

/-- An operand has no captures, at every record. -/
example [FreshNames] (C : Contract) (rc : ElabRec C) :
    hoistWith C rc (.name "x") = pure ([], .name "x") := hoist_name C rc "x"

/-- `unchecked { }` is `rc.elabBranch` under the unchecked scope. -/
example [FreshNames] (C : Contract) (rc : ElabRec C) :
    elabStmt1With C rc (.unchecked []) = (do
      withReader (fun sc => { sc with unchecked := true })
        (rc.elabBranch (← ElabM.lift (uncheckStmts [])))) := stmt1_unchecked C rc []

end Solidity.Examples.Lowering.Sim.Expr
