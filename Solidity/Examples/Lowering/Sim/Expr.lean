import Solidity.Correctness.Lowering.Sim.Expr.Strength

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

/-- info: 'Solidity.Correctness.Lowering.Sim.simulates_of_exprCases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Correctness.Lowering.Sim.simulates_of_exprCases

end Solidity.Examples.Lowering.Sim.Expr
