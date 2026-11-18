import Solidity.Correctness.Lowering.Sim.Expr.Strength
import Solidity.Correctness.Lowering.Sim.Expr.Frame
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

/-- `ExprCases` alone is the diagram's simulation. -/
example [FreshNames] (kernel : elabKernelTotal) (exprs : ExprCases) : diagram.Simulates :=
  simulates_of_exprCases kernel exprs

/-- Operands have no captures, at every record. -/
example [FreshNames] (C : Contract) (rc : ElabRec C) :
    hoistWith C rc (.name "x") = pure ([], .name "x") ∧
    hoistWith C rc (.bool true) = pure ([], .bool true) ∧
    hoistWith C rc (.env .msgSender) = pure ([], .env .msgSender) ∧
    hoistWith C rc (.num 7) = pure ([], .num 7) :=
  ⟨hoist_name C rc "x", hoist_bool C rc true, hoist_env C rc .msgSender, hoist_num C rc 7⟩

/-- `!x` is the captures of `x`, then `narrowCapture`; `x += 1` as a value is
the block of that statement. -/
example [FreshNames] (C : Contract) (rc : ElabRec C) :
    hoistWith C rc (.unop .not (.name "x")) = (do
      let (P, a) ← rc.hoist (.name "x")
      let (Q, e) ← narrowCapture C (.unop .not a)
      pure (P ++ Q, e)) ∧
    hoistWith C rc (.opAssign .add (.name "x") (.num 1)) = (do
      let Q ← rc.elabStmtsP [.opAssign .add (.name "x") (.num 1)]
      pure (Q, .name "x")) :=
  ⟨hoist_unop C rc .not (.name "x") rfl, hoist_opAssign C rc .add (.name "x") (.num 1)
    (by first | decide | simp [RawExpr.hasIncDec, RawExpr.any])⟩

/-- Statements without a capture arm, and the declaration arm (`rc.hoistTop`). -/
example [FreshNames] (C : Contract) (rc : ElabRec C) :
    hoistStmtWith C rc .revert = pure ([], .revert) ∧
    hoistStmtWith C rc (.unchecked []) = pure ([], .unchecked []) ∧
    hoistStmtWith C rc (.decl (.named "uint") "y" (some (.name "x"))) = (do
      let (P, r) ← rc.hoistTop (.name "x")
      pure (P, .decl (.named "uint") "y" (some r))) :=
  ⟨hoistStmt_revert C rc, hoistStmt_unchecked C rc [], hoistStmt_decl C rc _ "y" "x"⟩

/-- `checked { }` inside a scope of the same mode is `rc.elabBranch`. -/
example [FreshNames] (C : Contract) (rc : ElabRec C) (o : OFMode) :
    elabStmt1With C rc (.checked o []) = (do
      match (← read).overflow with
      | some o' =>
        if o' == o then rc.elabBranch []
        else throw "`checked { … }` and `ignoringOverflow { … }` do not nest in each other"
      | none =>
        let P ← withReader (fun sc => { sc with overflow := some o }) (rc.elabBranch [])
        let sc ← read
        let sf := sc.selfFrame || sc.retainFailureData
        pure (P.flatMap (SStmt.withOF o sf))) := stmt1_checked C rc o []

/-- `unchecked { }` is `rc.elabBranch` under the unchecked scope. -/
example [FreshNames] (C : Contract) (rc : ElabRec C) :
    elabStmt1With C rc (.unchecked []) = (do
      withReader (fun sc => { sc with unchecked := true })
        (rc.elabBranch (← ElabM.lift (uncheckStmts [])))) := stmt1_unchecked C rc []

/-- v2 (frame relation): the v1 cases give every v2 site, and the `push()++`
case holds from the v2 obligation of `rc.hoist`. -/
example [FreshNames] (kernel : elabKernelTotal) (exprs : ExprCases) (C : Contract)
    (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) : SiteSim₂ C raw sc st [] st :=
  sites₂_of_exprCases C kernel exprs raw sc st [] st

example [FreshNames] (C : Contract) (rc : ElabRec C)
    (hoist : ∀ e sc st out st', Solidity.Goals.ElabRan (rc.hoist e) sc st out st' →
      ∀ raw, SiteSim₂ C raw sc st out.1 st')
    (sc : ElabScope) (st st' : ECtx × Nat) (out : SProg C × RawStmt)
    (ran : Solidity.Goals.ElabRan
      (hoistStmtWith C rc (.pushIncDec .postInc (.name "xs"))) sc st out st') :
    SiteSim₂ C [] sc st out.1 st' :=
  hoistStmt_pushIncDec_sat₂ C rc hoist _ _ sc st out st' ran []

end Solidity.Examples.Lowering.Sim.Expr
