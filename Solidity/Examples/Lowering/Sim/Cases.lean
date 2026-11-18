import Solidity.Correctness.Lowering.Sim.Match.Cases

/-!
# The case interface of the lowering diagram, used

Each declaration of `Sim/Match/Cases.lean` once: the instantiation of
`ElabKernelInduction` at `RecSim`, the families of some raw inputs, and the
cases with a loop hypothesis giving `diagram.Simulates`.
-/
namespace Solidity.Examples.Lowering.Sim.Cases

open Solidity.Goals (ElabSat ElabKernelInduction elabStmtsStep elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim

variable [FreshNames]

/-- **The instantiation**: `RecSim` is the conjunction that
`ElabKernelInduction` concludes, at `hoistQ`, `hoistStmtQ`, `stmtQ` (twice)
and `blockQ`; so the knot has it once the arms preserve it. -/
example (C : Contract) (rc : ElabRec C) (induction : ElabKernelInduction C rc)
    (step : ∀ r : ElabRec C, RecSim C r →
      ElabSat (hoistQ C) (hoistWith C r) ∧ ElabSat (hoistStmtQ C) (hoistStmtWith C r) ∧
      ElabSat (stmtQ C) (elabStmtPWith C r) ∧ ElabSat (stmtQ C) (elabStmt1With C r) ∧
      ElabSat (blockQ C) (elabStmtsStep C r)) : RecSim C rc :=
  induction (hoistQ C) (hoistStmtQ C) (stmtQ C) (stmtQ C) (blockQ C)
    fun r h s p o l => step r ⟨h, s, p, o, l⟩

example (C : Contract) (rc : ElabRec C) (induction : ElabKernelInduction C rc)
    (kernel : elabKernelTotal) (exprs : ExprCases) (stmts : StmtCases) (states : StateCases)
    (loops : ∀ r : ElabRec C, RecSim C r → StmtArm C r .loop) : RecSim C rc :=
  recSim_of_step C rc induction (step_of_cases C kernel exprs stmts states loops)

/-- The families of some raw inputs: a call on the right is a call, a loop is
no case, a jump has no constructor in the fragment. -/
example : stmtFamily .revert = .revert ∧
    stmtFamily (.assign (.name "x") (.call "f" [])) = .call ∧
    stmtFamily (.whileLoop {} (.bool true) []) = .loop ∧ stmtFamily .brk = .state ∧
    exprFamily (.binop .add (.num 1) (.num 2)) = .arith ∧ exprFamily (.call "f" []) = .state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A capture arm at a family is the obligation at each of its expressions. -/
example (C : Contract) (rc : ElabRec C) (arm : ExprArm C rc .operand) (sc : ElabScope)
    (st st' : ECtx × Nat) (out : SProg C × RawExpr)
    (ran : Solidity.Goals.ElabRan (hoistWith C rc (.num 1)) sc st out st') (raw : List RawStmt) :
    SiteSim C raw sc st out.1 st' :=
  arm (.num 1) rfl sc st out st' ran raw

/-- An obligation at a site is `RunSim` at each run recorded there. -/
example (C : Contract) (raw : List RawStmt) (sc : ElabScope) (st st' : ECtx × Nat) (P : SProg C)
    (site : SiteSim C raw sc st P st') (b : Body) (Γ : Ctx)
    (o : Solidity.Correctness.Lowering.Checker.Output C Γ)
    (m : Solidity.Lowering.V07.ContextMap b.ctx Γ) (run : Elaborated C o raw sc st P st')
    (lowered : Lowered b ⟨C, Γ, o⟩) (threaded : Threaded b ⟨C, Γ, o⟩)
    (accepted : Accepted ⟨C, Γ, o⟩) (assoc : diagram.Assoc b ⟨C, Γ, o⟩ m) :
    RunSim b ⟨C, Γ, o⟩ m :=
  site b Γ o m run lowered threaded accepted assoc

/-- **Sufficiency**: the three cases and a loop hypothesis give
`diagram.Simulates`, by the knot induction of `elabKernelTotal`. -/
example (kernel : elabKernelTotal) (exprs : ExprCases) (stmts : StmtCases) (states : StateCases)
    (loops : ∀ (C : Contract) (r : ElabRec C), RecSim C r → StmtArm C r .loop) :
    diagram.Simulates :=
  simulates_of_runs (runs_of_cases kernel exprs stmts states loops)

end Solidity.Examples.Lowering.Sim.Cases
