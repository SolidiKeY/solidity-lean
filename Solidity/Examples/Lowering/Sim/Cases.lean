import Solidity.Correctness.Lowering.Sim.Smoke

/-!
# The case interface of the lowering diagram, used

The instantiation of `ElabKernelInduction` at `RecSim`, the families of some
raw inputs, the cases implying `diagram.Simulates`, and the smokes of
`Sim/Smoke.lean` as leaf conjuncts of `StmtCases`.
-/
namespace Solidity.Examples.Lowering.Sim.Cases

open Solidity.Goals (ElabSat ElabKernelInduction elabStmtsStep elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim

variable [FreshNames]

/-- **The instantiation**: `RecSim` is what `ElabKernelInduction` concludes. -/
example (C : Contract) (rc : ElabRec C) (induction : ElabKernelInduction C rc)
    (step : ∀ r : ElabRec C, RecSim C r →
      ElabSat (hoistQ C) (hoistWith C r) ∧ ElabSat (hoistStmtQ C) (hoistStmtWith C r) ∧
      ElabSat (stmtQ C) (elabStmtPWith C r) ∧ ElabSat (stmtQ C) (elabStmt1With C r) ∧
      ElabSat (blockQ C) (elabStmtsStep C r)) : RecSim C rc :=
  recSim_of_step C rc induction step

/-- The families of some raw inputs. -/
example : stmtFamily .revert = .revert ∧
    stmtFamily (.assign (.name "x") (.call "f" [])) = .call ∧
    stmtFamily (.whileLoop {} (.bool true) []) = .loop ∧ stmtFamily .brk = .jump ∧
    exprFamily (.binop .add (.num 1) (.num 2)) = .arith ∧ exprFamily (.call "f" []) = .state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The three cases and a loop hypothesis imply `diagram.Simulates`, by the
knot induction of `elabKernelTotal` (an implication, not a proof plan). -/
example (kernel : elabKernelTotal) (exprs : ExprCases) (stmts : StmtCases) (states : StateCases)
    (loops : ∀ (C : Contract) (r : ElabRec C), RecSim C r → StmtArm C r .loop) :
    diagram.Simulates :=
  simulates_of_runs (runs_of_cases kernel exprs stmts states loops)

/-- The jump leaf of `StmtCases` for `elabStmt1With`, at every record. -/
example (C : Contract) (rc : ElabRec C) : ArmSat C (elabStmt1With C rc) .jump := jump_arm C rc

/-- The `revert();` leaf, from the Source side of its bodies. -/
example (C : Contract) (rc : ElabRec C)
    (bodies : ∀ (b : Body) (Γ : Ctx) (o : Solidity.Correctness.Lowering.Checker.Output C Γ)
      (m : Solidity.Lowering.V07.ContextMap b.ctx Γ), o.raw = [.revert] →
      Lowered b ⟨C, Γ, o⟩ → Threaded b ⟨C, Γ, o⟩ → diagram.Assoc b ⟨C, Γ, o⟩ m →
      LowerFresh b ⟨C, Γ, o⟩ ∧ SourceReverts b) :
    ArmSat C (elabStmt1With C rc) .revert := revert_arm_of C rc bodies

end Solidity.Examples.Lowering.Sim.Cases
