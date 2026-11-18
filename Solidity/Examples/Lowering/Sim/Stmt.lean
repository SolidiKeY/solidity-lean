import Solidity.Correctness.Lowering.Sim.Stmt.Main
import Solidity.Correctness.Lowering.Sim.Stmt.Framed

/-!
# The statement cases of the lowering diagram, used

The jump conjunct of `StmtCases` on a concrete arm, `StmtCases` from the
conjuncts that remain, and the frame obstruction at a body.
-/
namespace Solidity.Examples.Lowering.Sim.Stmt

open Solidity.Goals (ElabRan ElabSat elabStmtsStep elabKernelTotal)
open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Unchecked (RawOneInput SourceOneAssociation)

variable [FreshNames]

/-- `break;` through `elabStmtPWith` at every record: no body is elaborated to it. -/
example (kernel : elabKernelTotal) (C : Contract) (rc : ElabRec C) (sc : ElabScope)
    (st st' : ECtx × Nat) (P : SProg C) (ran : ElabRan (elabStmtPWith C rc .brk) sc st P st') :
    stmtQ C .brk sc st P st' :=
  (jump_cases C kernel rc).1 .brk rfl sc st P st' ran

/-- `StmtCases` from its conjuncts other than the jumps. -/
example
    (rest : elabKernelTotal → ∀ (C : Contract) (rc : ElabRec C), RecSim C rc →
      StmtArm C rc .assign ∧ StmtArm C rc .declLocal ∧ StmtArm C rc .opAssign ∧
      StmtArm C rc .incDec ∧ StmtArm C rc .require ∧ StmtArm C rc .assert ∧
      StmtArm C rc .revert ∧ StmtArm C rc .ite ∧ StmtArm C rc .block ∧
      ElabSat (blockQ C) (elabStmtsStep C rc)) : StmtCases :=
  stmt_cases_of rest

/-- Under v1 no emitted program simulates a body resolved to a local `x++` or `x -= 1`. -/
example {input : RawStmt} (context : Source.Ctx) (raw : RawOneInput input) {k : Source.SCtx}
    (statement : Source.RStmt context.env context.rets context.inModifier k context.tys context.tys)
    (certificate : SourceOneAssociation context raw statement) (scope : ElabScope)
    (before : Solidity.Correctness.Lowering.Checker.Snapshot) (site : Site) (u : Emitted)
    (m : Solidity.Lowering.V07.ContextMap context.tys u.Γ) (G : Source.Glob context.env)
    (F : Source.Fr) (src : Source.EMState context.env context.tys) :
    ¬ RunSim ⟨context.env, context.rets, context.inModifier, k, context.tys,
      ⟨[], statement, none, scope, before⟩, site⟩ u m :=
  one_not_runSim context raw statement certificate [] none scope before site u m G F src

/-- The jump conjunct under the v2 frame premise, on `break;`. -/
example (kernel : elabKernelTotal) (C : Contract) (rc : ElabRec C) :
    Stmt.V2.ArmSat C (elabStmtPWith C rc) .jump :=
  (Stmt.V2.jump_cases C kernel rc).1

/-- v2's `Simulates` from its per-run obligations. -/
example
    (runs : ∀ (b : Body) (u : Emitted) (m : Solidity.Lowering.V07.ContextMap b.ctx u.Γ),
      Production b u → Accepted u → diagram.Assoc b u m → Stmt.V2.RunSim b u m) :
    Stmt.V2.diagram.Simulates :=
  Stmt.V2.simulates_of_runs runs

/-- Under v2 a checked, non-static frame has a matched target state. -/
example (b : Body) (u : Emitted) (m : Solidity.Lowering.V07.ContextMap b.ctx u.Γ)
    (h : diagram.Assoc b u m) (G : Source.Glob b.E) (F : Source.Fr)
    (frame : F.static = false ∧ F.checked = true) (src : Source.EMState b.E b.ctx) :
    ∃ tgt : State u.C u.Γ, Stmt.V2.diagram.frameRel G F tgt :=
  (Stmt.V2.initial_matching b u m h G F frame src).imp fun _ h => h.2.2

end Solidity.Examples.Lowering.Sim.Stmt
