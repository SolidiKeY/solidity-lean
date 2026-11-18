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

variable [FreshNames]

/-- `break;` through `elabStmtPWith`, at every record: its output meets the
obligations at its site (no body is elaborated to it). -/
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

/-- A simulated body completes at a checked frame exactly when it completes
at an unchecked one. -/
example {b : Body} {u : Emitted} {m : Solidity.Lowering.V07.ContextMap b.ctx u.Γ}
    (sim : RunSim b u m) (G : Source.Glob b.E) (F : Source.Fr) (src : Source.EMState b.E b.ctx)
    (n : Nat)
    (done : (sourceRun b G { F with checked := true } n 0 none src).1 ≠ .error .timeout)
    (done' : (sourceRun b G { F with checked := false } n 0 none src).1 ≠ .error .timeout) :
    (∃ x, (sourceRun b G { F with checked := true } n 0 none src).1 = .ok x) ↔
      ∃ x, (sourceRun b G { F with checked := false } n 0 none src).1 = .ok x :=
  sim.frame_blind G G _ _ 0 0 none none src n done done'

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
