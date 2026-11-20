import Solidity.Correctness.Lowering.Sim.Stmt.Jump
import Solidity.Correctness.Lowering.Sim.Stmt.Frame

/-!
# Statement cases: what is proved

`StmtCases` (`Sim/Match/Cases.lean`) is not proved here, and is not provable
for the frozen `Sim.diagram`:

* proved: its `jump` conjunct (`jump_cases`, `Stmt/Jump.lean`);
* refuted where non-vacuous: a body whose resolved statement is a local
  integer `x++`, `x--`, `x += 1` or `x -= 1` has `RunSim` with no emitted
  program (`one_not_runSim`, `Stmt/Frame.lean`), so the `incDec` and
  `opAssign` conjuncts hold only if no production run of the fragment is
  associated with such a body. The cause (`RunSim.frame_blind`) reaches every
  family whose Source run reads the frame (arithmetic, state writes and reads);
* not proved: `revert`, the only other family whose Source run reads no frame.

`stmt_cases_of` is `StmtCases` from the conjuncts that remain.
-/

namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabSat elabStmtsStep elabKernelTotal)

variable [FreshNames]

/-- **`StmtCases` from its other conjuncts**: the jump family is `jump_cases`. -/
theorem stmt_cases_of
    (rest : elabKernelTotal → ∀ (C : Contract) (rc : ElabRec C), RecSim C rc →
      StmtArm C rc .assign ∧ StmtArm C rc .declLocal ∧ StmtArm C rc .opAssign ∧
      StmtArm C rc .incDec ∧ StmtArm C rc .require ∧ StmtArm C rc .assert ∧
      StmtArm C rc .revert ∧ StmtArm C rc .ite ∧ StmtArm C rc .block ∧
      ElabSat (blockQ C) (elabStmtsStep C rc)) : StmtCases := by
  intro kernel C rc sim
  obtain ⟨assign, declLocal, opAssign, incDec, require, assert, revert, ite, block, sequence⟩ :=
    rest kernel C rc sim
  exact ⟨assign, declLocal, opAssign, incDec, require, assert, revert, ite, block,
    jump_cases C kernel rc, sequence⟩

end Solidity.Correctness.Lowering.Sim
