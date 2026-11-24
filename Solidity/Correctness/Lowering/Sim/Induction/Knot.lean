import Solidity.Correctness.Lowering.Sim.Match.Cases

/-!
# Closing the elaborator knot from the frozen cases

Intermediate step toward `Solidity.Goals.loweringBySimulation`. The loop-arm
bridge remains explicit here: it must be derived from the production loop
hypothesis before this lemma can establish the requested simulation theorem.
No loop correctness or callee coverage is asserted by this helper.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (elabKernelTotal)

/-- The five callbacks of the actual elaborator satisfy the frozen case
predicates, provided every arm, including the loop arm, preserves them.
The induction principle is taken from `hk`, not from an imported totality proof. -/
theorem recSim_of_cases [FreshNames] (hk : elabKernelTotal)
    (exprs : ExprCases) (stmts : StmtCases) (states : StateCases)
    (C : Contract)
    (loops : ∀ r : ElabRec C, RecSim C r → StmtArm C r .loop) :
    RecSim C (elabRec C ()) :=
  recSim_of_step C _ (hk.1 C).2.2
    (step_of_cases C hk exprs stmts states loops)

end Solidity.Correctness.Lowering.Sim
