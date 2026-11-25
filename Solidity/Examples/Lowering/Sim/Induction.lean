import Solidity.Correctness.Lowering.Sim.Induction.Knot

/-! The intermediate elaborator-knot result under the production name policy.
The loop-arm bridge is still a hypothesis; this is not producer simulation. -/
namespace Solidity.Examples.Lowering.Sim.Induction

open Solidity.Goals (elabKernelTotal)
open Solidity.Goals.Shrink.Lowering (productionNames)
open Solidity.Correctness.Lowering.Sim

local instance : FreshNames := productionNames

/-- Close the actual elaborator record under production names, conditional on
all frozen cases and the loop-arm bridge. -/
example (hk : elabKernelTotal) (exprs : ExprCases) (stmts : StmtCases)
    (states : StateCases) (C : Contract)
    (loops : ∀ r : ElabRec C, RecSim C r → StmtArm C r .loop) :
    RecSim C (elabRec C ()) :=
  recSim_of_cases hk exprs stmts states C loops

end Solidity.Examples.Lowering.Sim.Induction
