import Solidity.Correctness.Lowering.Sim.Coverage.SpellingObstruction
import Solidity.Correctness.Lowering.Sim.Coverage.Alignment
import Solidity.Examples.Lowering.Sim.Match

/-!
# Exact coverage obstructions

The requested use of `diagram_total` cannot be supplied for the frozen v1
statement: the first example refutes it under the authorized kernel hypothesis.
The second checks that versioned production retains the v1 receipt; the third
shows that caller placement alone does not repair the frozen spelling relation.
-/
namespace Solidity.Examples.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Sim.Coverage

example (hk : Solidity.Goals.elabKernelTotal) :
    ¬ @Diagram.Total productionNames diagram := not_total hk

example (hk : Solidity.Goals.elabKernelTotal) :
    @Production productionNames uncheckedBody uncheckedEmitted :=
  (unchecked_production hk).toProduction

example (hk : Solidity.Goals.elabKernelTotal) :
    ¬ @TotalV2 productionNames diagram := not_totalV2 hk

/-- The existing smoke supplies an aligned map from its actual typing, before
any restriction predicate or successful-production premise is selected. -/
example (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    ∃ m : Solidity.Lowering.V07.ContextMap Match.body.ctx
      (request Match.body (Match.emitted out)).context.ctx, Aligned m :=
  spells_aligned (r := request Match.body (Match.emitted out))
    (s := Solidity.Correctness.Lowering.Total.SourceProgram.ofStmt Match.body.input.resolved)
    ⟨rfl, Match.context, Match.names, _, Match.names, .stmt Match.typing .nil,
      rfl, rfl, Match.spelled, rfl⟩

end Solidity.Examples.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.spells_aligned
