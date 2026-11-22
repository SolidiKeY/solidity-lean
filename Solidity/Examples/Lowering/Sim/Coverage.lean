import Solidity.Correctness.Lowering.Sim.Coverage.SpellingObstruction

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

end Solidity.Examples.Lowering.Sim.Coverage
