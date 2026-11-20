import Solidity.Correctness.Lowering.Sim.Coverage.ThreadedV2
import Solidity.Examples.Lowering.Sim.Match

/-!
# Caller-context bridge on the existing standalone loop

The loop is `while (i = a) break;` from `Sim.Match`. As there, the emitted
output and placement are parameters. V1 threading is an explicit receipt;
this example proves no closed elaborator run or coverage theorem.
-/

namespace Solidity.Examples.Lowering.Sim.Coverage.ThreadedV2

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering
open Solidity.Correctness.Lowering.Sim
open Solidity.Correctness.Lowering.Sim.Coverage
open Solidity.Examples.Lowering.Sim.Match

/-- Bridge the existing `while (i = a) break;` vocabulary and v1 receipt. -/
theorem loop_bridge (out : Checker.Output C [.val .bool, .val .bool])
    (threaded : Threaded body (emitted out))
    (placed : out.names = (request body (emitted out)).context.names) :
    ThreadedV2 body (emitted out) :=
  ThreadedV2.ofAssoc threaded
    (show Assoc body (emitted out) (Total.Simulation.primitiveMap [.bool, .bool]) from
      ⟨rfl, placed, aligned_primitiveMap _, _,
        ⟨rfl, context, names, _, names, .stmt typing .nil, rfl, rfl, spelled, rfl⟩, rfl⟩)

/-- The bridge retains the original threading receipt for the same loop. -/
example (out : Checker.Output C [.val .bool, .val .bool])
    (threaded : Threaded body (emitted out))
    (placed : out.names = (request body (emitted out)).context.names) :
    Threaded body (emitted out) :=
  (loop_bridge out threaded placed).toThreaded

end Solidity.Examples.Lowering.Sim.Coverage.ThreadedV2

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.ThreadedV2.toThreaded
#print axioms Solidity.Correctness.Lowering.Sim.Coverage.ThreadedV2.ofAssoc
#print axioms Solidity.Examples.Lowering.Sim.Coverage.ThreadedV2.loop_bridge
