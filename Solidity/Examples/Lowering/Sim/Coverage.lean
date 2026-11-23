import Solidity.Correctness.Lowering.Sim.Coverage.SpellingObstruction
import Solidity.Correctness.Lowering.Sim.Coverage.Alignment
import Solidity.Examples.Lowering.Sim.Match

/-!
# Coverage obstructions and independent smoke facts

The requested use of `diagram_total` cannot be supplied for the frozen v1
statement: the first example refutes it under the authorized kernel hypothesis.
The second checks that versioned production retains the v1 receipt; the third
shows that caller placement alone does not repair the frozen spelling relation.
The final checks establish decoder success, alignment and acceptance of the
existing materialized program separately; no production receipt is inferred.
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

/-- The existing decoder computes the smoke’s actual Source resolution. -/
theorem smoke_decoded
    (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    Solidity.Correctness.Lowering.Total.Decode.decode (request Match.body (Match.emitted out)) =
      some (Solidity.Correctness.Lowering.Total.SourceProgram.ofStmt Match.body.input.resolved) := by
  rfl

/-- The existing smoke supplies an aligned map from its actual typing, before
any restriction predicate or successful-production premise is selected. -/
example (out : Solidity.Correctness.Lowering.Checker.Output Match.C [.val .bool, .val .bool]) :
    ∃ m : Solidity.Lowering.V07.ContextMap Match.body.ctx
      (request Match.body (Match.emitted out)).context.ctx, Aligned m :=
  spells_aligned (r := request Match.body (Match.emitted out))
    (s := Solidity.Correctness.Lowering.Total.SourceProgram.ofStmt Match.body.input.resolved)
    (Solidity.Correctness.Lowering.Total.decode_spells (smoke_decoded out))

/-- Acceptance of the existing materialized while/break program. This is a
kernel check of that exact program, not its still-needed production receipt. -/
example : Solidity.Backend.AbiWorld.PublicCompilerTotal.ProgOk []
    Solidity.Correctness.Lowering.Checker.IntrinsicProbe.actual.program.2 := by
  repeat constructor

end Solidity.Examples.Lowering.Sim.Coverage

#print axioms Solidity.Correctness.Lowering.Sim.Coverage.spells_aligned

#print axioms Solidity.Examples.Lowering.Sim.Coverage.smoke_decoded
