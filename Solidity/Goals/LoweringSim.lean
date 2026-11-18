import Solidity.Tools.Goal
import Solidity.Goals.LoweringDiagram

/-!
# The lowering shrink goal (H517)

* `loweringBySimulation` (`Solidity.Correctness.Lowering.Sim.lowering_producer`):
  ONE forward simulation diagram over the actual production lowering
  (`lowerLoops` then `lowerReturns`, as `calleeBody` sequences them, and the
  standalone `lowerLoops none` sites) followed by the actual elaborator
  (`elabStmtsP`, `SProg.chain`), with its fresh-name state, on t0's accepted
  fragment (`PublicCompilerTotal.ProgOk []`), with initial/final matching,
  stuttering, progress, source determinacy, a backward diagram, fresh-state
  soundness and coverage of every fragment production run.

Session level, deferred by H556 (not hidden): the lift of this diagram to a
frozen `Roadmap.Lowering S I` and a `G49Final.PassCorrect` per program needs
the actual intrinsic session semantics (Event/Outcome prefixes over the
emitted programs), which does not exist at the base. Quantifying over every
`IntrinsicSpec` with a free target-session reference would make the goal
impossible, and an existential one would make it arbitrary, so this goal
states no session-level conjunct. Plan step is0-intrinsic-session defines that
semantics; sg1-restate-lowering-goal then adds the lift against it, with the
program-to-body binding (every resolved function body of the actual Source
program) and the resource transport tied to the diagram's fuel.

## Limitations (stated, not hidden)

* No function from the raw input to its resolved Source statement exists at
  the base. `Diagram.Total` therefore asks, for every fragment production
  run, for SOME resolved Source statement with the same production input
  (`Body.SameInput`: site, raw input, return slots, scope and state) that the
  diagram simulates; the source context, environment and statement are
  existential. The goal so says "every emitted fragment program is simulated
  by some Source statement", not "by the statement its raw input means": a
  lowering that miscompiles into another Source-expressible behaviour is not
  excluded here. Binding the raw input to its resolved statement is part of
  sg1-restate-lowering-goal, with the program-to-body binding.
* The diagram's value and global relations are its own invariant, bound only
  by Boolean/integer reflection and total initial matching; storage and event
  agreement is a session-level obligation (sg1).
* The goal is stated for the production fresh-name policy
  (`productionNames`), not for the per-file `FreshNames.ofTable` instances of
  chain examples.
-/

namespace Solidity.Goals

open Solidity.Goal

/-- Production lowering on t0's fragment by one simulation diagram, under the
production fresh-name policy; its session-level lift to `Lowering`/`PassCorrect`
is added by sg1-restate-lowering-goal (H556). -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer "ls3-lowering-compose"]
def loweringBySimulation : Prop :=
  letI : FreshNames := Shrink.Lowering.productionNames
  Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram, D.Simulates ∧ D.Total

end Solidity.Goals
