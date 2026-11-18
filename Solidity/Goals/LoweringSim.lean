import Solidity.Tools.Goal
import Solidity.Goals.LoweringDiagram
import Solidity.Goals.LoweringSession
import Solidity.Goals.IntrinsicSession
import Solidity.Goals.IntrinsicStorage

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

Session level (H556 option A, sg1-restate-lowering-goal): for the same
diagram, `Shrink.Lowering.SessionLift` (`Goals/LoweringSession.lean`) lifts it
to the actual Source session semantics (`sourceLangEvents`) and the concrete
intrinsic session semantics (`IntrinsicSession.spec F`, every `F`): a lowered
world built from the production compilation of every Source program of the
fragment, the program-to-body binding, the environment map, a
`G49Final.PassCorrect` with the resource transport `D.fuel` and the backward
clause, and storage and event agreement through `D.globRel`. The goal is
blocked by `intrinsicSessionSemantics` and `intrinsicStorageAccounting`: it
counts as proved only when the semantics it names is validated.

## Limitations (stated, not hidden)

* No function from the raw input to its resolved Source statement exists at
  the base. `Diagram.Total` therefore asks, for every fragment production
  run, for SOME resolved Source statement with the same production input
  (`Body.SameInput`: site, raw input, return slots, scope and state) that the
  diagram simulates; the source context, environment and statement are
  existential. For the function bodies of a Source program's compilation,
  `SessionLift`'s binding fixes the source to the program's resolved body; the
  raw compilation itself is existential per program (no resolver links raw
  syntax to Source declarations; see `Goals/LoweringSession.lean`).
* The diagram's value and global relations are its own invariant, bound only
  by Boolean/integer reflection and total initial matching; storage and event
  agreement is `SessionLift`'s.
* The goal is stated for the production fresh-name policy
  (`productionNames`), not for the per-file `FreshNames.ofTable` instances of
  chain examples.
-/

namespace Solidity.Goals

open Solidity.Goal

/-- Production lowering on t0's fragment by one simulation diagram, under the
production fresh-name policy, lifted to the intrinsic session semantics
(H556 option A). -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer "ls3-lowering-compose" ←
    intrinsicSessionSemantics intrinsicStorageAccounting]
def loweringBySimulation : Prop :=
  letI : FreshNames := Shrink.Lowering.productionNames
  Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram, D.Simulates ∧ D.Total ∧ Shrink.Lowering.SessionLift D

end Solidity.Goals
