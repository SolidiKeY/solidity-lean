import Solidity.Tools.Goal
import Solidity.Goals.LoweringDiagram
import Solidity.Goals.LoweringSession
import Solidity.Goals.IntrinsicSession
import Solidity.Goals.IntrinsicStorage

/-!
# The lowering shrink goals (H517; v2 H556 A, H1185, H1186)

* `loweringBySimulation` (`Solidity.Correctness.Lowering.Sim.lowering_producer`):
  ONE forward simulation diagram over the actual production lowering
  (`lowerLoops` then `lowerReturns`, as `calleeBody` sequences them, and the
  standalone `lowerLoops none` sites) followed by the actual elaborator
  (`elabStmtsP`, `SProg.chain`), with its fresh-name state, on t0's accepted
  fragment (`PublicCompilerTotal.ProgOk []`), with initial/final matching,
  stuttering, progress, source determinacy, a backward diagram, fresh-state
  soundness and coverage of every fragment production run.

* `loweringBySimulationV2` (`Solidity.Correctness.Lowering.Sim.lowering_producer_v2`,
  H556 option A, kept next to v1 by H1185 and H1186 under H314): v1's
  statement and, for the same diagram, `Shrink.Lowering.SessionLift`
  (`Goals/LoweringSession.lean`): the lift to the actual Source session
  semantics (`sourceLangEvents`) and the concrete intrinsic session semantics
  (`IntrinsicSession.spec F`, every `F`), with a lowered world built from the
  production compilation of every Source program of the fragment, the
  program-to-body binding, the environment map, a `G49Final.PassCorrect` with
  the resource transport `D.fuel` and the backward clause, and storage and
  event agreement through `D.globRel`. It is blocked by
  `intrinsicSessionSemantics` and `intrinsicStorageAccounting`, so it counts as
  proved only when the semantics it names is validated. v2 implies v1.

v2 is temporarily weaker than the lift H556 asks for, in two stated ways, each
removed by a later plan step: the raw compilation is existential per Source
program (H1185: until a resolver from Source declarations to raw syntax and a
production ABI dispatcher make it a function of the program), and the two
behaviours carry the premises the Source session cannot yet meet (H1186: the
source is read at horizons whose transported target bound is ready, the target
at bounds without resource failure, until the Source side has a resource and
hash model). v1 states no session-level conjunct.

## Limitations (stated, not hidden)

* No function from the raw input to its resolved Source statement exists at
  the base. `Diagram.Total` therefore asks, for every fragment production
  run, for SOME resolved Source statement with the same production input
  (`Body.SameInput`: site, raw input, return slots, scope and state) that the
  diagram simulates; the source context, environment and statement are
  existential. The goal so says "every emitted fragment program is simulated
  by some Source statement", not "by the statement its raw input means": a
  lowering that miscompiles into another Source-expressible behaviour is not
  excluded here. v2's `SessionLift` binds the function bodies of a Source
  program's compilation to the program's resolved bodies.
* The diagram's value and global relations are its own invariant, bound only
  by Boolean/integer reflection and total initial matching; storage and event
  agreement is v2's (`SessionLift`).
* The goal is stated for the production fresh-name policy
  (`productionNames`), not for the per-file `FreshNames.ofTable` instances of
  chain examples.
-/

namespace Solidity.Goals

open Solidity.Goal

/-- Production lowering on t0's fragment by one simulation diagram, under the
production fresh-name policy; its session-level lift to `Lowering`/`PassCorrect`
is `loweringBySimulationV2` (H556 A). -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer "ls3-lowering-compose"]
def loweringBySimulation : Prop :=
  letI : FreshNames := Shrink.Lowering.productionNames
  Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram, D.Simulates ∧ D.Total

/-- v1 with the session-level lift of the same diagram to the concrete intrinsic
session semantics (H556 A; the existential compilation and the two behaviour
premises of H1185 and H1186). -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer_v2 "ls3-lowering-compose" ←
    intrinsicSessionSemantics intrinsicStorageAccounting]
def loweringBySimulationV2 : Prop :=
  letI : FreshNames := Shrink.Lowering.productionNames
  Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram, D.Simulates ∧ D.Total ∧ Shrink.Lowering.SessionLift D

end Solidity.Goals
