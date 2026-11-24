import Solidity.Goals.LoweringDiagramV2
import Solidity.Correctness.Lowering.Sim.Expr.Frame

/-!
# The frame-aware diagram companion (H1391, ls3a prerequisite P4)

Connects the v2 run obligations (`RunSim₂`, `frameRel`: `Sim/Expr/Frame.lean`,
`Sim/Match/Relations.lean`) with the v2 goal contract
(`Goals/LoweringDiagramV2.lean`), toward `Solidity.Goals.loweringBySimulation`
through its additive v2 `loweringBySimulationV2`.

* `frameRel_eq`: the contract's `FrameRel` is `Sim.frameRel`.
* `simulatesV2_of_runs₂`, `runs₂_of_simulatesV2`: `RunSim₂` at every associated
  production run of the fragment is exactly the per-run part of
  `diagram.SimulatesV2`.
* `simulatesV2_of_simulates`, `lowering_v2_of_v1`: **v1 gives v2** (the latter
  with `FrameTotal`, which v1 does not state). No converse is stated or holds
  by these lemmas: v2 says nothing at a static or unchecked frame.

## Limitations (first checkpoint: statements and definitional bridges only)

* Nothing is proved about `diagram.SimulatesV2` or `diagram.FrameTotal`: the
  relation is under review. `RunSim₂` at every run is a hypothesis here
  (ls3a-sim-induction owns it), and `FrameTotal` for `Sim.diagram` (a model
  transaction built from the frame, next to `initial_matching`) is not proved.
* The session consumers (`Sim/Session/`) are stated over `Diagram` and
  hypotheses (`MatchedFrames`), not over `Simulates`; they are not migrated.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

/-- The contract's frame relation is this lane's. -/
theorem frameRel_eq {E : Source.Env} {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr)
    (σ : State C Γ) : frameRel G F σ = FrameRel G F σ := rfl

variable [FreshNames]

/-- `RunSim₂` at every associated production run of the fragment is
`diagram.SimulatesV2`. -/
theorem simulatesV2_of_runs₂
    (runs : ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
      Production b u → Accepted u → diagram.Assoc b u m → RunSim₂ b u m) :
    diagram.SimulatesV2 :=
  ⟨diagram_relations.1, diagram_relations.2.1, diagram_relations.2.2, runs⟩

/-- `diagram.SimulatesV2` gives `RunSim₂` at every associated production run. -/
theorem runs₂_of_simulatesV2 (h : diagram.SimulatesV2) (b : Body) (u : Emitted)
    (m : ContextMap b.ctx u.Γ) (production : Production b u) (accepted : Accepted u)
    (assoc : diagram.Assoc b u m) : RunSim₂ b u m :=
  h.2.2.2 b u m production accepted assoc

/-- **Bridge, v1 to v2**: the v1 obligations of any diagram give its v2 ones. -/
theorem simulatesV2_of_simulates {D : Diagram} (h : D.Simulates) : D.SimulatesV2 :=
  ⟨h.1, h.2.1, h.2.2.1, fun b u m production accepted assoc =>
    have run := h.2.2.2 b u m production accepted assoc
    ⟨run.1, run.2.1, run.2.2.choose, fun G F nps ph src tgt related glob _ =>
      run.2.2.choose_spec G F nps ph src tgt related glob⟩⟩

end Solidity.Correctness.Lowering.Sim

namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals.Shrink.Lowering

/-- **Bridge, v1 to v2, at the goal**: `loweringBySimulation` with a diagram
that is also total at transactional frames gives `loweringBySimulationV2`. -/
theorem lowering_v2_of_v1
    (h : letI : FreshNames := productionNames
      CallerBound ∧ ∃ D : Diagram, D.Simulates ∧ D.FrameTotal ∧ D.Total ∧ SessionLift D) :
    Solidity.Goals.loweringBySimulationV2 :=
  letI : FreshNames := productionNames
  let ⟨bound, D, simulates, frames, total, lift⟩ := h
  ⟨bound, D, simulatesV2_of_simulates simulates, frames, total, lift⟩

end Solidity.Correctness.Lowering.Sim
