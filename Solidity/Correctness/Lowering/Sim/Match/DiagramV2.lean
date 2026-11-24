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

* `frame_matching`: `diagram.FrameTotal`, proved: the model state of
  `initial_matching` with the instance at the frame's address and the
  transaction read off the frame.
* `lowering_v2_of_runs₂`: the v2 goal from `RunSim₂` at every run, coverage and
  the session lift; the three are hypotheses.

## Limitations

* `diagram.SimulatesV2` is not proved: `RunSim₂` at every run is a hypothesis
  (ls3a-sim-induction owns it), as are `diagram.Total` and `SessionLift diagram`
  (ls3b, ls2s). So `loweringBySimulationV2` stays open.
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

omit [FreshNames] in
/-- An address as a model `uint`. -/
private def addressDenote (a : Roadmap.Address) : PrimTy.uint.Denote :=
  Total.Simulation.wordDenote
    ⟨a.val, Nat.lt_trans a.isLt (Nat.pow_lt_pow_right (by decide) (by decide))⟩

omit [FreshNames] in
/-- **Globals half of frame-total matching**: every Source state and
transactional frame has a related model state whose transaction is the frame,
with any locals over the empty heap. -/
theorem globRel_frame {E : Source.Env} {C : Contract} {Γ : Ctx} (typed : StorageTyped E C)
    (st : Source.St E) (env : TEnv C [] Γ) (G : Source.Glob E) (F : Source.Fr)
    (static : F.static = false) (checked : F.checked = true) :
    ∃ tgt : State C Γ,
      tgt.H = [] ∧ HEq tgt.env env ∧ globRel st tgt ∧ FrameRel G F tgt := by
  obtain ⟨storage, related⟩ := Total.Simulation.fields_onto (cell st F.this) C.vars
    fun x T mem => by
      obtain ⟨p, rfl, ty⟩ := typed x T mem
      exact ⟨p, rfl, Total.Simulation.read_prim _ _ p ty⟩
  let tx : TTx := ⟨addressDenote F.sender, addressDenote F.this,
    Total.Simulation.wordDenote F.value, Total.Simulation.wordDenote G.timestamp, []⟩
  let state (funds : PrimTy.uint.Denote) : State C Γ :=
    { storage := storage, H := [], heap := Heap.empty, env := env, tx := tx, selfBalance := funds }
  by_cases fits : Source.Monetary.Fits (st.ex.world.accounts F.this).balance
  · exact ⟨state (Total.Simulation.wordDenote ⟨_, fits⟩), rfl, HEq.rfl,
      ⟨F.this, rfl, related, fun _ => rfl⟩, rfl, rfl, rfl, rfl, static, checked⟩
  · exact ⟨state (PrimTy.dflt .uint), rfl, HEq.rfl,
      ⟨F.this, rfl, related, fun h => absurd h fits⟩, rfl, rfl, rfl, rfl, static, checked⟩

/-- **Frame-total initial matching** for the diagram: `diagram.FrameTotal`. -/
theorem frame_matching : diagram.FrameTotal := by
  intro b u m _ _ assoc G F static checked src
  have h : Assoc b u m := assoc
  obtain ⟨env, related⟩ := h.2.2.1.locals b.E.layout u.C [] src.1
  obtain ⟨⟨storage, H, heap, env', funds, tx⟩, rfl, same, glob, frame⟩ :=
    globRel_frame h.storageTyped src.2 env G F static checked
  cases same
  exact ⟨_, related, glob, frame⟩

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

/-- **The v2 goal from its open parts**: `RunSim₂` at every associated
production run of the fragment, coverage and the session lift give
`loweringBySimulationV2`; the caller binding and frame-total matching are
proved. -/
theorem lowering_v2_of_runs₂
    (runs : letI : FreshNames := productionNames
      ∀ (b : Body) (u : Emitted) (m : Solidity.Lowering.V07.ContextMap b.ctx u.Γ),
        Production b u → Accepted u → diagram.Assoc b u m → RunSim₂ b u m)
    (total : letI : FreshNames := productionNames; diagram.Total)
    (lift : letI : FreshNames := productionNames; SessionLift diagram) :
    Solidity.Goals.loweringBySimulationV2 :=
  letI : FreshNames := productionNames
  ⟨caller_bound, diagram, simulatesV2_of_runs₂ runs, frame_matching, total, lift⟩

end Solidity.Correctness.Lowering.Sim
