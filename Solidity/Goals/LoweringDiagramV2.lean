import Solidity.Tools.Goal
import Solidity.Goals.LoweringDiagram
import Solidity.Goals.LoweringSession
import Solidity.Goals.IntrinsicSession
import Solidity.Goals.IntrinsicStorage

/-!
# The frame-aware lowering diagram contract, v2 (H1391, ls3a prerequisite P4)

`Diagram.Simulates` (`Goals/LoweringDiagram.lean`, frozen) asks its run clauses
at every Source frame. A static frame reverts in Source at a storage write the
model completes, and an unchecked frame wraps where the model panics, so v1 is
not provable at such bodies (`Sim/Match.lean`, "Limitations"). This module is
the additive v2 beside it; nothing of v1 is changed.

* `FrameRel G F σ`: the Source frame is the model's transaction (own address,
  sender, value, timestamp), not static, checked. It is fixed here, not a field
  of the diagram: a diagram cannot choose an empty frame relation.
* `Diagram.SimulatesV2`: `Diagram.Simulates` with the forward, source-stability
  and backward clauses at frames related by `FrameRel`. Value reflection, fuel
  monotonicity, `LowerFresh` and total initial matching are v1's, verbatim.
* `Diagram.FrameTotal`: initial matching is total at every transactional frame:
  every Source state, world and non-static checked frame has a related model
  state that `FrameRel` relates to the frame. Without it a global relation that
  pins a transaction field would leave `SimulatesV2` vacuous at other frames.
* `loweringBySimulationV2`: `loweringBySimulation` with `SimulatesV2` and
  `FrameTotal` for `Simulates`. `CallerBound`, `Diagram`, `Diagram.Total` and
  `SessionLift` are v1's, so session consumers (`Sim/Session/`) need no change.

## Bridge direction and migration

* **v1 gives v2, never the converse.** `D.Simulates → D.SimulatesV2`
  (`Sim/Match/DiagramV2.lean`); with `D.FrameTotal`, `loweringBySimulation`
  gives `loweringBySimulationV2`. No statement here or downstream may use
  v2 as v1: `SimulatesV2` says nothing at a static or unchecked frame.
* **Migration.** `loweringBySimulation` stays stated, open and unchanged. The
  lowering proof (`RunSim₂`, `CasesV2`, ls3a-sim-induction, ls3-lowering-compose)
  targets `loweringBySimulationV2`. A consumer of `loweringBySimulation` that
  reads only `CallerBound`, `Diagram.Total` or `SessionLift` moves to v2
  unchanged; one that reads `Simulates` must supply `FrameRel` at its frames.
  Retiring or re-pointing the v1 goal is the owner's decision, not made here.

## Limitations

* `FrameTotal` and the frame premise speak of one body's frame. That the frames
  of a session's calls satisfy `FrameRel` is `SessionLift`'s to establish
  (`Sim/Session/Forward.lean`, `MatchedFrames`); it is not stated here.
* The limitations of `Goals/LoweringSim.lean` (existential source, relations
  bound only by reflection and matching, production names) carry over.
-/

namespace Solidity.Goals

namespace Shrink.Lowering

open Solidity.Lowering.V07 (ContextMap IntValueRel integerPrim)

variable [FreshNames]

/-- **The frame relation**: the Source frame is the model's transaction, not
static, checked. -/
def FrameRel {E : Source.Env} {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr)
    (σ : State C Γ) : Prop :=
  (F.this.val : Int) = σ.tx.selfAddress.1 ∧ (F.sender.val : Int) = σ.tx.msgSender.1 ∧
  σ.tx.msgValue.1 = (F.value.val : Int) ∧ σ.tx.timestamp.1 = (G.timestamp.val : Int) ∧
  F.static = false ∧ F.checked = true

/-- **The diagram's obligations, v2**: those of `Diagram.Simulates`, the three
run clauses at Source frames `FrameRel` relates to the model state. -/
def Diagram.SimulatesV2 (D : Diagram) : Prop :=
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (v : Source.Val Dl .bool) (b : Bool),
    D.valRel (C := C) (H := H) .bool (.val .bool) v b → v = .bool b) ∧
  (∀ {Dl : Source.Layout} {C : Contract} {H : HTy} (t : Source.IntTy) (v : Source.Val Dl (.int t))
    (x : (integerPrim t).Denote), D.valRel (C := C) (H := H) (.int t) (.val (integerPrim t)) v x →
      IntValueRel t v x) ∧
  (∀ n n', n ≤ n' → D.fuel n ≤ D.fuel n') ∧
  ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    Production b u → Accepted u → D.Assoc b u m →
    LowerFresh b u ∧
    (∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
      m.Related (fun τ v => D.valRel τ v) src.1 tgt.env ∧ D.globRel src.2 tgt) ∧
    ∃ emb : Thin u.Γ u.output.program.1,
    ∀ (G : Source.Glob b.E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph b.E))
      (src : Source.EMState b.E b.ctx) (tgt : State u.C u.Γ),
      m.Related (fun τ v => D.valRel τ v) src.1 tgt.env → D.globRel src.2 tgt →
      FrameRel G F tgt →
      (∀ n, (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
        D.Final m emb (sourceRun b G F n nps ph src) (u.output.program.2.runF (D.fuel n) tgt)) ∧
      (∀ n n', n ≤ n' → (sourceRun b G F n nps ph src).1 ≠ .error .timeout →
        sourceRun b G F n' nps ph src = sourceRun b G F n nps ph src) ∧
      (∀ n, u.output.program.2.runF n tgt ≠ .error .diverge →
        ∃ j, D.Final m emb (sourceRun b G F j nps ph src) (u.output.program.2.runF n tgt))

/-- **Initial matching is total at every transactional frame**: for an
associated production run of the fragment, every Source state, world and
non-static checked frame has a related model state whose transaction is the
frame. So the frame premise of `SimulatesV2` excludes static and unchecked
frames only. -/
def Diagram.FrameTotal (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted) (m : ContextMap b.ctx u.Γ),
    Production b u → Accepted u → D.Assoc b u m →
    ∀ (G : Source.Glob b.E) (F : Source.Fr), F.static = false → F.checked = true →
    ∀ src : Source.EMState b.E b.ctx, ∃ tgt : State u.C u.Γ,
      m.Related (fun τ v => D.valRel τ v) src.1 tgt.env ∧ D.globRel src.2 tgt ∧ FrameRel G F tgt

end Shrink.Lowering

open Solidity.Goal

/-- Production lowering on t0's fragment by one simulation diagram at
transactional frames (v2 of `loweringBySimulation`, H1391), under the
production fresh-name policy, lifted to the intrinsic session semantics. -/
@[goal Solidity.Correctness.Lowering.Sim.lowering_producer_v2 "ls3-lowering-compose" ←
    intrinsicSessionSemantics intrinsicStorageAccounting]
def loweringBySimulationV2 : Prop :=
  letI : FreshNames := Shrink.Lowering.productionNames
  Shrink.Lowering.CallerBound ∧
    ∃ D : Shrink.Lowering.Diagram,
      D.SimulatesV2 ∧ D.FrameTotal ∧ D.Total ∧ Shrink.Lowering.SessionLift D

end Solidity.Goals
