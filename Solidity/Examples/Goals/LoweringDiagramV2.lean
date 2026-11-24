import Solidity.Goals.LoweringSim
import Solidity.Correctness.Lowering.Sim.Match.DiagramV2

namespace Solidity.Goals

/--
info: open Solidity.Goals.loweringBySimulationV2 ← Solidity.Correctness.Lowering.Sim.lowering_producer_v2 blocked by [Solidity.Goals.intrinsicSessionSemantics, Solidity.Goals.intrinsicStorageAccounting] plan ls3-lowering-compose
-/
#guard_msgs in
#roadmap_goal loweringBySimulationV2

namespace Shrink.Lowering

open Solidity.Correctness.Lowering.Sim (simulatesV2_of_simulates)

/-- The v2 goal differs from v1 in its diagram obligations only. -/
example : loweringBySimulationV2 =
    (letI : FreshNames := productionNames;
      CallerBound ∧ ∃ D : Diagram, D.SimulatesV2 ∧ D.FrameTotal ∧ D.Total ∧ SessionLift D) := rfl

/-- **Bridge direction**: v1 with `FrameTotal` gives v2. -/
example (h : loweringBySimulation)
    (frames : letI : FreshNames := productionNames; ∀ D : Diagram, D.Simulates → D.FrameTotal) :
    loweringBySimulationV2 :=
  letI : FreshNames := productionNames
  let ⟨bound, D, simulates, total, lift⟩ := h
  ⟨bound, D, simulatesV2_of_simulates simulates, frames D simulates, total, lift⟩

/-! ## Non-vacuity of the frame relation -/

/-- A static frame is related to no model state: v2 obliges nothing there. -/
example {E : Source.Env} {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr)
    (σ : State C Γ) (static : F.static = true) : ¬ FrameRel G F σ :=
  fun h => by simp [h.2.2.2.2.1] at static

/-- Nor is an unchecked frame. -/
example {E : Source.Env} {C : Contract} {Γ : Ctx} (G : Source.Glob E) (F : Source.Fr)
    (σ : State C Γ) (unchecked : F.checked = false) : ¬ FrameRel G F σ :=
  fun h => by simp [h.2.2.2.2.2] at unchecked

/-- `FrameTotal` is refused by a global relation that pins the sender: the
frame premise cannot be emptied through `globRel`. -/
example [FreshNames] (D : Diagram) (total : D.FrameTotal) (b : Body) (u : Emitted)
    (m : Solidity.Lowering.V07.ContextMap b.ctx u.Γ) (production : Production b u)
    (accepted : Accepted u) (assoc : D.Assoc b u m) (G : Source.Glob b.E) (F : Source.Fr)
    (static : F.static = false) (checked : F.checked = true) (src : Source.EMState b.E b.ctx)
    (pinned : ∀ tgt : State u.C u.Γ, D.globRel src.2 tgt → tgt.tx.msgSender.1 ≠ F.sender.val) :
    False :=
  let ⟨tgt, _, glob, frame⟩ := total b u m production accepted assoc G F static checked src
  pinned tgt glob frame.2.1.symm

end Shrink.Lowering

end Solidity.Goals
