import Solidity.Goals.LoweringSim
import Solidity.Syntax.Splice

namespace Solidity.Goals

/--
info: open Solidity.Goals.loweringBySimulation ← Solidity.Correctness.Lowering.Sim.lowering_producer plan ls3-lowering-compose
-/
#guard_msgs in
#roadmap_goal loweringBySimulation

/--
info: open Solidity.Goals.loweringBySimulationV2 ← Solidity.Correctness.Lowering.Sim.lowering_producer_v2 blocked by [Solidity.Goals.intrinsicSessionSemantics, Solidity.Goals.intrinsicStorageAccounting] plan ls3-lowering-compose
-/
#guard_msgs in
#roadmap_goal loweringBySimulationV2

/-- v1 is the statement before H556 option A. -/
example : Solidity.Goals.loweringBySimulation =
    (letI : FreshNames := Solidity.Goals.Shrink.Lowering.productionNames;
      Solidity.Goals.Shrink.Lowering.CallerBound ∧
        ∃ D : Solidity.Goals.Shrink.Lowering.Diagram, D.Simulates ∧ D.Total) := rfl

/-- v2 is additive: v1 is a conjunct of it. -/
example : Solidity.Goals.loweringBySimulationV2 → Solidity.Goals.loweringBySimulation :=
  fun ⟨bound, D, simulates, total, _⟩ => ⟨bound, D, simulates, total⟩

namespace Shrink.Lowering

open Solidity.Roadmap (Prefix)
open Solidity.Roadmap.G49Final (Behaviour PassCorrect)
open Solidity.Semantics.IntrinsicSession (spec)

variable [FreshNames]

/-- The lowered world's entries are elaborated exactly as `elabProgS` does. -/
example (C : Contract) : topBlock C = elabProgS C := rfl

/-! ## Non-vacuity: `Lift` (hence `SessionLift`) is refused -/

/-- **A target session with no events** refines no source that shows an event
at a ready horizon. -/
theorem lift_refused_silent (D : Diagram) (F : Roadmap.Fixed) {E : Source.Env}
    (P : Source.SrcProg E) (c : Compilation)
    (silent : ∀ e r, ((spec F).lang.sem (loweredWorld c) e r).events = [])
    (shows : ∃ e n, e.Allowed ∧ (sourceBehaviour D F P (loweredWorld c)).Ready e n ∧
      ((Source.sourceLangEvents E).sem P e n).events ≠ []) :
    ¬ Lift D F P c := by
  rintro ⟨⟨pc, abs, _⟩, _⟩
  obtain ⟨e, n, allowed, ready, events⟩ := shows
  have le := (pc.need_ok e n allowed (by rw [abs]; exact ready)).2
  rw [abs] at le
  exact events (List.prefix_nil.1 (silent e _ ▸ le.1))

/-- **A source that never completes** is refined by no target session that
completes at a guarded bound without resource failure: the backward clause is
not discharged by the target alone. -/
theorem lift_refused_stuck (D : Diagram) (F : Roadmap.Fixed) {E : Source.Env}
    (P : Source.SrcProg E) (c : Compilation)
    (never : ∀ e n, ((Source.sourceLangEvents E).sem P e n).final = none)
    (completes : ∃ e r o, e.Allowed ∧ r.NoFail ∧ (spec F).lang.Guard (loweredWorld c) e r ∧
      ((spec F).lang.sem (loweredWorld c) e r).final = some o) :
    ¬ Lift D F P c := by
  rintro ⟨⟨pc, abs, _⟩, _⟩
  obtain ⟨e, r, o, allowed, noFail, guard, done⟩ := completes
  obtain ⟨n, _, _, le⟩ := pc.back e r allowed noFail guard
  have final : ((Source.sourceLangEvents E).sem P e n).final = some o := by
    have same := congrArg Prefix.final (le.final_eq done)
    rw [abs] at same
    exact same.trans done
  rw [never] at final
  cases final

end Shrink.Lowering

end Solidity.Goals
