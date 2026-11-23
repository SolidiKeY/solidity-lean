import Solidity.Correctness.Lowering.Sim.Coverage.ThreadedV2

/-!
# Production with caller placement

The additive H1182 boundary retains every v1 producer receipt and adds the
caller placement from `ThreadedV2`. This does not claim Source decoding or
coverage: the frozen association still requires `Total.Spells`.
-/
namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering

/-- Actual production, with the caller context and names threaded as well. -/
def ProductionV2 [FreshNames] (b : Body) (u : Emitted) : Prop :=
  Lowered b u ∧ Checker.ElaborationReceipt u.output ∧ ThreadedV2 b u

theorem ProductionV2.toProduction [FreshNames] {b : Body} {u : Emitted}
    (h : ProductionV2 b u) : Production b u :=
  ⟨h.1, h.2.1, h.2.2.toThreaded⟩

/-- Coverage at the versioned production boundary; acceptance is unchanged. -/
def TotalV2 [FreshNames] (D : Diagram) : Prop :=
  ∀ (b : Body) (u : Emitted), ProductionV2 b u → Accepted u →
    ∃ b' : Body, b'.SameInput b ∧ ∃ m, D.Assoc b' u m

end Solidity.Correctness.Lowering.Sim.Coverage
