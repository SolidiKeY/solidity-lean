import Solidity.Correctness.Lowering.Sim.Match

/-!
# Caller-context threading (H1182)

An additive prerequisite for `Solidity.Goals.loweringBySimulation`.
The frozen v1 `Threaded` remains unchanged. This contract adds exactly the
caller context and names required by `Sim.Assoc`; it does not produce these
equalities or establish restricted coverage, decoding, or full coverage.
-/

namespace Solidity.Correctness.Lowering.Sim.Coverage

open Solidity.Goals.Shrink.Lowering
open Solidity.Lowering.V07 (ContextMap)

/-- V1 state threading together with the caller context and names. -/
def ThreadedV2 (b : Body) (u : Emitted) : Prop :=
  Threaded b u ∧ u.Γ = (request b u).context.ctx ∧
    u.output.names = (request b u).context.names

/-- Forgetting caller placement recovers the frozen v1 receipt. -/
theorem ThreadedV2.toThreaded {b : Body} {u : Emitted}
    (h : ThreadedV2 b u) : Threaded b u :=
  h.1

/-- An existing association supplies exactly the two extra equalities. -/
theorem ThreadedV2.ofAssoc {b : Body} {u : Emitted} {m : ContextMap b.ctx u.Γ}
    (threaded : Threaded b u) (assoc : Assoc b u m) : ThreadedV2 b u :=
  ⟨threaded, assoc.1, assoc.2.1⟩

end Solidity.Correctness.Lowering.Sim.Coverage
