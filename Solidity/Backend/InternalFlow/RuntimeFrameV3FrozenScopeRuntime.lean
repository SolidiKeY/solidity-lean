import Solidity.Backend.InternalFlow.RuntimeFrameV3FrozenScopeClient

/-! Inhabited runtime-side assembly for the exact frozen scoped family.
This is the existing V2 contract, not approved-domain or V3 coverage closure.
Both source outcomes have actual represented witnesses for the same arguments.
General recursion, exhaustion simulation and profile provenance remain open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeRuntime
open Evm Evm.Memory
open DisjointScalarReturn.Client (Γ F reference)

def producer : InterfaceV2.PendingRecursiveReturns 1 F "scalarCountdown"
 (DisjointScalarEntry.args rfl reference ScalarReentry.count)
 (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (FrozenScopeFamily.step CountdownWitness.A rfl .uint (.user "sameCall")) where
 plan := ScalarReentry.plan
 required_successful_entry := ⟨4,FrozenScopeClient.successful_entry⟩
 required_source_coherence := FrozenScopeClient.coherence
 required_return := fun depth => FrozenScopeCompiler.returns ScalarReentry.emitted ScalarReentry.selected
   (by decide) rfl reference .here "scalarCountdown" .uint (.user "sameCall") depth
 required_bare_revert := fun depth => FrozenScopeCompiler.bare_revert ScalarReentry.emitted ScalarReentry.selected
   (by decide) rfl reference .here "scalarCountdown" .uint (.user "sameCall") depth

theorem reverting_entry (depth : Nat) : InterfaceV2.RevertingEntry 1 F
 (InterfaceV1.recursiveSource "scalarCountdown" (DisjointScalarEntry.args rfl reference ScalarReentry.count)
 (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
 (FrozenScopeFamily.step CountdownWitness.A rfl .uint (.user "sameCall")) depth) (producer.plan.at depth) :=
 FrozenScopeClient.reverting_entry depth

end Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeRuntime
