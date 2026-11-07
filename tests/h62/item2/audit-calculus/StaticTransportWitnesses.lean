import Solidity.Examples.Tactics.StaticStorageCompatibility
import tests.h62.item2.«audit-calculus».KernelCensus

/-! Closed joint hypotheses for the unchanged static try transports.
The nonself condition is exercised with self=true and receiver7.
Frame/decoder witnesses do not authenticate source/native opaque calls. -/
namespace H62.AuditCalculus.StaticTransport
open Solidity Solidity.Semantics
abbrev C := Solidity.Examples.Tactics.ExternalReturnBytes.C
private def sigma : State C [] := State.init C
private def invariant : StateInv C := ⟨fun state => state.storage = sigma.storage, true⟩
private def call : ExtCall C [] := ⟨.lit 7 rfl, "fetch", [], .static, .site 0⟩
private def payload : List UInt8 := wordBytes 1
private def word : Semantics.Word := ⟨1, rfl⟩
private def credited := Solidity.Examples.Tactics.StaticStorageCompatibility.credited

#joint_premises Solidity.ExecS.static_tryOk_of_storage_frame as rawPremises
/-- All hypotheses use the same static frame, receiver, decoder and continuation. -/
theorem raw_joint : rawPremises := by
  refine ⟨C, invariant, [], [], [], [], [], [], [], [], [],
    sigma, sigma, call, 0, .nil, .nil, .nil, .none, .nil, .nil, .nil, .nil,
    true, payload, rfl, rfl,
    ⟨sigma, .returned .static sigma payload, rfl⟩,
    rfl, rfl, rfl, [word], [word], (), rfl,
    .ok ⟨sigma, List.prefix_refl _⟩, ?_, .nil, True.intro⟩
  intro _
  constructor <;> decide

#joint_premises Solidity.ExecS.static_tryOk_of_declared_return_bytes as declaredPremises
/-- The nonempty bytes validate the declared integer before all results are discarded. -/
theorem declared_joint : declaredPremises := by
  refine ⟨C, invariant, [], [], [], [], [], [], [], [], [],
    sigma, sigma, call, 0, .nil, .nil, .nil, .none, .nil, .nil, .nil, .nil,
    true, payload, [.int],
    Solidity.Examples.Tactics.PrimitiveReturnConsumer.integer, .discard _,
    rfl, rfl, ⟨sigma, .returned .static sigma payload, rfl⟩, rfl, rfl, rfl,
    [], (), Solidity.Examples.Tactics.PrimitiveReturnConsumer.canonical_int_discard,
    .ok ⟨sigma, List.prefix_refl _⟩, ?_, .nil, True.intro⟩
  intro _
  constructor <;> decide

#joint_premises Solidity.ExecS.static_tryOk_storage_only as storagePremises
/-- The storage invariant holds jointly with a genuinely changed ledger and balance. -/
theorem storage_joint : storagePremises := by
  refine ⟨C, invariant, [], [], [], [], [], [], [], [], [],
    sigma, credited, call, 0, .nil, .nil, .nil, .none, .nil, .nil, .nil, .nil,
    true, payload, [.int],
    Solidity.Examples.Tactics.PrimitiveReturnConsumer.integer, .discard _,
    rfl, rfl, Solidity.Examples.Tactics.StaticStorageCompatibility.actual_frame,
    rfl, rfl, [], (),
    Solidity.Examples.Tactics.PrimitiveReturnConsumer.canonical_int_discard,
    .ok ⟨credited, List.prefix_refl _⟩, ?_, .nil, True.intro⟩
  intro _
  constructor <;> decide

/-- The exact storage-only frame has observable ledger and balance changes.
This is the operational frame relation; no physical STATICCALL adequacy is asserted. -/
theorem credit_boundary : credited.storage = sigma.storage ∧
    credited.net ≠ sigma.net ∧ credited.selfBalance ≠ sigma.selfBalance := by
  exact ⟨rfl, by decide, Solidity.Examples.Tactics.StaticStorageCompatibility.changed_balance⟩

#verify_joint Solidity.ExecS.static_tryOk_of_storage_frame with raw_joint
#verify_joint Solidity.ExecS.static_tryOk_of_declared_return_bytes with declared_joint
#verify_joint Solidity.ExecS.static_tryOk_storage_only with storage_joint
#audit_module "Solidity.Calculus.StaticInvocation"
#audit_module "Solidity.Calculus.PrimitiveReturnTransport"
#audit_module "Solidity.Calculus.StaticStorageTransport"
#print axioms credit_boundary
end H62.AuditCalculus.StaticTransport
