import Solidity.Lowering.P8.FrozenInterface
import Solidity.Source.FailureResources

/-! P8-SPEC-LAW1: consume the existing kernel-checked diagonal obstruction.
This does not revise either frozen contract or extend the source evaluator. -/
namespace Solidity.Lowering.P8.ResourceContractLaw1
open P8a

/-- Full SourceSpec failure replacement plus the frozen projection forces an
arbitrary-plan retraction from the resource. If that resource embeds in Nat
with a decoder, the existing frame diagonal contradicts the two contracts.
(A `Nat` resource is the case `encode = decode = id`.) No NoFail, execution,
frame-count, finite-sample or new premise is substituted for full plan coverage. -/
theorem nat_encodable_resource_impossible (S : Spec) (F : FailureProjection S)
    (encode : S.lang.Res → Nat) (decode : Nat → S.lang.Res)
    (roundtrip : ∀ r, decode (encode r) = r) : False := by
  apply Source.FailureResources.no_horizon_retraction
    (fun n => F.points (S.failures (decode n)))
    (fun n p => encode (S.withFailures (decode n) (F.ofPoints p)))
  intro n p
  rw [roundtrip, S.failures_with, F.points_ofPoints]

/-- info: 'Solidity.Lowering.P8.ResourceContractLaw1.nat_encodable_resource_impossible' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms nat_encodable_resource_impossible
end Solidity.Lowering.P8.ResourceContractLaw1
