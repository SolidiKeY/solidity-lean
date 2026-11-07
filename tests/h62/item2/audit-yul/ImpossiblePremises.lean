import Solidity.Lowering.P8.ResourceContractLaw1
/-! The frozen mapped statement is an intentional impossibility result.
Its entire premise telescope cannot have a simultaneous witness. The
unchanged frozen interface and the original proof dependency suffice; importing
the unrelated Source session runner is not needed to state these premises. This audit
certificate preserves the original theorem and supplies no new premise. -/
namespace H62.AuditYul
open Solidity.Lowering.P8

def CountableResourcePremises : Prop :=
  ∃ (S : P8a.Spec) (_failures : P8a.FailureProjection S)
    (encode : S.lang.Res → Nat) (decode : Nat → S.lang.Res),
    ∀ r, decode (encode r) = r

theorem no_countable_resource_joint_witness : ¬ CountableResourcePremises := by
  rintro ⟨S, failures, encode, decode, roundtrip⟩
  exact ResourceContractLaw1.nat_encodable_resource_impossible S failures encode decode roundtrip

#print axioms no_countable_resource_joint_witness
end H62.AuditYul
