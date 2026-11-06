import Solidity.Backend.InternalFlow.RuntimeFrameV4Migration
import Solidity.Backend.InternalFlow.RuntimeFrameV3FrozenScopeCoverage

/-! Migration controls on a populated recursive family: the scoped scalar
family's V3 producer moves to V4 with the same plan, and back to V3 with its
own reverting entry. Only the external approved-domain agreement is an input,
as in `FrozenScopeCoverage.with_profile`. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V4MigrationControls
open Evm Evm.Memory V4Migration
open DisjointScalarReturn.Client (Γ F reference)

def family (approved : Nat → InterfaceV3.Admission SameCallInputs.C Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved FrozenScopeCoverage.inputs) :=
  FrozenScopeCoverage.with_profile approved agreement

def familyV4 (approved : Nat → InterfaceV3.Admission SameCallInputs.C Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved FrozenScopeCoverage.inputs) :=
  recursive_ofV3 (family approved agreement)

theorem same_plan (approved : Nat → InterfaceV3.Admission SameCallInputs.C Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved FrozenScopeCoverage.inputs) :
    (familyV4 approved agreement).plan = (family approved agreement).plan := rfl

/-- Back to V3, supplying the original reverting entry. -/
theorem round_trip (approved : Nat → InterfaceV3.Admission SameCallInputs.C Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved FrozenScopeCoverage.inputs) :
    recursive_toV3 (familyV4 approved agreement)
      (family approved agreement).required_reverting_entry = family approved agreement :=
  recursive_round_trip _

end Solidity.Backend.InternalFlow.RuntimeFrame.V4MigrationControls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V4MigrationControls.round_trip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V4MigrationControls.round_trip
