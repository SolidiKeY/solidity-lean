import Solidity.Correctness.Lowering.Sim.Match.AssociationV2

/-! Statement-level interface check for the proposed P3 association contract.
This checks that the complete conjunction is a proposition; it supplies no
inhabitant, compatibility proof or coverage witness before owner review. -/
namespace Solidity.Examples.Lowering.Sim.AssociationV2

/-- The proposed compatibility, initial matching and coverage obligations form
one well-typed proposition, not a claimed theorem. -/
example : Prop := Solidity.Correctness.Lowering.Sim.AssociationV2.Contract

end Solidity.Examples.Lowering.Sim.AssociationV2
