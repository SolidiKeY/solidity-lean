import Solidity.Lowering.G16.AddressLiterals
import Solidity.Lowering.V07.WordCastControls

/-! Inhabited literal clients and negative controls for address digit order
and the required 160-bit reduction. -/
namespace Solidity.Lowering.G16.AddressLiteralControls
open Solidity.Lowering.V07
open Solidity.Lowering.G16.AddressLiterals

/-- The concrete source and target fixtures contain live reference bindings. -/
def client (digits : List (Fin 16)) (pipeline : Roadmap.Pipeline) (fuel : Nat) :=
  transport (MixedAssignmentControls.globals pipeline) Source.SemanticsExamples.F0 fuel
    (WordCastControls.source .u8 0 1 (by decide) (by decide))
    (WordCastControls.target .u8 0 1 (by decide) (by decide)) digits

/-- Guards against little-endian digit folding and dropping the Source
literal's 160-bit reduction on an overlong resolved digit list. -/
theorem wrong_address_rejected :
    (address [1,2]).val ≠ 33 ∧
    (address (1 :: List.replicate 40 0)).val = 0 ∧
    (address (1 :: List.replicate 40 0)).val ≠ 2 ^ 160 := by
  decide

end Solidity.Lowering.G16.AddressLiteralControls

/-- info: 'Solidity.Lowering.G16.AddressLiteralControls.wrong_address_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.AddressLiteralControls.wrong_address_rejected
