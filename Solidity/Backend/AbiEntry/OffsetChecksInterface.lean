import Solidity.Semantics.AbiEntry
import Solidity.Backend.Scalar.Heights

/-! Actual indexed ABI tail/region predicates over runtime words. Stack order
is explicit. No canonicality, unsigned-span restriction, native-load claim or
whole-reference admission follows from either predicate alone. -/
namespace Solidity.Backend.AbiEntry.Interface
structure OffsetChecksCertificate (tailCode regionCode : Program) : Prop where
  tail_correct : ∀ (size base relative extent : Scalar.Word) (suffix : Scalar.Stack),
    Scalar.run tailCode (extent::size::base::relative::suffix)=
      some (Scalar.flag (Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat)::suffix)
  region_correct : ∀ (size address length stride : Scalar.Word) (suffix : Scalar.Stack),
    Scalar.run regionCode (length::stride::size::address::suffix)=
      some (Scalar.flag (Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat)::suffix)
  tail_capacity : ∀ (suffix : Scalar.Stack), suffix.length+5≤1024 →
    Scalar.stackBound tailCode ((suffix.length+4 : Nat) : Int)=true
  region_capacity : ∀ (suffix : Scalar.Stack), suffix.length+5≤1024 →
    Scalar.stackBound regionCode ((suffix.length+4 : Nat) : Int)=true
end Solidity.Backend.AbiEntry.Interface
