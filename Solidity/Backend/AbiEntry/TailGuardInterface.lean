import Solidity.Backend.AbiEntry.OffsetChecksInterface

/-! Composed length-prefixed tail guard over actual runtime operands. Native
operand loading and fetched conditional branching remain separate contracts. -/
namespace Solidity.Backend.AbiEntry.Interface
structure TailGuardCertificate (code : Program) : Prop where
  correct : ∀ (size base relative extent length stride address : Scalar.Word)
    (suffix : Scalar.Stack),
    Scalar.run code (extent::size::base::relative::length::stride::size::address::suffix)=
      some (Scalar.flag (Solidity.AbiEntry.tailFits size.toNat base.toNat relative.toNat extent.toNat &&
        decide (length.toNat≤Solidity.AbiEntry.lim) &&
        Solidity.AbiEntry.regionFits size.toNat address.toNat length.toNat stride.toNat)::suffix)
  capacity : ∀ (suffix : Scalar.Stack), suffix.length+9≤1024 →
    Scalar.stackBound code ((suffix.length+8 : Nat) : Int)=true
end Solidity.Backend.AbiEntry.Interface
