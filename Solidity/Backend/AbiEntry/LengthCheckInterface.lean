import Solidity.Semantics.AbiEntry
import Solidity.Backend.Scalar.Heights

/-! Loaded dynamic-length admission at the actual semantic limit. Native load
correspondence and other entry guards are separate obligations. -/
namespace Solidity.Backend.AbiEntry.Interface
structure LengthCheckCertificate (code : Program) : Prop where
  correct : ∀ (length : Scalar.Word) (suffix : Scalar.Stack),
    Scalar.run code (length::suffix)=
      some (Scalar.flag (decide (length.toNat≤Solidity.AbiEntry.lim))::suffix)
  capacity : ∀ (suffix : Scalar.Stack), suffix.length+2≤1024 →
    Scalar.stackBound code ((suffix.length+1 : Nat) : Int)=true
  lazy_revert : ∀ (input : Solidity.AbiEntry.Input) (shape : Solidity.AbiEntry.Shape)
    (base pointer : Nat),
    Solidity.AbiEntry.tailFits input.size base (Solidity.AbiEntry.load input.data pointer) shape.tailSize=true →
    shape.lengthPrefixed=true →
    Solidity.AbiEntry.lim<Solidity.AbiEntry.load input.data
      (Solidity.AbiEntry.wrap (base+Solidity.AbiEntry.load input.data pointer)) →
    Solidity.AbiEntry.tailRef input shape base pointer=.error .revert
end Solidity.Backend.AbiEntry.Interface
