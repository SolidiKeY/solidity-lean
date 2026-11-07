import Solidity.Backend.AbiEntry.CalldataWordInterface
import Solidity.Backend.Scalar.Heights

/-! Four-byte selector comparison in the existing numeric compiler. Raw source
agreement needs a complete prefix; short-input dispatch is a separate guard. -/
namespace Solidity.Backend.AbiEntry.Interface
structure SelectorMatchCertificate (emit : Vector UInt8 4 → Program) : Prop where
  numeric : ∀ (selector : Vector UInt8 4) (word : Scalar.Word) (suffix : Scalar.Stack),
    Scalar.run (emit selector) (word::suffix)=
      some (Scalar.flag (decide (word.toNat/2^224=Source.beValue selector.toList))::suffix)
  raw : ∀ (selector : Vector UInt8 4) (frame : Source.Fr), 4≤frame.cd.length →
    ∀ suffix : Scalar.Stack,
    Scalar.run (emit selector) (BitVec.ofNat 256 (Solidity.AbiEntry.load frame.cd 0)::suffix)=
      some (Scalar.flag (frame.cd.take 4==selector.toList)::suffix)
  capacity : ∀ (selector : Vector UInt8 4) (suffix : Scalar.Stack), suffix.length+2≤1024 →
    Scalar.stackBound (emit selector) ((suffix.length+1 : Nat) : Int)=true
end Solidity.Backend.AbiEntry.Interface
