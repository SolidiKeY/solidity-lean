import Solidity.Semantics.AbiEntry
import Solidity.Backend.Scalar.Heights

/-! Ordinary indexed ABI entry's initial selector-inclusive head predicate.
Input is an actual size word; equality to a semantic byte length is an explicit
initial representation fact, not a new language admission. Passing this one
predicate does not certify subsequent decoding or entry success. -/
namespace Solidity.Backend.AbiEntry.Interface
structure HeadCheckCertificate (emit : List Solidity.AbiEntry.Param → Program) : Prop where
  correct : ∀ (parameters : List Solidity.AbiEntry.Param) (size : Scalar.Word) (tail : Scalar.Stack),
    Scalar.run (emit parameters) (size::tail)=
      some (Scalar.flag (decide (size.toNat<4+Solidity.AbiEntry.headsOf parameters))::tail)
  capacity : ∀ (parameters : List Solidity.AbiEntry.Param) (tail : Scalar.Stack),
    tail.length+2≤1024 → Scalar.stackBound (emit parameters) ((tail.length+1 : Nat) : Int)=true
  classified : ∀ (input : Solidity.AbiEntry.Input) (parameters : List Solidity.AbiEntry.Param)
    (size : Scalar.Word) (tail : Scalar.Stack), size.toNat=input.size →
    Scalar.run (emit parameters) (size::tail)=
      some (Scalar.flag (decide (input.size<4+Solidity.AbiEntry.headsOf parameters))::tail)
  early_revert : ∀ (input : Solidity.AbiEntry.Input) (fuel : Nat)
    (parameters : List Solidity.AbiEntry.Param),
    input.size<4+Solidity.AbiEntry.headsOf parameters →
    Solidity.AbiEntry.entry input fuel parameters=.error .revert
end Solidity.Backend.AbiEntry.Interface
