import Solidity.Semantics.AbiEntry
import Solidity.Backend.Scalar.Heights

/-! Contracts for emitted primitive validators in the existing numeric runner.
These certify neither calldata loading nor control flow, gas, or full decoding.
The original word is consumed; every arbitrary stack suffix is retained. -/
namespace Solidity.Backend.AbiEntry.Interface

/-- Concrete bytecode accepts exactly the semantic word predicate. Scratch
bounds extra stack cells above the input word, at every instruction boundary.
No source-input admission predicate can narrow the accepted encodings. -/
structure WordValidator (kind : Solidity.AbiEntry.Kind) where
  code : Program
  scratch : Nat
  scratch_fits : 1 + scratch ≤ 1024
  correct : ∀ (word : Scalar.Word) (tail : Scalar.Stack),
    Scalar.run code (word :: tail) =
      some (Scalar.flag (kind.valid word.toNat) :: tail)
  capacity : ∀ (tail : Scalar.Stack), tail.length + 1 + scratch ≤ 1024 →
    Scalar.stackBound code ((tail.length + 1 : Nat) : Int) = true

end Solidity.Backend.AbiEntry.Interface
