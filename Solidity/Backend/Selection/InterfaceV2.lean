import Solidity.Backend.Selection.Interface

/-!
# Physical frame capacity contract, version 2

The published V1 frame contract remains available for compatibility, but its
conditional prefix field is not a physical-capacity certificate. This contract
requires actual prefix capacity for every tail admitted by an explicit peak.
The empty tail is always admitted, so capacity cannot be made vacuous by
choosing a peak that leaves no room. Numeric execution is still Scalar.run.
-/
namespace Solidity.Backend.Selection.V2

/-- A successful frame transformation with an inhabited physical room domain.
`peak` is a sufficient extra-word allowance above the complete input height;
it need not be the least possible peak. Larger tails retain the gasless frame
law but have no physical-capacity claim. -/
structure FrameCertificate (input output : Scalar.Stack) where
  code : Program
  peak : Nat
  inputRoom : input.length + peak ≤ 1024
  frame : ∀ tail : Scalar.Stack,
    Scalar.run code (input ++ tail) = some (output ++ tail)
  capacity : ∀ tail : Scalar.Stack,
    (input ++ tail).length + peak ≤ 1024 →
    Scalar.stackBound code ((input ++ tail).length : Int) = true

end Solidity.Backend.Selection.V2
