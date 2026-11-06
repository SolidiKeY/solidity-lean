import Solidity.Source.Infer
import Solidity.Frontend.Static.Infer

/-!
Candidate case specifications for the copied inference helpers. This file is
an additive test, not a replacement for either inferencer. The constructor
inventory is explicit so that a new `STy` constructor requires review.
The file requires a successful Lean check before its theorems are evidence.
-/

namespace Solidity.H62.InferHelpers

open Solidity.Source

/-- Expected mapping, payable-argument and conversion-location results. -/
def expected : STy → Bool × Bool × DataLoc
  | .int _ => (false, false, .memory)
  | .bool => (false, false, .memory)
  | .address _ => (false, true, .memory)
  | .fixedBytes _ _ => (false, false, .memory)
  | .fixed _ => (false, false, .memory)
  | .enum _ => (false, false, .memory)
  | .udvt _ => (false, false, .memory)
  | .contract _ => (false, true, .memory)
  | .bytes loc => (false, false, loc)
  | .string loc => (false, false, loc)
  | .array _ _ _ => (false, false, .memory)
  | .struct _ _ => (false, false, .memory)
  | .mapping _ _ => (true, false, .memory)
  | .fn _ _ _ _ => (false, false, .memory)
  | .rational _ => (false, false, .memory)
  | .hexConst _ _ => (false, false, .memory)
  | .stringLit _ => (false, false, .memory)
  | .tuple _ => (false, false, .memory)

/-- All source helper results agree with the constructor specification. -/
theorem source_cases (τ : STy) :
    expected τ = (τ.isMapping, τ.isPayableArg, τ.convLoc) := by
  cases τ <;> rfl

/-- All static helper results agree with the same constructor specification. -/
theorem static_cases (τ : STy) :
    expected τ = (Solidity.Frontend.Static.isMappingTy τ,
      Solidity.Frontend.Static.payableArg τ, Solidity.Frontend.Static.convLoc τ) := by
  cases τ <;> rfl

end Solidity.H62.InferHelpers
