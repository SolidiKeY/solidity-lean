import Solidity.Source.Observe
import Solidity.RevertBytes

/-!
# Panic bytes at the unchecked boundary

Guards loss or alteration of panic payloads when relating Source failures to
retained model revert data. Unchecked arithmetic suppresses overflow checks,
but division by zero and other panics remain observable. This codec law covers
every Source panic code, including arithmetic; it does not identify a model
halt with a Source halt or supply a program-observation bridge.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- The two independently defined panic encoders produce identical bytes.
No assumption rules out arithmetic overflow, division by zero, or any other
panic. A semantic bridge must still prove that the actual execution selects
this payload and retains it at the observation boundary. -/
theorem panicData_exact (code : Source.PanicCode) :
    Source.panicData code = Semantics.encodePanic code.code := by
  cases code <;> rfl

#print axioms panicData_exact

end Solidity.Correctness.Lowering.Unchecked
