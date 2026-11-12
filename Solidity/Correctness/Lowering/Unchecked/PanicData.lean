import Solidity.Lowering.V08.AbiObservations

/-!
# Panic bytes at the unchecked boundary

Guards loss or alteration of panic payloads when relating Source failures to
retained model revert data. Unchecked arithmetic suppresses overflow checks,
but division by zero and other panics remain observable. This codec law covers
every Source panic code, including arithmetic; it does not identify a model
halt with a Source halt or supply a program-observation bridge.
-/
/- Reuse the canonical codec agreement rather than maintaining an unchecked
copy. This guard checks its standard-only axiom boundary; the execution still
must select and retain the payload at the observation boundary. -/
#print axioms Solidity.Lowering.V08.panicData_transport
