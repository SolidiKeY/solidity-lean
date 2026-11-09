# Exact verification

The implementation is [Tools/CompleteVerification.lean](../Solidity/Tools/CompleteVerification.lean)
and its imported exact-reduction modules. `sol_exact` and its suggestion twin
handle recognized reductions. Unsupported cases require another proof route;
source declarations and tests define the fragment.

Keep both directions of every reduction used to certify a counterstate.
A directional proof reduction is insufficient for refutation. Counterstates
must be realizable typed states, including alias consistency, not arbitrary
assignments to independent read occurrences. Search-budget exhaustion and unsupported input
are unknown. Native computation does not replace the final kernel check of a
claimed certificate. General Solidity completeness and reachable-state
reconstruction are not established by this backend.
