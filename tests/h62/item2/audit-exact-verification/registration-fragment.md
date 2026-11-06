# Registration proposal for coordinator review

Current additive file: `tests/h62/item2/audit-exact-verification/VisitedSetAudit.lean`.
It imports unchanged `Solidity.Calculus.VisitedSet` and certifies nine local input
bundles plus walk success/reject-all/fuel controls. No root/map/pin edits made.

Proposed destination if the exact-verification area producer approves registration:
the module `Solidity.Examples.H62VisitedSetAudit`, with a row in that area's producer
fragment describing the nine witness bundles and their limited helper scope.
The coordinator must choose/register the final module name and axiom pins.
This proposal does not authorize moving the file or changing generated roots.
