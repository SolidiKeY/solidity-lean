# Registration proposal for coordinator review

Current additive file: `tests/h62/item2/audit-exact-verification/VisitedSetAudit.lean`.
It imports unchanged `Solidity.Calculus.VisitedSet` and certifies nine local input
bundles plus walk success/reject-all/fuel controls. No root/map/pin edits made.

Proposed destination if the exact-verification area producer approves registration:
the module `Solidity.Examples.H62VisitedSetAudit`, with a row in that area's producer
fragment describing the nine witness bundles and their limited helper scope.
The coordinator must choose/register the final module name and axiom pins.
This proposal does not authorize moving the file or changing generated roots.

## H70 additive files, registration still pending owner review

- `tests/h62/item2/audit-exact-verification/JointWitness.lean`: test-only binder/type/axiom machinery.
- `tests/h62/item2/audit-exact-verification/JointWitnessControls.lean`: hidden-premise rejection and feasible dependent control.
- `tests/h62/item2/audit-exact-verification/BitArithAudit.lean`: 16 source instances.
- `tests/h62/item2/audit-exact-verification/LinearDecisionAudit.lean`: 80 source instances.
- `tests/h62/item2/audit-exact-verification/LinearHypothesesAudit.lean`: one source instance and three local controls.
- `tests/h62/item2/audit-exact-verification/RecoveryAudit.lean`: two unconditional instances and two local controls.
- `tests/h62/item2/audit-exact-verification/IndependentModuleCensus.lean`: exact compiler theorem census for six imported modules.

Do not register or move these automatically. The timing gate failed and all
full-assignment obligations remain incomplete. Central roots/maps/pins unchanged.
