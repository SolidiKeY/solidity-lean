# Coordinator-only registration proposal

These standalone audit files remain under the authorized tests directory.
Do not add their test paths to generated library roots. After an area producer
approves an actual library destination, rewrite these rows to its approved paths
and register there; no original producer ownership is transferred.

| Current audit file | Proposed role |
|---|---|
| `tests/h62/item2/audit-bytecode-selection/Witnesses.lean` | Joint feasibility fixtures and exact legacy/negative controls. |
| `tests/h62/item2/audit-bytecode-selection/LiteralSuccess.lean` | Same-selected-code numeric literal totality, success and trivial-selector controls. |
| `tests/h62/item2/audit-bytecode-selection/RuntimePremiseWitness.lean` | Closed nonidentity compiler/decoder/consumer/input witness, with local-adapter boundary. |
| `tests/h62/item2/audit-bytecode-selection/ValueGateSuccess.lean` | Existing public compiler family selection, nonempty success, refusal and mutant controls. |
| `tests/h62/item2/audit-bytecode-selection/BoolBindingSuccess.lean` | Actual selected Boolean binding, simultaneous certificate/memory witness and success/refusal controls; audit-only. |

The HypothesisDomains audit imports the Lean frontend. Keep it audit-only under
tests; it is not proposed for intrinsic library registration.

Scoped axiom inventory proposal: `tests/h62/item2/audit-bytecode-selection/BoolBindingSuccess.pins.json` contains twenty-eight kernel-guarded standard-only records. Coordinator destination: scripts/g07-axiom-pins.d/tests/h62/item2/audit-bytecode-selection/BoolBindingSuccess.json, then regenerate the shared inventory. The preceding checkpoint global scan reported 111 unrecorded changes (twelve then proposed here), zero axiom errors; current results are retained in the new handoff. This lane does not rewrite the shared inventory.

FailurePathsWitnesses also imports the audit elaborator through HypothesisDomains.
Keep it audit-only under tests; no intrinsic registration is proposed.
