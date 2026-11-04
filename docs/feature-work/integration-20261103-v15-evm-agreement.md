# v15-evm-agreement integration checkpoint

Producer: `5ec4d8cc9c386b1f28a7e18f08c86ec15ba2cd56`. This imports only the following modules:

- `Bridge/SolidityBridge/RoadmapV15/P10/NegationBody.lean`
- `Bridge/SolidityBridge/RoadmapV15/P10/NegationBodyControls.lean`
- `Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceConsumer.lean`
- `Bridge/SolidityBridge/RoadmapV15/P10/NegationSourceControls.lean`

The increment preserves the producer statements, hypotheses and exclusions;
it does not establish completion of the remaining lane queue.
Touched-module and library checkpoint gates pass: trust, roots, orphans,
layers, documentation paths and axiom inventory.
The selected Bridge modules also pass their kernel build.
Independent read-only finder and skeptic reviews are required before publication.

Finder and skeptic reviews passed. Confirmed fixes and retained boundaries are
recorded in the [integration milestone](integration-20261103-checkpoints.md).
