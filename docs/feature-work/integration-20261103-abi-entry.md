# abi-entry integration checkpoint

Producer: `cbfc15dd7d05a5278bb12dff184450b3a2b41f82`. This imports only the following modules:

- `Bridge/SolidityBridge/AccessBridge/Interface.lean`
- `Bridge/SolidityBridge/AccessBridge/MemoryCharged.lean`
- `Bridge/SolidityBridge/AccessBridge/MemoryControls.lean`
- `Bridge/SolidityBridge/AccessBridge/MemoryInterface.lean`
- `Bridge/SolidityBridge/AccessBridge/MemoryLoad.lean`
- `Bridge/SolidityBridge/AccessBridge/MemoryLoadControls.lean`
- `Bridge/SolidityBridge/AccessBridge/MemoryLoadInterface.lean`

The increment preserves the producer statements, hypotheses and exclusions;
it does not establish completion of the remaining lane queue.
Touched-module and library checkpoint gates pass: trust, roots, orphans,
layers, documentation paths and axiom inventory.
The selected Bridge modules also pass their kernel build.
Independent read-only finder and skeptic reviews are required before publication.

Finder and skeptic reviews passed. Confirmed fixes and retained boundaries are
recorded in the [integration milestone](integration-20261103-checkpoints.md).
