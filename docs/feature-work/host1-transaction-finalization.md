# HOST1 message finalization for V17/G52

H10-HOST1 authorizes this VY5 help producer. Development base:
`c53e2a17fb43630716f540838526ca47bea5fbd3`; branch
`codex/solidity-inline-assembly5-20261031/vy5-composition-help`.
Original VY5 tree and blocked goal are preserved; this package does not close Y10.

## Public contract

[Typed interface](../../scripts/host1-finalization/interface.mts) exports
`createFinalizationSession`, branded request parsers, immutable receipts,
`validateFinalizedMessage` and checked observed-account/slot readers.
[Runner](../../scripts/host1-finalization/reference.mjs) freezes independent
source expectations before execution. Install the existing pinned reference
engine dependencies as documented in its directory; no pin changes are needed.

The producer uses the existing exported machine and public instance events/state
APIs. It executes `runCall`, then explicitly finalizes that message boundary:
consume actual committed SELFDESTRUCT/created-address substate, apply EIP-6780
eligible deletion, perform journal cleanup, clear transient storage, and commit
its outer checkpoint. Beneficiary transfer is already performed by the engine.
SimpleStateManager deletion requires clearing storage and code before metadata;
the receipt records these actual operations and their order. Missing committed
root substate blocks capture; it never means an empty set. Host limits poison the
session and produce no finalized receipt.

This is not `runTx`: no signed envelope, intrinsic gas, fee accounting, state root,
or untouched-world completeness is asserted. Snapshot domains contain observed
and explicitly declared accounts/slots. Unknown state remains unavailable.
Account/code/storage identity, DELEGATECALL storage ownership, ordered frames,
full bytes/logs, raw frame memory, semantic RETURN/REVERT windows, retained
returndata and transient pre/post images are recorded separately. Raw compiler
memory is not equated across pipelines. Empty-code roots lacking engine substate
are blocked. This is an external DTO/API contract, not a new intrinsic Source IR.

## Validation and reviews

Node 24.19.0; strict TypeScript 5.9.3 checks the actual interface and invalid
consumer examples (third-party declaration checking uses skipLibCheck).
All 81 tests pass, including actual five-million-step limit refusal, malformed
and missing evidence, coordinated domain erasure, wrong owner/state/bytes,
creation/deletion ordering, concurrency, stale fingerprints and pipeline identity.
All 56 fresh native calls pass: 14 ordered calls under each legacy/viaIR and
optimizer-off/on profile, pinned solc 0.8.38+commit.1835d247 and Osaka.
Independent plans cover CREATE/CREATE2 reuse and rollback, existing-account
SELFDESTRUCT, self-beneficiary, transient reset, static refusal, touched-empty
cleanup and constructor revert. ConstructorDie is compiled but not executed by
the matrix; constructor SELFDESTRUCT has a separate literal-bytecode smoke test.
Source/settings/compiler/runtime/helper/code fingerprints are checked on replay.

Separate read-only finder and skeptic reviews identified and verified repairs to
frame code/storage ownership, parent call conventions, touched-domain binding,
creation-address binding, nondeleted-state preservation and transient cleanup.
Final review records and raw passing/failing invocations are retained in
`/workspace/vy5-composition/host1-help-20261102/` and its sealed final package.
Checks run serially under the writer lock, hard 12 GiB/no-swap cap, CPU1 and H1
4 GiB available-memory reserve; fixed gas/instruction budgets are unchanged.

No Lean files/imports or Source/replay-engine implementations changed. No new
kernel, KeySort, axiom or compiler-correctness pass is claimed by these scripts.
Original historical docs/G03 failures and strict native journal failure remain
separate retained evidence. All 24 original Y10 obligations, six general Source
combinations, raw hooks, frontend admission, allocation/refinement/G01,
compiler/world/V16 adequacy and joint kernel closure remain open. V17 may consume
this producer only within its documented finite message-boundary domain.
