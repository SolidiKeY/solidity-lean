# Actual packet-emitter instruction prefixes

PacketPrefix.take_split derives actual emit.take(3*k+r) from existing writes
append/length laws. boundary proves checkedRun after k complete MSTORE8 writes,
with original stack and exact partial memory. boundary_bytes exposes complete
ordered written bytes and every untouched address. byte_push/byte_offset_push
show the pending byte and address above it before the write. length_push and
offset_push show terminal length and offset words in their real stack order;
complete proves RETURN or REVERT only after the final instruction.
The after_terminal law proves stability of longer prefixes even when their
unreachable suffix would be unsupported by Slice.

checked_writes_tail takes the actual stackSafe Boolean, not a desired execution
oracle. Every headline phase discharges it using Fits and initialstack+2<=1024.
The code and machine are the existing Failure.Emit/Slice definitions, unchanged.
There is no new evaluator, opcode, fuel semantics or widening of the reserved
slice. Counts are Slice instructions, not encoded-byte PCs, gas, transaction
resources, fetched EVM execution or source-call adequacy. Reaching a truncated
program with outcome none is pending, not source exhaustion/divergence.

Controls use actual uint300/bytes[0,255] ABI result128bytes, a nonempty stack and
older memory165. All k boundaries/byte phases have inhabited applied theorems.
Snapshots retain full reached stack, entire payload-window memory, old/post-span
sentinels and distinct fault/pending/return/revert observations. Word boundaries
and payload offsets are exercised; pushing byte/address does not prematurely
write memory, and no RETURN appears before its actual terminal. Crowded1023
stack rejects the second push. RETURN/customREVERT/empty/Panic/Error constructor
controls reuse actual code, not expected output tables.

Automation-first failed on generic prefix decomposition. Existing list/writes
laws complete it. Raw syntax/control-recursion failures retained; controls use
proved codec length/layout instead of increasing recursion or heartbeat limits.
No new axioms/sorry/native_decide/implemented_by. Per-file diagnostics pass;
independent readonly finder/skeptic source reviews PASS, no findings; final
artifact reviews retained externally. Original scopes/observations/seals and
private input provenance remain unchanged; no reserved producer edits.

This advances G42.06/BackfillB and G41 packet preparation only. G21/G41/G42.04/
G42.06/BackfillsA/B and original arbitraryself/externalworld obligations remain
partial. G40/G42.05 transferred; G42.03/P3 readonly-external-owned. Unknown-memory
ABI encoding, compiler/source/native relations, actual arbitrary call/library/
world rollback and physical resource prefixes remain unfinished. Original goal
unchanged blocked, no administration. Historical failures remain failures;
no unchanged heavy gate retry or proof/fuel/node/time/resource increase.

Coordinator-generated modules:

- `Solidity.Backend.AbiWorld.PacketPrefix`
- `Solidity.Backend.AbiWorld.PacketPrefixControls`
