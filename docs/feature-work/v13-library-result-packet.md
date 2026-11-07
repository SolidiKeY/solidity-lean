# Typed ABI observations of published library results

`Backend/AbiWorld/LibraryResultPacket` constructs actual indexed uint256+bytes
Vals and derives encoding from parts/assemble: uint word, offset64, byte length,
complete payload and padding. Marker, offset, payload and natural total-length
laws retain full words including300/max. The natural length equation is not a
nonwrapping admission theorem. No codec/decoder/runtime encoder is introduced.

The lane-local `tests/v13-help/LibraryResultConsumer.lean` imports the published
LibraryTrySource example READ ONLY above the frontend boundary. Its
expected_transport/ordered_typed/ordinary_typed consume original_outputs and
ordinary_execution, proving actual ordered four library results equal complete
indexed ABI packets, not assuming success or reimplementing library execution.
The existing separate storageEffects projection remains0,0,9,9. No new joint
output/storage same-invocation claim is inferred. Core never imports frontend.

Complete packets are [8,empty], [18,failure], [9,empty], [19,failure], with the
published ordered failure bytes102,97,105,108,117,114,101. Pure codec controls
cover300/max/empty/embeddedzero/31/32/33, wrong offset32 versus64, lowbyte44 versus
300, field/payload order and truncated-byte inequality. That last inequality is
not a classified decoder failure. None changes original profiles or observations.

Automation first exposed padding normalization; existing equations completed
the proof. Initial45s MCP timeout retained. Its cause was not isolated between
import/cache work and the draft duplicate host replay of upstream execution.
That redundant replay was removed while the actual kernel execution link stayed.
A rewrite failure was fixed by exposing the actual failure-message definition.
Later diagnostics passed under the same45s limit. Printed vectors distinguish
actual codec observations from published expected packets; kernel theorems link
the latter to actual source-world runs. No new external/native pipeline claim.

Independent read-only finder and skeptic source reviews PASS, no findings;
final artifact reviews retained externally. All prior fixtures/seals/failures
unchanged. Serial-j1/LEAN_NUM_THREADS1,12GiB/noSwap/reserve4GiB and original
proof/fuel/node/time limits unchanged. No reserved Source/World/runtime edits,
new axioms/sorry/native_decide/implemented_by or registration changes.

G21/G41/G42.04/G42.06/BackfillsA/B remain partial, including original arbitrary
self/external-world obligations. G40/G42.05 stay transferred; G42.03/P3 remains
readonly-external-owned. Uniform aggregate library compilation, runtime-memory
encoding, actual compiler/source/call-frame/world/resource relations and final
whole-lane gates remain open. Goal unchanged blocked; no administration.

Coordinator registration: `Solidity.Backend.AbiWorld.LibraryResultPacket` only.
The lane test stays above frontend and must not be imported into core.
