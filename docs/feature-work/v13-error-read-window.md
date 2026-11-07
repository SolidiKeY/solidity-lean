# Complete Error payload windows

`Backend/AbiWorld/ErrorReadWindow.lean` consumes the existing `decodeError`,
`encodeError`, word readback and terminal Slice proofs. `unpadded` proves the
actual decoder accepts the full declared reason with arbitrary trailing bytes;
`source_prefix` projects the unpadded window from the existing encoder;
`prefix_readback` composes them. The word-length representability premise is
explicit. These sufficient packet laws change no decoder/profile/admission.

`emitted` derives that premise from actual whole-packet `Fits` and proves
constant custom-packet emission with arbitrary instruction suffix, full exact
REVERT bytes, reached memory readback and the decoded reason. Ignored trailing
bytes are still part of the REVERT payload. This does not compile Source reason
reverts to different bytes, execute caller catch clauses, read unknown runtime
memory or establish native/source/world correspondence.

Controls use a nonempty stack and older memory byte, seven messages including
empty/zero/255/mixed and31/32/33 boundaries, dirty padding, header/payload
truncation, wrong selector/kind and differing full packets. A suffix supplying a
missing payload byte decodes a changed reason: completeness is essential.
Complete packet and reached-readback vectors, decoded values and explicit
success flags are exported. No prior observation or expected result changes.

Automation-first initially failed on the generic take/drop goal. Explicit
window and existing word-read equations completed it. A redundant tactic and a
missing explicit RevertData import failed subsequent diagnostics and were fixed;
raw failures remain. The first shell reserve guard lacked `set -e`, permitting
a check below the required4GiB reserve. That admission failure remains FAIL.
Service stopped, clean cache pages reclaimed without deletion, subsequent
launches use a fail-closed guard. Cap12GiB/no-swap and proof/time limits unchanged.

Independent read-only finder and skeptic source/artifact reviews are retained
externally. Finder noted `getD []` output alone is ambiguous for the empty
message; an explicit isSome row was added and kernel `populated` proves success
for every listed packet. No semantic finding or expectation change.

G21/G40/G41/G42.01-.02/G42.04/G42.06 and BackfillsA/B remain partial. G42.03/P3
belongs to readonly-external; G42.05 depends on full producer closure. Unknown-
memory encoding, all-profile decoder/dispatch, raw-return/static execution
linkage, arbitrary call/library/world/resource composition and final whole-lane
gates remain open. Historical mandatory failures remain failures, not rerun.
Goal remains unchanged blocked; no registration edited. New coordinator modules:

- `Solidity.Backend.AbiWorld.ErrorReadWindow`
- `Solidity.Backend.AbiWorld.ErrorReadWindowControls`
