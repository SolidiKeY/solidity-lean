# Error offset windows

New owned `ErrorOffsetWindow.gap_readback` proves the actual published
`Semantics.decodeError` consumes its body-relative offset32+gap.length, skips
arbitrary gap bytes, reads a full length word and returns the complete reason.
Offset and length must each be representable in32bytes; neither natural offset
nor total packet size is silently identified with a modulo word. This is a
sufficient packet equation, not a new admitted profile or canonicality rule.

`zero_offset` proves existing overlapping offset/empty-length behavior for any
suffix. It does not claim canonical encoding. `emitted` derives both word bounds
from actual whole-packet `Fits`, then consumes real constant-packet terminal
emission, exact full REVERT bytes and reached Slice memory readback. Gap and
suffix bytes remain observable in the packet even when ignored by the decoder.
No desired decoder/run premise, caller catch phase, Source agreement or runtime
memory-reading encoder is assumed.

Controls reuse the existing populated two-word-stack/memory fixture across42
combinations of seven empty/zero/255/mixed/31/32/33-byte reasons and six gaps.
Actual offsets32/33/35/63/64/65 include unaligned windows. Changed gap bytes keep
the decoded reason but change the full packet. Wrong offsets, truncated headers,
lengths and payloads, zero-offset/stale-reason, reordered payload, older-byte and
exact-capacity/one-past controls preserve distinctions between actual decoder
failure, accepted aliasing and architectural Fits conditions. Complete vectors
and explicit successful-decoding flags are exported, not sampled.

Standard automation first failed on the generic goal; explicit existing
append/drop/word-read laws completed it. Per-file diagnostics passed with no
budget increase. Independent read-only source finder and skeptic PASS, no
findings. Final artifact reviews are retained externally. All prior source and
observations preserved; no producer/Source/Failure semantic edit.

The isolated helper rebased without conflict onto published24149fd5; the prior
sealed2dff36ae head is preserved in refs/task-backups/v13/pre-24149-2dff. Existing
sealed artifacts were not rewritten. G40 and G42.05 remain transferred; no work
on those items. This is G41/BackfillA. G21, G41, G42.04, G42.06 and BackfillsA/B
remain partial; original arbitrary self/external/world obligations remain open.
Unknown-runtime encoders, actual same-invocation/static execution linkage,
compiler/native/world/library/resource composition and final mandatory gates
remain unresolved. Historical failed gates remain failed; no unchanged heavy
retry or goal administration. New modules for coordinator-generated registration:

- `Solidity.Backend.AbiWorld.ErrorOffsetWindow`
- `Solidity.Backend.AbiWorld.ErrorOffsetWindowControls`
