# Error readback dependency restoration

The helper branch omitted `Backend/AbiWorld/ErrorLayout.lean` and
`Backend/AbiWorld/ErrorRoundtrip.lean`, leaving the existing
`Lowering/V08/LiteralFailureBytesReadback` and its controls without a dependency.
Both modules are restored byte-for-byte from the original owned checkout at
`85d13e5c7db386fd832391be5f7d04970ad31f22`; their last source commit is
`53fedb6574fc26694e268aad96d728744f854b9e`. This reuses prior proofs rather than
introducing a second codec or changing published semantics.

`error_roundtrip` retains the necessary `bs.length < 256^32` premise.
`LiteralFailureBytesReadback.lowered_packet` derives it from actual packet
`Fits`, relates the Source packet to indexed `AbiEntry.Vals [.bytes]`, consumes
actual constant-packet `Failure.Slice.checkedRun`, and decodes the bytes read
from the reached slice memory. Its populated controls cover empty, zero, 255,
mixed, and 31/32/33-byte messages, unpadded acceptance, truncated header/payload,
wrong selector/kind/order and preservation of an older byte. Source and Slice
states are distinct machines. This is not an unknown-memory encoder, fetched
EVM agreement, caller catch execution, or world rollback theorem.

Per-file diagnostics passed for both restored modules and both consumers.
The RAM reading before the second diagnostic was below the required 4 GiB
reserve; that diagnostic was incorrectly allowed to proceed. Its Lean pass
is retained separately from this admission failure. The service was stopped,
clean cache pages released without deleting files, and later launches used
an enforced prelaunch reserve check. No proof or resource cap was raised.

Read-only source finder and skeptic reviews are recorded with this checkpoint's
external evidence. Full G21, G40, G41, G42.01-.02, G42.04, G42.06 and both
backfills remain partial. G42.03 is readonly-external's responsibility;
G42.05 remains dependent. Unknown-memory ABI encoding, all-profile runtime
dispatch, same-invocation/raw-return linkage, arbitrary call/world/resource
composition and mandatory whole-lane validation remain open. Historical failed
Suite/full/cold/docs/frozen-comparison gates remain failures; no unchanged
heavy gate was retried. The persistent goal remains unchanged.

New modules for coordinator-generated registration:

- `Solidity.Backend.AbiWorld.ErrorLayout`
- `Solidity.Backend.AbiWorld.ErrorRoundtrip`

Existing consumer modules to register with this closure:

- `Solidity.Lowering.V08.LiteralFailureBytesReadback`
- `Solidity.Lowering.V08.LiteralFailureBytesReadbackControls`
