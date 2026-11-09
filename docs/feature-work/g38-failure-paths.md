# Source reference

Read the [source or current guidance](../../Solidity/Backend/FailurePaths).
This path is retained for links from checker-pinned reference documents.

## Storage-byte encoding exhaustion

`Backend/FailurePaths/StorageEncoderTimeout.lean` derives `IncompleteAt` and
horizon-three local ABI timeout from length-two/first-byte reads, preserving
Env, locals and complete state before allocation; no encoder outcome is assumed.
`StorageEncoderTimeoutControls.lean` seeds 17/34 by real writes in a unit with
bytes state/error; both pipelines check exact completion and horizon-five allocation.
Error parameters use memory and refuse storage, blocking identity-conversion
custom-error instantiation. No admitted compilation, code selection, resource
classification or Source-to-EVM adequacy follows from these Source observations.
