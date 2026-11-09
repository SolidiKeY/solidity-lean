# Source reference

Read the [source or current guidance](../../Solidity/Backend/FailurePaths).
This path is retained for links from checker-pinned reference documents.

## Storage-byte encoding exhaustion

`Backend/FailurePaths/StorageEncoderTimeout.lean` discharges the existing
`IncompleteAt` predicate from actual length-two and first-byte storage reads
in the same environment, locals and complete state. The local `abi.encode`
consumer derives horizon-three timeout before allocation. It takes no encoder
outcome or desired target result as a premise.

`StorageEncoderTimeoutControls.lean` declares bytes state and a bytes error
in one source unit, seeds bytes 17 and 34 through real writes, and contrasts
timeout with exact encoder completion and horizon-five local allocation for
both pipelines. Ordinary error parameters resolve to memory: the storage
signature is refused. This prevents using the storage-reference witness as an
identity-conversion custom-error caller. These are Source observations, not
admitted custom-error compilation, pipeline code selection, transaction
resource classification or Source-to-EVM adequacy.
