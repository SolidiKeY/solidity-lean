# Authenticated private census inputs

The default calculus audit loader reads the checksum manifest and exact payloads from private repository SolidiKeY/solidity-lean-coord at immutable commit 4f8722f12dae4f516332d892b025def2ca09fec9, directory evidence/solidity-h28-sol-20261104/automation-benchmark/byte-capture-inputs-v128.

Published receipt: evidence: 4f8722f12dae4f516332d892b025def2ca09fec9 evidence/solidity-h28-sol-20261104/automation-benchmark/

This packet contains the current V128 classification dataset and frozen scope payload with their checksum manifest. The exact historical V123/V124 manifests and payloads remain published at private commit bbfdd31172bf0ab028bd4967e50d63e7f8a91357, directory h145-authenticated-inputs-v125. No missing historical evidence was reconstructed. The checksum manifest is private; this document is the durable reproduction route.

Use an external checkout of the private repository, fetch the exact commit, and set SOLIDITY_COORD_EVIDENCE_REPO to its absolute directory before running the existing audit commands. Git credentials are needed only for fetching; the loader performs no network access. It reads committed objects at the pin, not mutable checkout files. Missing objects fail closed, without falling back to VM-local payload paths. Git replacement objects and inherited Git repository-selection environment variables are disabled during reads. Every payload still passes the existing size and SHA256 checks from the private manifest. Both the manifest and payload must be regular committed files: a symlink in either position is refused. Missing commits and unregistered entries fail without consulting a VM mirror.

Explicit caller-supplied manifests remain supported for genuine checker fixtures and isolated controls. They do not change the pinned default or grant proof acceptance. The public evidence/checksum manifest has been removed. Interpretation documents and actual Lean/Python checker fixtures remain.

Current census:1628 reviewed/3655 pending of5283;3806 confirmed semantic owners/1477 unresolved. Zero fresh joint witnesses. This transport repair supplies no Lean, kernel, replay, compiler-totality or performance acceptance and clears no H28 pause or STOP. Historical unavailable exact bytes remain UNVERIFIABLE.
