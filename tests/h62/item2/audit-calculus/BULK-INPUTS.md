# Authenticated private census inputs

The default calculus audit loader reads the checksum manifest and exact payloads from private repository SolidiKeY/solidity-lean-coord at immutable commit 74956e3ca554128d499fcd4b921ea67c7634ad17, directory evidence/solidity-h28-sol-20261104/automation-benchmark/evm-try-owner-inputs-v135.

Published receipt: evidence: 74956e3ca554128d499fcd4b921ea67c7634ad17 evidence/solidity-h28-sol-20261104/automation-benchmark/

This packet contains the current V135 classification/ownership dataset and frozen scope payload with their checksum manifest. The exact historical V123/V124 manifests and payloads remain published at private commit bbfdd31172bf0ab028bd4967e50d63e7f8a91357, directory h145-authenticated-inputs-v125. No missing historical evidence was reconstructed. The checksum manifest is private; this document is the durable reproduction route.

Use an external checkout of the private repository, fetch the exact commit, and set SOLIDITY_COORD_EVIDENCE_REPO to its absolute directory before running the existing audit commands. Git credentials are needed only for fetching; the loader performs no network access. It reads committed objects at the pin, not mutable checkout files. Missing objects fail closed, without falling back to VM-local payload paths. Git replacement objects and inherited Git repository-selection environment variables are disabled during reads. Every payload still passes the existing size and SHA256 checks from the private manifest. Both the manifest and payload must be regular committed files: a symlink in either position is refused. Missing commits and unregistered entries fail without consulting a VM mirror.

Explicit caller-supplied manifests remain supported for genuine checker fixtures and isolated controls. They do not change the pinned default or grant proof acceptance. The public evidence/checksum manifest has been removed. Interpretation documents and actual Lean/Python checker fixtures remain.

Current census:1672 reviewed/3611 pending of5283;3884 confirmed semantic owners/1399 unresolved. Zero fresh joint witnesses. This transport repair supplies no Lean, kernel, replay, compiler-totality or performance acceptance and clears no H28 pause or STOP. Historical unavailable exact bytes remain UNVERIFIABLE.

For exact historical V127/V128 reproduction and actual old-to-new preservation checks without private HTTPS access, use tests/h62/item2/audit-calculus/PACKET-VERIFICATION.md. This route leaves the current default pin unchanged.
