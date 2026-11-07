# DEP-MIGRATION-001 — unchanged import closure fails on pinned Lean

Recipient: coordinator relay to Hash.CollisionBound producer/migration owner (owner not resolved by V07 area snapshot).
No relay.sh is available in this checkout; this saved ticket is for coordinator retrieval, not a delivered message.

Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4
File: Solidity/Hash/CollisionBound.lean (read only)
SHA256: 49e8b756f01c78c6e850401ba29ac4e65b71ce3d091a2ccee02e2291a6d9e7ce
Path: AcceptedGraphProducer -> P8Bindings -> P8.FrozenInterface -> Roadmap.Contracts -> Hash.CollisionBound.
Pinned Lean 4.35.0 fails: countP_contains_le line 407 unsolved equality; omega at 660 and 680; axiom-message guards at 950,953,956,959,962,968 fail. This is a migration failure, not evidence that a frozen V07 statement is vacuous.
Reproduce with the check-imports.py command in the handoff. See import-check/results.json and Solidity.Hash.CollisionBound.log off git.

Q-MIG-001 [sources: checkpoint 2/3/4, DEP-MIGRATION-001]: How should this lane obtain a statement-preserving dependency repair for the official pinned toolchain?
Options: (A) producer/migration owner supplies a reviewed isolated overlay plus exact commit and validation; this lane validates it without editing the original; (B) retain the dependency blocker until the coordinator provides the repaired integration base/overlay, keeping the original pinned base and all audit obligations recorded.
No alternative toolchain, weakened statement or new premise is requested.

H82 retirement disposition: withdraw any proof-only exact-file agreement requirement under the standing human authorization. Retain DEP-MIGRATION-001 as the actual migration/acceptance dependency. No Hash edit was made before the explicit stop-and-handoff; successor owns integration.
