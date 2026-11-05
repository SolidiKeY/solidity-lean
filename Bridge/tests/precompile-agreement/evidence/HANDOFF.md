# Blocked SOL-PC checkpoint handoff

Batch: solidity-sol-20261103; task: precompile-agreement.
Repository: /workspace/solidity-lean
Branch: codex/solidity-sol-20261103/precompile-agreement
Base: b6ba0696102a7a038afe2ed333c09dff397cc5b2
Reviewed payload commit: 210fb33ec08ac6787459cdd2c692cae6c74986c7
The containing seal commit is identified by the final CLOUDVM-RESULT head;
this document cannot contain its own commit hash.

Original committed payload patch:
/workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence/original.patch
Feature/queue handoff:
/workspace/solidity-lean/docs/feature-work/precompile-agreement.md
Evidence:
/workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence
Checksums:
/workspace/solidity-lean/Bridge/tests/precompile-agreement/evidence/SHA256SUMS

Source inventory: all 18 addresses recorded and independently reviewed. Passing
source-only checker plus 12 mutation tests. Exact hashes cover core inputs,
manifest, vendor Lean closure and provenance. Vendor SHA256SUMS gate passes.
All review findings were fixed and re-reviewed without Lean/server.

Environment tooling uses the pinned compiled Cache hasher and produced 898
exact archive names, including all 20 direct Mathlib roots. It is not a proof.
Cache restore failed: 0/334 downloaded, proxy CONNECT 403. No Mathlib rebuild,
repin or network bypass. Q-CACHE options: supply coordinator xfer-mathlib-ae
artifacts with checksums, or restore supported access to the pinned Azure cache.

KeySort source elaboration (-j1) passed; existing solkeycheck executable reported
377 parsed taclets and all 131 read-bearing annotations matched. This does not
substitute for a fresh full ./run-lean.sh --bridge final build. Actual versions
are Lean 4.24.0 and Lake 5.0.0-src+797c613. No RUNTIME_GATE_PASS.

Unfinished obligations: arbitrary-length IDENTITY exact vendor output/charged gas
and branch boundary; all common algebraic gas and header/rounding proofs;
inhabited/malformed/insufficient-gas EVM fixtures; theorem/fixture mapping;
explicit axiom pins, kernel/trust gates, full final build, final proof milestone
finder/skeptic reviews and final complete handoff. No task proof was added or
claimed. Every inventory proof mapping is explicitly empty/pending. Default
acceptance exits 1 until these obligations are implemented and checked.

Source mismatches remain openly recorded: MODEXP fork gas/bounds, BLAKE2F short
header padding, opaque/subprocess output boundaries, unsupported BLS/P256.
No extra crypto premise, exclusion, statement weakening, vendor change, Source
edit, maxHeartbeats increase or central registry/root change. No G47/full B16/G51
claim. No push/merge/PR. Existing goal retained; get_goal is unavailable.

Reproduction commands and decisive outputs are in the feature doc and evidence
logs. After pinned cache transfer, resume the same branch/goal and return to the
proof queue. Central registration is deferred per H21, not silently edited here.

SHA256SUMS binds the reviewed payload files, original.patch and this handoff.
The manifest excludes itself. Verify from repository root with:
sha256sum --check Bridge/tests/precompile-agreement/evidence/SHA256SUMS
