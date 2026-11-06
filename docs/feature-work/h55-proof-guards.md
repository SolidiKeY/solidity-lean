# H55 proof guards: preliminary inventory

Status: partial. The coordinator's lease correction makes the listed source files inputs only until current owners transfer exact paths. No source migration is included. The three queue items and scope-complete acceptance remain outstanding.

`scripts/h55/proof-guards/census.py` emits a preliminary, single-line lexical inventory of tracked Lean files, with line text, file SHA-256, HEAD, and tracked working-tree status. At base 4d3790eadb8a5212233bc7d5e345817476b2f590 it found 637 matching lines in 197 files. This is not a count of no-op guards: it misses multiline guards, counts lines rather than occurrences, and can include comments, strings, nonterminal skips and effective closers. Do not use it to justify deletion. Full census, semantic classification, ownership routing, mechanical patches and real Lean checks are pending.

Evidence stored off Git in `/workspace/h55-proof-guards-evidence/` per bulk policy:

- `census.json` SHA-256 `75e6808b0e00f576476aaa35cd21ce33c2af6109d3d63549067f093d629d12b8`.
- `keysort.log` SHA-256 `81b5374a30d80c662ee32d4fccc441cad7c0007ece79b355153828ffdc4e7f3a`: `LEAN_NUM_THREADS=1 lean -j1 Solidity/KeySort.lean` passed, 1.881 seconds wall. Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b); Lake 5.0.0-src+797c613. This is a prerequisite only, not an affected-module proof or runtime gate.

Independent finder and skeptic reviews were read-only and used no Lean server. Both found the lexical coverage limits above and noted that HEAD alone does not describe dirty source files; the script now records tracked status as well as per-file hashes. No candidate was proven safe to remove. Python syntax compilation passed. Speed history inspected includes fcd5ba31b and 2ff6a0f3e; no before/after migration measurement has been made.

The first creation of the standalone census script occurred before acquiring the required writer lock; subsequent modification, checking and commit use the lock. No existing source was edited. Future writes and Lean checks must acquire the lock first.

## Exact-form candidate export

The standalone `candidate_patches.py` exports two exact, standalone line spellings: 319 `first | (simp only;done) | decide | omega | rfl | skip` and two with `(decide)`. They occur in 109 files (20 under `Solidity/Yul/Adapters`, 89 under `Solidity/Yul/Views`), none in the listed input paths. The numeric match to 321 does not establish that this is the complete intended set, nor that any closer is ineffective. Other forms, multiline tactics, comments and strings require separate analysis. These patches are **unverified review candidates**, not validated owner-ready deliveries. Current owner and accepted handoff must be established before routing or application; no owner has been assumed.

The export is `/workspace/h55-proof-guards-evidence/candidate-patches-v2/`; manifest SHA-256 `f4baf9dd16bf79f6b16fe1cfc9cf1d6aa7b3e58f3e2ba4a4d0e9e26c34244dbb`. It records per-file source and patch hashes and the generator hash. All 109 individual patches passed `git apply --check`, and synthetic tests checked both forms and preservation of a different form. These are text checks, not Lean proof checks. No original source file was changed.

Independent read-only finder and skeptic reviews used no Lean server. They verified the counts and applicability and warned that equality with 321 proves neither scope nor no-op status. They identified that the first manifest omitted the untracked generator's identity; the regenerated manifest records its SHA-256. Full repository classification, real proof checks, matching owner transfers and delivery, speed comparisons and complete acceptance remain pending.

## Retirement handoff (H82)

H82 retirement directs stop after preserving the smallest safe checkpoint; successor is `solidity-h62-2-20261106/audit-readonly-calls`. H82 standing authorization permits statement-preserving proof changes without exact-file owner agreements, subject to the stated owner and frozen-interface exceptions. The original queue is not complete:

1. Full repository census, classify every original first/skip guard, prove no effective closer is removed, make and land required patches, route remaining work as appropriate, and check all affected modules. The 321 exact-form candidates and their patches are unverified; their equality in count does not establish their identity with the assignment.
2. Parameterise near-copy packet/control files in scope with exact case correspondence and complete acceptance.
3. Share Evm/Backend lemma/HeapRepr/AllocatorRepr fixtures in scope, accounting for every original lemma and observation.
4. Backfill safe helper reuse within scope when blocked; complete proof, correspondence, axiom, resource, speed and acceptance gates; independent finder and skeptic reviews and fixes; commit, export and handoff. Three queue items then fresh thread. H58 HOLD and the theorem, premise, exclusion, observation, budget, intrinsic core and H44 restrictions remain binding.

The proof baseline dependency build for `Solidity.Yul.Adapters.RawPhysicalCalldata:deps` was terminated for retirement, exit 143, after 76 reported build/fetch steps. It is not a passing gate. No Lean source was edited, and no after timing exists. The temporary Lake config and build log are retained under `/workspace/h55-proof-guards-evidence/`. KeySort previously passed as described above. No additional proof or external-test gate passed. The partially built `.lake` tree is retained in this worktree; an off-Git pack is included in the evidence handoff. No source patch was applied and no push was performed; H71 push permission was not provided here, and the original assignment prohibited pushing without separate authorization.

The full original rendered prompt and its exact scope manifest were not found as files in this VM. The assignment was available in the original conversation, but this runtime exposes no tool to export the original thread or verify an exact reproduction against its stated SHA-256 `9f05c52ab2b62fe0122767bc8affe191f39942f28074e8d181aeee5ab1444b78`. Do not treat the preliminary inventory or the 109 Yul patch candidates as the original scope manifest. The successor must obtain the exact prompt and manifest from the coordinator before relying on scope. The goal tool available here has only complete/blocked outcomes and cannot set PAUSED; the goal was already marked blocked in an earlier turn. No new goal was created or reset. Automatic implementation continuation is not authorized after this handoff.
