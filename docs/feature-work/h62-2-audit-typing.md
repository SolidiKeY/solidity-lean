# H62 item 2: typing/frontend empty-statement audit

Status: partial; none of the four checkpoints is complete. Persistent goal remains unfinished.
Owner: solidity-h62-2-20261106/audit-typing.
Branch: codex/solidity-h62-2-20261106/audit-typing.
Frozen base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
Repository: /workspace/solidity-lean.

## Saved source backfill

The deterministic generator is `scripts/h62/item2/audit-typing/source_census.py`.
Run from this checkout:

```
python3 scripts/h62/item2/audit-typing/source_census.py --output /workspace/h62-audit-typing-evidence/source-census.json
```

It reads frozen Git objects, expands every code-first Lean module row in the typing/frontend maps, deduplicates paths, and preserves exact complete source including section variables. Bulk JSON stays off Git. Current output: 309 unique modules, 3207 lexical candidates, zero unmatched patterns. These counts are NOT verified interface statement counts. Comments/strings may create candidates; macros may be missed. Fully qualified names, elaborated signatures, owner resolution, classification of global versus per-input hypotheses and all simultaneous witnesses remain unresolved. No declaration has been certified or excluded.

## Setup and checks

Initial checkout was clean `work` at 6cf853aea0417155aca29ddb91f1767d3f3a3cc4. Exact base absent locally. `git fetch origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4` exited 0. `git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master` exited 0. Assigned branch created at exact base under writer lock; existing clean branch preserved. No push/merge/PR.

All five coordinator input hashes matched `/workspace/h62-coordinator-inputs/sha256.json`. Downloaded the official pinned v4.35.0 Linux archive into off-Git evidence. SHA256: 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.

Actual binaries: `/workspace/h62-audit-typing-tools/lean-4.35.0-linux/bin/`.
Lean: 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release.
Lake: 5.0.0-src+eb6cafb (Lean 4.35.0).
Tracked lean-toolchain remains unchanged; no v4.24 cache was used.

KeySort command: `LEAN_NUM_THREADS=1 /workspace/h62-audit-typing-tools/lean-4.35.0-linux/bin/lean -j1 --memory=11000 --tstack=131072 Solidity/KeySort.lean` under writer lock, Python 120-second timeout. Exit 0, empty diagnostics, 1.416963547 seconds, peak RSS 507048 KiB. Evidence: `/workspace/h62-audit-typing-evidence/keysort-result.json`. Initial timing wrapper failed before running Lean because `/usr/bin/time` is absent; recorded in keysort.log and superseded by the successful Python-timed run.

VM: cgroup memory.max 17179869184 bytes; no active swap; approximately 16 GiB initially available. No systemd-run, no concurrent heavy Lean processes, no raised proof budgets. Runtime prerequisite only: no full RUNTIME_GATE_PASS or proof audit pass is claimed.

Generator run twice; `cmp` exited 0. `git diff --check` passed. No Lean sources or frozen statements edited; new axioms/sorry/native_decide: 0. No before/after proof timing comparison exists because no proof refactor was made.

## Independent reviews

Finder and skeptic agents reviewed read-only, neither using a Lean server or running Lean. Both verified every retained source and SHA256 against frozen Git objects, unique paths, all 21 typing and 264 frontend map rows, and the preliminary-only disclaimers. Neither found a material issue. Finder flagged unused import and wildcard crossing directory boundaries; removed import and constrained wildcard matching per path segment. Regeneration retained the same 309/3207 counts and was byte-identical across two runs. No claim of reviewing the unfinished proof audit is made.

## Remaining checkpoints and continuation

1. Inventory: exact elaborated frozen signatures and live producer owners for EVERY interface theorem with hypotheses. Source candidates are only backfill.
2. Witnesses: simultaneous inhabitant of every complete hypothesis bundle, importing unchanged interfaces. No witnesses yet.
3. Success: supported-program totality/success and negative reject-all/always-revert controls, observable failure/gas/fork boundaries. None yet.
4. Fidelity: reconcile every statement exactly once and report uncovered theorem/owner pairs. None yet.

Next: use verified official binary and an isolated output/cache configuration to elaborate imports for a Lean environment-based declaration census. Reconcile it with frozen source candidates and resolve owner mapping; do not claim regex as signature fidelity. Maintain the 4 GiB reserve and serial bounded checks. Existing-file edits outside owned paths remain forbidden; owner registration fragments and tickets go through coordinator. No frozen theorem weakness has been established, so no theorem ESCALATE lines or repair premises have been invented.

No get_goal tool is exposed; coordinator explicitly confirmed this is not a blocker. No goal was created/reset/stopped. This is one preparatory backfill item, not a completed checkpoint; fresh-thread threshold has not been reached. Full affected validation, acceptance, census/witness audits, totality proofs and final finder/skeptic milestone reviews remain pending.
