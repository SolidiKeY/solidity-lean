# Moved lane: mutation-testing (from a Codex VM)

The user decided (2026-11-05) to move idle Codex lanes to Claude VMs: this lane
(H28 mutation testing) finishes on a Claude VM with the same scope. The Codex
goal was paused (waiting.md: "must not be resumed for cache delivery"). None of
the lane is on master yet. Its head d24101bb sits on 9863cd532, over delivery
base 32dd5befc. The 70-file lane diff matches the Codex VM checkout, which only
added automatic master-sync merges (VM head 96ed396b5). **Start from
origin/cloud/mutation-testing-move (e25db89bbf30d9213e7b121a23eccccbd844d376)**,
merging current origin/master (aec9adf1ad8666a7e591e42a537069a93dc858cb at move
time) into it. Push to your session branch only.

The rescue branch is d24101bb plus one WIP commit. That commit adds the 15
top-level draft JSONs that the lane `.gitignore` excludes (`/*.json`). Each is
byte-identical to its H44 bulk-index entry:
- `inventory.draft.json`, `inventory.extended.draft.json`,
  `inventory.extended.errata.json`
- `{alias,bounds,callback,division,guard,overflow,payment,pop-delete,push,push-order}-cases.draft.json`
- `bounds-default-schema-invalid.draft.json`, `overflow-schema-invalid.draft.json`

The VM stashes 0/1 ("h28 alias WIP") hold older alias oracles. The committed
versions supersede them, so they were not rescued.

## Caveat: bulk-bound tooling
`verify_bulk.py` and the bulk-input lookup authenticate off-git inputs (H44)
against absolute `/workspace/...` paths. They will fail on a Claude VM. Before
any runner work, regenerate the inputs from committed sources, or re-freeze the
manifest with paths relative to the repository and fresh sha256 values. Do not
fake the old digests.

## Remaining queue
1. Make the tooling self-contained (caveat above).
2. Inventory: 215 constructor rows. Finish the clause/operator-instance
   dispositions in the 9 families and freeze the exhaustive manifest.
3. Runner: the guard, overflow, division, bounds, pop-delete, push, alias,
   payment and callback pilots pass at 1/1 with `scope_complete=false`. Extend
   them to the full family scope.
4. Semantic witnesses for the remaining families. The callback pilot targets the
   shared `Taclet`, not the separate `CallbackTaclet` table. Cover that table or
   record why it is excluded.
5. A combined whole-manifest run with the score denominator, the full acceptor,
   final repository gates, reviews, and the seal in
   `docs/feature-work/h28-mutation-testing.md`.
6. Backfill: negative controls.

## Bulk evidence (stays on the Codex VM)
These stay on Codex env `ccarenv_b64_Y2NhcmVudl9kNDdjMzE2OTgwN2M4MTkxYjdlZTEzOTdkMWI5ZGRkNQ`:
- the H44 bulk archive `/workspace/h28-h44-bulk-be546c1dc/bulk-data.tar.gz`
  (885301 bytes, sha256 4a1eb27e2142d7464b9c705350f7ef803c2db4aceea474bf0e902eb0773e73e5)
- the cache packs `/workspace/h28-callback-cache-export-v2/normal-callback-cache.tar.gz`
  and `/workspace/h28-callback-export-9863cd53/proof-worlds.tar.gz`
- the handoff `/workspace/h28-h44-handoff-d24101bb`, and the validation
  `/workspace/h28-h44-validation-9863cd53`
- the in-tree ignored `tests/h28-sol/mutation-testing/evidence/` (997 files, about 9 MB)

Claude VMs cannot reach any of this. Re-run validation fresh instead of citing
the old seals or caches.

## Interfaces and owners
- Exclusive writes: `tests/h28-sol/mutation-testing/**`,
  `docs/feature-work/h28-mutation-testing.md`.
- Read-only: `Calculus/Rules.lean`, `Calculus/RuleShapes.lean`,
  `TestSuite/Refuted.lean`, `tests/upstream/README.md`. Apply mutants only in
  scratch copies, never to the shared calculus files.
- Shared roots and registries (H21) are coordinator-owned.

## Gates
- Lean MCP diagnostics clean (severity=error) on every touched Lean file.
- `./run-lean.sh` on the final head, plus `bash scripts/coord-tools/register.sh --check`,
  `node scripts/check-orphans.mjs` and the doc-path check, with no new findings.
- Separate read-only finder and skeptic reviews per area, neither using the Lean
  server. Fix confirmed findings and record them in the lane doc.

## Exclusions
No sorry/axioms or `maxHeartbeats` changes, and no theorem, premise, exclusion
or budget weakening. Use no Codex tooling (`ship-cache.sh`, `runtime-bin/`, Docker
caps, posting to the `codex/*` branch). Never push to master or force-push.

## Original assignment (Codex prompt; replace Codex-specific tooling with the preamble's rules)

You are the Codex Cloud worker for batch "solidity-h28-sol-20261104", task "mutation-testing": Semantic rule mutation testing with checked kill witnesses.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-h28-sol-20261104/mutation-testing` from that exact commit;
  verify its ancestry before continuing an existing branch. An environment may
  contain an older clean checkout: fetch the intended remote branch and exact
  published base, verify remote ancestry, then create your assigned branch at
  that base without resetting/discarding anything. Preserve unexpected local
  work in an owned worktree if needed. A missing local commit or branch alone
  is recoverable setup, not a reason to stop the persistent goal. Report a real
  mismatch if safe setup or remote ancestry cannot be established.
  Commit reviewable checkpoints on this branch. Do not push, merge into the
  default branch, open a PR or expand scope without separate human authorization.
  The coordinator retrieves committed artifacts from this same VM.
- Follow AGENTS.md and available repository skills. Personal skills on the
  coordinator's computer are not automatically available here. Discover the
  actual tools, checkout path, toolchain versions and VM resources; do not
  assume Claude's environment, PATH, permissions, MCP names or memory limits.
  For Solidity-Lean use per-file Lean MCP diagnostics when available, obey
  repository build policy for final gates, and report actual Lean/Lake versions
  and passing KeySort output before RUNTIME_GATE_PASS. Keep heavy work serial,
  Lean -j1 with bounded memory/no swap and OS headroom, and preserve proof budgets.
  Respect writer locks wherever another writer may exist, including on this VM.
- Complete the original assignment's implementation, proofs, checks, required
  finder/skeptic reviews and handoff. For a Work queue, finish each checkpoint
  with its gates, reviews and committed handoff section, then take the next.
  Use only explicitly assigned backfill when a dependency blocks a checkpoint;
  return to the blocked item when possible. A checkpoint or elapsed-time estimate
  does not complete the whole queue. Report unfinished obligations accurately.
- The launcher already created a persistent goal for the entire assignment.
  Inspect it with get_goal; never create a second goal, reset it, or schedule a
  competing continuation. The active goal owns continuation between turns. Do
  not mark it complete with work or required validation left. Honor user pauses
  and runtime limits. If a real scope decision is required, report it and follow
  the goal tool's blocking rules; never weaken a theorem, exclusion or premise.
  Warn before a refactor that may slow checking, as repository instructions require.
- Record scope questions as self-contained questions with short stable IDs,
  source tags and 2-3 mutually exclusive options describing their consequences.
  Recommend an option only with evidence; never recommend approving an exclusion
  or premise. Questions and requests for explanations do not grant authorization.
- Prepare absolute VM paths for the original patch, handoff, evidence directory
  or archive and checksum manifest. Record the full committed head, base and
  actual repository path. Include each gate's command, outcome and decisive
  output, plus proof versus external-test boundaries and outstanding work.

End a result or scope-question turn with one JSON report between these markers
(use actual values; a complete goal or this report alone never proves success):

CLOUDVM-RESULT
{
  "batch": "solidity-h28-sol-20261104", "slug": "mutation-testing", "status": "done | partial | blocked",
  "branch": "codex/solidity-h28-sol-20261104/mutation-testing", "base": "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5", "head": "<full committed SHA>",
  "repository": "<absolute VM checkout>",
  "checkpoints": [{"name": "<checkpoint>", "status": "done | partial | blocked"}],
  "gates": [{"command": "<command>", "status": "pass | fail | pending", "evidence": "<output/path>"}],
  "reviews": "<required finder/skeptic results and evidence>",
  "limitations": "<unfinished or unproved work, or none>",
  "questions": [{"id": "Q1", "sources": ["<checkpoint>"], "question": "<standalone question>", "options": ["<choice: consequence>", "<choice: consequence>"]}],
  "artifacts": {"original_patch": "<absolute path>", "handoff": "<absolute path>", "evidence": "<absolute path>", "checksums": "<absolute path>"}
}
END-CLOUDVM-RESULT

Use questions=[] when none. A blocked task may have no committed changes yet;
report missing head/artifacts as null rather than inventing them. The continuous
listener observes saved task/goal transitions and wakes the existing auditor.
It never submits another turn to your active goal.

Assignment:

Coordinator message (2026-11-02). A Claude Code session is now the coordinator of all cloudvm batches; the Codex listener/auditor is retired. Human decisions are recorded verbatim in the coordinator decisions file (H1-H8); the ones relevant to you are quoted below and are authorizations from the human, scoped as stated. Original assignment, semantics, observations, proof budgets and final gates are otherwise unchanged. Keep working in this same VM/branch; do not create or reset a goal. End every turn with a CLOUDVM-RESULT (questions=[] if none); never end a turn with an empty answer.

H28-MUTATION-TESTING: Semantic rule mutation testing with checked kill witnesses
Pinned base: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5
Exclusive writes: tests/h28-sol/mutation-testing/tools/**; tests/h28-sol/mutation-testing/**; docs/feature-work/h28-mutation-testing.md
Read-only inputs: Solidity/Calculus/Rules.lean; Solidity/Calculus/RuleShapes.lean; Solidity/TestSuite/Refuted.lean; tests/upstream/README.md

H28 is approved; finish the frozen queue, aiming 8–10 hours of useful work without padding. Inputs are pinned published master, immutable. Use attached executor and assigned branch in your own VM; local worktrees under ~/projects/solidity-lean-worktrees when needed. Follow AGENTS.md, docs/module-map.md, docs/README.md and matching conventions; read intrinsic.md Gate G0. No H16/H19/H25 Source edits, no frozen H22 Core ExtCall, no producer-owned implementations, H21 roots/module maps/shared registries/trust inventories, frozen upstream baseline, or another lane's files. New modules have a local registration manifest for central integration; no generated root changes. Core stays dependency-free and intrinsic.
Never weaken theorem statements, premises, exclusions, refusals, observations or budgets; no new axiom/sorry/admit/unsafe/native_decide trust shortcut, no maxHeartbeats raise. No producer-interface changes without reporting ESCALATE with 2–3 options. No push/merge. Do not claim whole compiler correctness from restricted or conditional lemmas. Check git log for speed-motivated changes before refactoring; warn before any potentially slower refactor. Measure matched before/after for speed changes, stop and retain evidence for any >10% slowdown.
Lean work serial LEAN_NUM_THREADS=1 and -j1, one heavy check at a time, <=12 GiB/no swap and H1 4 GiB VM headroom. Discover actual cgroup/runtime, use an existing bounded scope/container if present; do not assume host scope settings apply to a new VM. Prefer Lean MCP diagnostics and scripts/coord-tools/lean-mcp; no blocked bare lake/lean invocation. Record actual Lean/Lake versions and a passing permitted KeySort gate before RUNTIME_GATE_PASS. Use coord toolkit gate/seal/handoff where available. If an unavailable get_goal tool is the only problem, keep working under the existing frozen persistent objective; do not create/reset goals or launch another VM.
Every checkpoint needs actual implementation/proofs/tests, source identities and exact commands/exits/timing/RSS. Separate read-only finder and skeptic per area, neither using Lean server; fix confirmed findings. Acceptance must enumerate all assigned constructors/clauses/files/fixtures, no sample-only inventory, empty/False relation or mocked successful proof. Use inhabited positive and negative controls and universal proofs where requested; timeouts/errors/open obligations stay explicit. Commit short checkpoint messages, one coherent item per commit; keep immutable evidence, bundle/patch/hashes, base/head/branch, theorem signatures/axioms, review verdicts and full queue accounting. End each turn CLOUDVM-RESULT JSON with questions=[] when none. Never emit empty status-only turns. Backfill only inside exclusive scope; an incomplete checkpoint is not whole-goal completion.


## Work queue
1. Inventory mutation candidates and proof/semantic oracles for overflow, division/minimum, index bounds, push dirty tail/length ordering, pop/delete, alias capture once, guard polarity, rollback/payment and callback frames. Freeze target hashes and exhaustive candidate manifest; production inputs read-only.
2. Implement disposable-tree mutation runner with exact mutant IDs and one-change diffs. Distinguish invalid compilation, timeout/error, killed, equivalent and surviving cases; never score unrun cases. Include normal baseline and independent known-kill controls.
3. Build real semantic witnesses/Lean proof-oracle checks for each selected family; require source-to-mutant attribution and inhabited inputs. Surviving non-equivalent mutants need concrete regression witnesses; no expected-failure relabeling. Keep existing budgets and trust boundaries.
4. Run whole declared manifest, retain per-mutant commands/exits/timings/hash and score denominator, scope-complete acceptance plus self-tests for runner false passes, independent reviews and final sealed evidence.

## Backfill queue
Add further negative controls within the same manifest families, not production theorem repairs.
