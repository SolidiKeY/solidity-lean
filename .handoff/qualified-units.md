# Moved lane: qualified-units (from a Codex VM)

The user decided (2026-11-05) to move idle Codex lanes to Claude VMs: this lane
(SOL-QN qualified-unit resolution, G12) finishes on a Claude VM with the same
scope. All lane code is on master, and all 24 `Solidity/Frontend/QualifiedUnits/**`
modules are registered. The lane head f94495e38 is 260441fd8 plus the H44 manifest
`tests/sol-qualified-units/bulk-evidence-H44.json` (1626 lines). That commit was
unpushed on the VM. It is now pushed as-is, with no WIP commit. **Start from
origin/cloud/qualified-units-move (f94495e383cee408aaf2d329b65fd75e1f4da735)**,
merging current origin/master (aec9adf1ad8666a7e591e42a537069a93dc858cb at move
time) into it. Push to your session branch only.

## Remaining queue
(From the lane doc table, `docs/feature-work/qualified-unit-resolution.md`.)
1. The final target relation, including inherited-overload behavior.
2. An independent C3/bound: hierarchy existence and precedence, and the
   `idUniverse` bound. Also normalization adequacy.
3. Full target completeness.
4. Supported-type adequacy.
5. Full library, `./run-lean.sh` and corpus gates. The last full checkpoint on
   the Codex VM was killed (exit 137) by the H1 memory-reserve guard. That was a
   resource stop, not a proof failure.
6. check-trust: two `References.lean` sites. The trust inventory now has entries
   near lines 1388/1393. Re-check that they are covered.
7. The 12 central registration proposals listed as pending. All 24 modules are
   now registered, so verify this and close them in the doc.
8. Final acceptance, finder/skeptic reviews, and the handoff.

## Bulk evidence (stays on the Codex VM)
These stay on Codex env `ccarenv_b64_Y2NhcmVudl9iZGYxYWZkYzZhZTA4MTkxYjkwZDYxZDM4MjFhZTFlMQ`:
- `/workspace/sol-qn-bulk/H44-364bd1e47fa1` (269 files, 73851319 bytes), which
  `bulk-evidence-H44.json` indexes
- the untracked `tests/sol-qualified-units/evidence/` (34 files, about 78 MB of
  patches, handoffs and SHA256SUMS)
- the VM-local backup branches qualified-units-pre-H44 (364bd1e47), pre-e684
  (8ebb2061d) and pre-size-rewrite (f27942fcc)

Claude VMs cannot reach any of this. Re-run validation fresh instead of citing
the old seals or caches.

## Interfaces and owners
- Exclusive writes: `Solidity/Frontend/QualifiedUnits/**`,
  `tests/sol-qualified-units/**`, `scripts/check-sol-qualified-units.py`,
  `docs/feature-work/qualified-unit-resolution.md`.
- Read-only inputs: `Source/Units.lean`, `Source/Resolve.lean`,
  `Frontend/Static/{Units,Closure,Overloads}.lean`. No Source edits (H16/H19/H25).
- H27: QN-SIG normalization stays inside SOL-QN's own paths.
- Not in scope: the separate G25 worktree on the same Codex VM
  (`/workspace/solidity-lean-ucast-1104`, branch codex/solidity-sol-20261103/ucast-1104,
  601ac4993, 4 commits not on master, `tests/primitive-packets-1104/UnsignedCast`)
  is a different assignment. It was not moved or rescued here.

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

You are the Codex Cloud worker for batch "solidity-sol-20261103", task "qualified-units": SOL-QN: qualified multi-unit declaration resolution (G12).
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: b6ba0696102a7a038afe2ed333c09dff397cc5b2. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-sol-20261103/qualified-units` from that exact commit;
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
  "batch": "solidity-sol-20261103", "slug": "qualified-units", "status": "done | partial | blocked",
  "branch": "codex/solidity-sol-20261103/qualified-units", "base": "b6ba0696102a7a038afe2ed333c09dff397cc5b2", "head": "<full committed SHA>",
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

Human-approved H23: SOL-QN — qualified multi-unit declaration resolution (G12)
Base: b6ba0696102a7a038afe2ed333c09dff397cc5b2
Shared rules: intrinsic existing Source syntax/declarations/identities, no new untyped intermediate language; preserve statements, premises, exclusions, observations and proof budgets. No maxHeartbeats increases. No edits to H16 Source modules, H22 ExtCall, or H21 central build/registry changes. Treat existing definitions as read-only. Register new roots/module-map rows centrally at integration after H21, rather than placing shared registry edits in lane commits. Any necessary producer-interface or representation change becomes an ESCALATE with 2–3 options; do not silently widen the lane. Each lane uses its own VM/branch/worktree and exact pinned base, serial Lean diagnostics/checkpoints (`LEAN_NUM_THREADS=1`, `-j1`, 12 GiB/no swap, H1 4 GiB VM reserve). Warn and inspect speed-motivated git history before any potentially slower refactor. Required finder and skeptic read-only reviews per milestone, explicit axiom pins, complete acceptance and final evidence bundle. The hour estimates are work budgets, not a reason to extend scope or claim completion.

## Work queue and acceptance

Value: `docs/coverage-plan.md` G12 and V06 explicitly leave `N.x` namespace resolution and cross-unit typing open; manifest IDs `imports` and `identifiers` remain partial and require declaration identity, lexical shadowing and qualified references. Close the independent name-resolution portion against existing syntax; cross-unit typing integration remains with its future owner.

**Exclusive writes:** `Solidity/Frontend/QualifiedUnits/**`, `tests/sol-qualified-units/**`, `scripts/check-sol-qualified-units.py`, `docs/feature-work/qualified-unit-resolution.md`. New namespaces; no edits to Frontend/Checked (VA1), Frontend/Admission (CR), Frontend/SolcJson/Yul (VY1), Lowering, Source, or existing Frontend/Static files.

**Inputs on master:** `Solidity/Source/Units.lean`, `Solidity/Source/Resolve.lean`, `Solidity/Frontend/Static/{Units,Closure,Overloads}.lean`, and `docs/feature-work/frontend-static.md`. The delivered launch manifest must list only verified input paths; the candidate resolver can use `UnitSet.globals`, `Sees`, declaration identities and the existing namespace symbols directly. No new core representation needed.

**Work queue (8–10 h):** (1) 1 h: complete inventory of qualified-path constructors and current namespace symbols, independent declarative path relation over existing identities, positive/negative obligations; (2) 3 h: implement arbitrary finite qualified-name lookup through namespace aliases, transitive/cyclic imports, duplicate paths and diamond imports, with termination from the existing finite graph; (3) 2–3 h: soundness/completeness against that relation and identity/no-clash preservation, distinguishing missing/ambiguous routes from valid identical declarations; (4) 2 h: exhaustive constructor coverage fixture matrix, solc 0.8.38 differential cases in a new fixture directory, kernel controls for shadowing, two units with same spelling, aliases, cycles, unknown names and nontrivial diamond identity; full per-area reviews and handoff.

**Acceptance:** checker enumerates every new module/declaration and every matrix row, validates compiler pin and expected acceptance/rejection for all fixtures, runs every qualified-resolution theorem/control and trust/axiom gates. At least one successful multi-hop qualified reference, one ambiguous refusal and one missing-symbol refusal. Do not call a self-referential definition-to-checker equality external Solidity correctness. No G13/G15 completion or source-to-EVM claim. No dependency on SOL-OV or SOL-PC.

## Execution and coordinator contract
The first line is the current coordinator header; this human-approved new assignment supersedes its historical "same VM/branch" wording only for this new launch. Use the exact pinned base and assigned branch in the worker preamble. The Claude coordinator retains supervision; Codex auditors/listeners are retired: no new monitor, scheduler or integration/push authorization. Queue budget is 8–10 hours of useful work, never permission to expand scope.
The persistent goal already exists; if get_goal is unavailable in the tool catalog, continue the assignment without that call, never create/reset a goal, and report that limitation. Missing goal tooling is not a design blocker.
Read AGENTS.md, docs/module-map.md, docs/README.md and applicable conventions (including docs/intrinsic.md Gate G0) before edits. Existing modules are read-only, including all Source modules (H16/H19 VY5), Core ExtCall (H22) and shared roots/module maps/build scripts (H21). Keep all writes in the four exclusive paths. Stage explicit files only. Document pending central registrations in your own feature-work doc; no duplicate root/framework.
Use existing coord-tools and per-file Lean MCP diagnostics/lean_multi_attempt; inspect actual Lean/Lake versions and pass the repository-approved KeySort gate before RUNTIME_GATE_PASS. Use ./run-lean.sh for shell checks, obey its actual syntax. Every Lean check serial, explicit -j1 and LEAN_NUM_THREADS=1, hard <=12 GiB/no swap and H1 4 GiB VM reserve. No maxHeartbeats raise, sorry, new axioms, theorem/premise/exclusion weakening or empty/False relations used to claim correctness. Warn and inspect git history before refactors that may slow checking.
At every milestone perform separate read-only finder and skeptic reviews per area, neither using the Lean server; fix confirmed findings and record them in your own milestone doc. Keep explicit axiom pins and complete acceptance coverage. No unrelated proof delegation. If a producer interface cannot represent a requirement, preserve it and report ESCALATE with 2–3 self-contained options. Final handoff includes committed original patch, head/base/branch, all queue/backfill statuses, real command outputs, complete file/theorem/fixture-row coverage, reviews, trust boundaries and checksum manifest. End each turn with CLOUDVM-RESULT, questions=[] when none.
