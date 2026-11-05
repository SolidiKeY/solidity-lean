# Moved lane: literal-grammar (from a Codex VM)

The user decided (2026-11-05) to move idle Codex lanes to Claude VMs: this lane
(H28 SOL literal grammar, G08) finishes on a Claude VM with the same scope. The
Codex thread is idle with its goal blocked (status partial). Its head e6849d3b
("Merge control-tuples") is already on master, and all 24
`Solidity/Frontend/LiteralGrammarH28/**` modules are registered in the roots
(Q-ROOT-01 is resolved). **Start from origin/cloud/literal-grammar-move
(3b327d00fd2262cfb27ccecdc911e9c5d2e7d4f1)**, merging current origin/master
(aec9adf1ad8666a7e591e42a537069a93dc858cb at move time) into it. Push to your
session branch only.

The rescue branch is e6849d3b plus one WIP commit. That commit restores
`tests/h28-sol/literal-grammar/solc-fixtures.mjs`, the soljson observation runner
over `solc-cases.json`, from the VM-local branch codex/h28-preserved-6492f34c
(sha256 19679c4c9f22007192edf059398c07ce1044fe22b20f8895911050ae978b3ba6).
Master's merge 23a5b676 dropped it. The same merge also dropped Codex
`runtime-bin/{mcp,post-precheck.py,serial-build.py}` and about 270 evidence logs.
Those are deliberately not restored.

## Remaining queue
1. Fresh exact-head validation on the registered master: `./run-lean.sh`, roots,
   orphans, the lane's full gates, and the axiom inventory against
   `tests/h28-sol/literal-grammar/pins.json` (200 theorem pins, 4 control modules).
2. Repair the lane's `audit.py`. It currently fails because it reads pruned
   historical axiom logs. Make it depend only on committed inputs such as
   `evidence/proof-safety-diag.json`, which is still on master, or on fresh output.
3. Re-run the solc 0.8.38 fixture gate fresh with the restored `solc-fixtures.mjs`:
   58 cases × legacy/viaIR, soljson sha256
   6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
   Fetch soljson from the official solc-bin and check the sha.
4. Backfill: suffix properties and byte-length/encoding properties.
5. Whole-lane acceptance, finder/skeptic reviews, and the final handoff in
   `docs/feature-work/h28-literal-grammar.md`.

Known deviations stay retained and documented: surrogate Unicode escapes, and
empty or single-quoted assembly flags.

## Bulk evidence (stays on the Codex VM)
These stay on Codex env `ccarenv_b64_Y2NhcmVudl83OGVkMzYwN2I2ODQ4MTkxYjM0N2E2ODhhN2MwMmU2OA`:
- `/workspace/scratch/h28-rebase-e6849d3b/` (original.patch, HANDOFF.md, SHA256SUMS)
- the H41 owned cache `/workspace/scratch/h28-h35-cache-e7cf5143/owned-lake-cache.tar.gz`
  (sha256 648c8b65…)
- the pre-merge evidence logs on the VM-local branch codex/h28-preserved-6492f34c

Claude VMs cannot reach any of this. Re-run validation fresh instead of citing
the old seals or caches.

## Interfaces and owners
- Exclusive writes: `Solidity/Frontend/LiteralGrammarH28/**`,
  `tests/h28-sol/literal-grammar/**`, `docs/feature-work/h28-literal-grammar.md`.
- Read-only: `Checked/Lexer.lean`, `Checked/Token.lean`,
  `tests/upstream/grammar-0.8.38/SolidityLexer.g4`. No Source edits (H16/H19/H25).
- Shared roots and registries (H21): change them only through `register.sh` and
  module-map fragments. Do not hand-edit generated roots.

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

You are the Codex Cloud worker for batch "solidity-h28-sol-20261104", task "literal-grammar": G08 nonnumeric literal decoder completeness.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-h28-sol-20261104/literal-grammar` from that exact commit;
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
  "batch": "solidity-h28-sol-20261104", "slug": "literal-grammar", "status": "done | partial | blocked",
  "branch": "codex/solidity-h28-sol-20261104/literal-grammar", "base": "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5", "head": "<full committed SHA>",
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

H28-LITERAL-GRAMMAR: G08 nonnumeric literal decoder completeness
Pinned base: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5
Exclusive writes: Solidity/Frontend/LiteralGrammarH28/**; tests/h28-sol/literal-grammar/**; docs/feature-work/h28-literal-grammar.md
Read-only inputs: Solidity/Frontend/Checked/Lexer.lean; Solidity/Frontend/Checked/Token.lean; tests/upstream/grammar-0.8.38/SolidityLexer.g4

H28 is approved; finish the frozen queue, aiming 8–10 hours of useful work without padding. Inputs are pinned published master, immutable. Use attached executor and assigned branch in your own VM; local worktrees under ~/projects/solidity-lean-worktrees when needed. Follow AGENTS.md, docs/module-map.md, docs/README.md and matching conventions; read intrinsic.md Gate G0. No H16/H19/H25 Source edits, no frozen H22 Core ExtCall, no producer-owned implementations, H21 roots/module maps/shared registries/trust inventories, frozen upstream baseline, or another lane's files. New modules have a local registration manifest for central integration; no generated root changes. Core stays dependency-free and intrinsic.
Never weaken theorem statements, premises, exclusions, refusals, observations or budgets; no new axiom/sorry/admit/unsafe/native_decide trust shortcut, no maxHeartbeats raise. No producer-interface changes without reporting ESCALATE with 2–3 options. No push/merge. Do not claim whole compiler correctness from restricted or conditional lemmas. Check git log for speed-motivated changes before refactoring; warn before any potentially slower refactor. Measure matched before/after for speed changes, stop and retain evidence for any >10% slowdown.
Lean work serial LEAN_NUM_THREADS=1 and -j1, one heavy check at a time, <=12 GiB/no swap and H1 4 GiB VM headroom. Discover actual cgroup/runtime, use an existing bounded scope/container if present; do not assume host scope settings apply to a new VM. Prefer Lean MCP diagnostics and scripts/coord-tools/lean-mcp; no blocked bare lake/lean invocation. Record actual Lean/Lake versions and a passing permitted KeySort gate before RUNTIME_GATE_PASS. Use coord toolkit gate/seal/handoff where available. If an unavailable get_goal tool is the only problem, keep working under the existing frozen persistent objective; do not create/reset goals or launch another VM.
Every checkpoint needs actual implementation/proofs/tests, source identities and exact commands/exits/timing/RSS. Separate read-only finder and skeptic per area, neither using Lean server; fix confirmed findings. Acceptance must enumerate all assigned constructors/clauses/files/fixtures, no sample-only inventory, empty/False relation or mocked successful proof. Use inhabited positive and negative controls and universal proofs where requested; timeouts/errors/open obligations stay explicit. Commit short checkpoint messages, one coherent item per commit; keep immutable evidence, bundle/patch/hashes, base/head/branch, theorem signatures/axioms, review verdicts and full queue accounting. End each turn CLOUDVM-RESULT JSON with questions=[] when none. Never emit empty status-only turns. Backfill only inside exclusive scope; an incomplete checkpoint is not whole-goal completion.


## Work queue
1. Inventory strBody, escapeChar, quotedBody, hexBody, plainString, utf8 and plain/unicode/hex literal classification arms. Reuse existing strBody_sound; SOL-NL numeric/EIP55 work excluded. State an independent grammar/value relation without defining correctness by the decoder.
2. Prove missing decoder completeness and exact consumed suffix/value for arbitrary-length literals and escape sequences: simple escapes, hex/unicode escapes, escaped line ends, quote modes, concatenated fragments. Preserve documented invalid-UTF8 treatment and actual solc deviations; do not silently extend Unicode validation.
3. Prove precise hex-pair/underscore rules, fragment concatenation byte-value properties and classification/refusal consequences. Establish constructive round trips against existing decoder; no lexer implementation changes or stronger input contract hiding accepted cases.
4. All-arm kernel controls plus fixed solc 0.8.38 legacy/viaIR scanner fixtures; independently enumerated coverage, theorem/axiom pins, reviews, handoff.

## Backfill queue
Additional suffix and byte-length/encoding properties; numeric literals and compiler imports remain immutable.
