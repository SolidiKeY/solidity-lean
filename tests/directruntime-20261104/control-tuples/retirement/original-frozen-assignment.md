You are the Codex Cloud worker for batch "solidity-directruntime-20261104", task "control-tuples": Uncovered do-while and tuple construct admission.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: b419c3cf4f642ae519b66bebc26cdf2f7cf93574. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-directruntime-20261104/control-tuples` from that exact commit;
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
  "batch": "solidity-directruntime-20261104", "slug": "control-tuples", "status": "done | partial | blocked",
  "branch": "codex/solidity-directruntime-20261104/control-tuples", "base": "b419c3cf4f642ae519b66bebc26cdf2f7cf93574", "head": "<full committed SHA>",
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

AUTHORIZED DISPATCH after the coordinator host receipt receipts/h28-inactive-20261104-1445.txt confirmed H28 inactive. Fresh remote/ownership audit: directruntime-20261104/receipts/reservation-audit.json. Coordinator reserves DR-A..D via registry.py before freezing this prompt and dispatches through the journaled original-thread launcher. This frozen prompt is the worker dispatch authorization; the earlier prepared draft is superseded. Exact reservation evidence remains on the coordinator in directruntime-20261104/receipts/dispatch-ready.json. No permission to take other lanes or producer paths.

Authorized batch solidity-directruntime-20261104, gpt-6.1-sol. Complete concrete implementation, proofs and validation, not an architecture proposal. Follow AGENTS.md, docs/module-map.md, docs/README.md, intrinsic.md Gate G0 and area conventions. No H16/H19/H25 Source edits, frozen Core ExtCall, other producer files or shared generated roots/maps/trust pins. New modules need a local registration manifest/docs row proposal for central registration, not edits to shared generated roots. Core remains dependency-free and intrinsically typed. No new axiom/sorry/admit, theorem/premise/exclusion weakening, trust expansion or maxHeartbeats increase. Unsupported stays unknown. Ordinary verification must load no Lean kernel/elaborator/tactic frontend/serialized env; certificates remain optional. Keep runtime trusted-verifier boundary unchanged.
Use own attached VM and branch. Local coordinator worktrees are under ~/projects/solidity-lean-worktrees. One heavy Lean check at a time, LEAN_NUM_THREADS=1, -j1; <=12 GiB/no swap, H1 4 GiB available reserve in each VM. Verify actual runtime cgroup, Lean/Lake versions and allowed KeySort gate before RUNTIME_GATE_PASS; use MCP per-file checks and ./run-lean.sh/coord toolkit, no blocked bare lake/lean commands. No systemd-run when already bounded. Check git log and warn before a refactor that could slow checking; measure before/after. No source completion claim from tool availability.
FIRST A publishes concrete interface checkpoint; B/C use it without altering it. Interface producer changes needing a design decision get ESCALATE with 2–3 options. Waiting lanes use fixture/inventory/controls backfill inside their owned paths, no parallel translator. Every milestone has independent read-only finder and skeptic, neither using Lean server; fix confirmed findings and record them. Use actual exact-base/head theorem/axiom signatures, commands/exits/wall/RSS, fixture coverage and fresh source/binary provenance. Distinguish admission success, proof closure, semantic support and backend gaps. End each turn CLOUDVM-RESULT JSON with base/head/branch, gates, reviews, artifacts/hashes, queue accounting, limitations and questions=[] if none. Short commits. No push/merge; usual merge job handles integration under existing authorization. Persistent goal owns continuation: never create/reset another goal or VM.

Exclusive writes: Solidity/Frontend/ExecutableAst/ControlTuple/**; tests/directruntime-20261104/control-tuples/**; docs/feature-work/directruntime-control-tuples.md

Pinned base: b419c3cf4f642ae519b66bebc26cdf2f7cf93574

Work queue:
1. Inventory confirms DirectRuntime lacks DoWhileStatement and TupleExpression/multiple declarations, while existing RawStmt.doWhile/tupleDecl/tupleAssign and RawExpr.tuple provide counterparts. Scope exactly these families; no grammar uniqueness, numeric/constant evaluation, name resolution, internal calls or backend producers. A owns complete census. Read existing SolcJson behavior as immutable reference.
2. Wait for A committed typed extension boundary; fixtures and evaluation-order controls are ready work meanwhile. Implement adapters in ControlTuple only. Do-while must preserve execute-before-test, break/continue, returns and loop annotations by existing lowering, never ad hoc loop semantics.
3. Tuple read/assignment/declaration/return routing only when existing intrinsic semantics expresses the whole shape, preserving holes and simultaneous RHS capture/evaluation order. No overloaded/internal-call semantics expansion. Unsupported inline arrays/calls/types remain unknown and explicitly inventoried.
4. Positive/negative tests, repeated/aliased targets, skipped holes, side effects, zero-iteration distinction, early return and box/diamond controls. Report admission vs proof closure vs model/backend gaps; committed module packet for A with exact signatures and retained build/checking timings, reviews and handoff.


The user requests the full assignment as a persistent goal. The launcher has already created it; use get_goal to inspect it, do not create a second goal. Continue until all required proofs, tests and validation are complete. Mark complete only with evidence for the full assignment; preserve constraints and report blockers.
