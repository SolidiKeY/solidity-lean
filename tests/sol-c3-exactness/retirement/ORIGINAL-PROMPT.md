You are the Codex Cloud worker for batch "solidity-sol2-20261104", task "c3-exactness": G14 exact C3 merge trace and finite fuel coverage.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-sol2-20261104/c3-exactness` from that exact commit;
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
  "batch": "solidity-sol2-20261104", "slug": "c3-exactness", "status": "done | partial | blocked",
  "branch": "codex/solidity-sol2-20261104/c3-exactness", "base": "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5", "head": "<full committed SHA>",
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

SOL-C3: G14 exact C3 merge trace and finite fuel coverage

Exclusive write scope: Solidity/Frontend/C3Exactness/**; tests/sol-c3-exactness/**; scripts/check-sol-c3-exactness.py; docs/feature-work/c3-exactness.md

Gap and value: Existing C3 proofs establish successful linearizations obey partial-order laws; deterministic C3 choice, failure characterization and fuel adequacy remain separate obligations.

Read-only master inputs: Solidity/Source/Inheritance.lean; Solidity/Frontend/Static/C3.lean; Solidity/Frontend/Static/Inheritance.lean; Solidity/Source/Decls.lean

H26 pre-approves this independent Sol lane. Work 8–10 hours where scope supports it; estimates are not completion evidence. All listed inputs are on pinned master. Preserve intrinsic existing Source/Syn/types; core remains dependency-free. Never edit H16/H19/H25 Source modules (VY5-only), frozen H22 Core ExtCall, H21 shared roots/registries/layout, any other owner area, existing Checked/Static implementations, shared tests/trust inventory, or generated library roots. All inputs read-only. Register new modules/module-map rows through coordinator at integration; include a registration manifest in your own tests directory. No push/merge. New premise/interface/scope changes require ESCALATE with 2–3 concrete options; no sorry/admit/axiom/unsafe or weakened statements, premises, exclusions, observations, refusals or budgets. Do not raise maxHeartbeats. Check speed-motivated git history and warn before a potentially slower refactor; this lane should add modules only.
Use attached executor; fetch pinned published base and verify ancestry. Discover actual toolchain/commands and follow AGENTS.md, intrinsic.md Gate G0, module-map/docs README and matching conventions. VM Lean work serial: LEAN_NUM_THREADS=1 explicit -j1, MemoryMax 12 GiB/no swap, H1 4 GiB free VM reserve; MCP diagnostics preferred and one heavyweight check at a time. Do not run bare lake env/lean if worker policy blocks it; use Lean MCP and ./run-lean.sh. Record actual Lean/Lake versions and passing permitted KeySort check before RUNTIME_GATE_PASS. Use scripts/coord-tools toolkit for timings/gate/seal/handoff if available.
Every checkpoint: implement actual definitions/proofs/tests; separate read-only finder and skeptic reviews, neither using Lean server; fix confirmed findings. Acceptance enumerates every new module/declaration, syntax constructor or case family, control and open obligation, checks all fixtures and exact source pins; a file-presence check alone is insufficient. Prove arbitrary structures/lengths rather than native_decide-only examples. Keep missing proofs and failed/time-limited checks explicit. Final committed packet: short commit, exact base/head/branch, full patch/bundle, immutable hashes, commands/exits/timings/peak RSS, theorem signatures and actual axiom sets, independent review verdicts, scope-complete acceptance, inhabited witnesses and negative controls, unclosed obligations. End each turn with CLOUDVM-RESULT JSON including questions; no empty status turn or marker-only commits. If waiting on an unavailable future input, use only the assigned backfill; do not widen scope.

## Work queue
1. Inventory Env.merge/linearizeF/linearize, list filtering, deterministic first admissible-head selection and fuel formulas. State an independent inductive C3 merge trace over existing declaration identities: choose the first candidate head absent from every tail, remove that head globally, succeed only at empty residual lists; state inconsistent-residual stuckness without calling Env.merge in the relation.
2. Prove soundness/completeness and trace uniqueness for Env.merge at a constructive fuel bound from the finite input lists, plus precise distinction between insufficient fuel and genuine C3 ordering obstruction. Derive no-duplicates, exact membership and local ordering from the relation; do not duplicate linearize_sound as the main deliverable.
3. Lift exact merge/fuel correspondence to existing Env.linearize for acyclic, resolved inheritance graphs under their existing admission invariants, preserving reverse direct-base order and constructor order. Cover diamonds and repeated shared ancestors. Prove successful output uniqueness from deterministic C3, and refuse actual cyclic/ordering-inconsistent graphs with a checked witness. If existing public fuel is insufficient, preserve that obligation visibly with a kernel counterexample and prove an additive sufficient-fuel entrypoint without modifying the producer API.
4. All-head-choice and obstruction controls, arbitrary-family kernel proofs, pinned solc multiple-inheritance fixtures and full acceptance/axiom checks, finder/skeptic and sealed handoff.

## Backfill queue
Additional constructive obstruction certificates and constructor-order consequences; no override-graph validation, modifier resolution or SOL-OV writes/dependencies.


The user requests the full assignment as a persistent goal. The launcher has already created it; use get_goal to inspect it, do not create a second goal. Continue until all required proofs, tests and validation are complete. Mark complete only with evidence for the full assignment; preserve constraints and report blockers.
