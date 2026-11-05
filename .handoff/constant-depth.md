# Moved lane: constant-depth (from a Codex VM)

The user decided (2026-11-05) to move idle Codex lanes to Claude VMs: this lane
finishes on a Claude VM with the same branch and scope. The Codex thread is idle
with its goal blocked. Its last result (head 0c6d40e2, status partial) was an H44
split of the refill item; no Codex worker is editing the checkout. The
coordinator's sweep still merges origin/master into the Codex branch on that VM.
Start from `origin/cloud/constant-depth-move` (06e61bc0556a42e6084da10cd5b8d744b827f71a),
merging current origin/master into it. Push to your session branch only.

## Start point
`cloud/constant-depth-move` is the VM's lane head 06e61bc0, which was never on
origin: RawInt commit 0c6d40e2 plus coordinator merges of master up to aec9adf1.
It has no WIP commit because the VM checkout was clean, with no stash and no
untracked files. Its delta against master is the seven-file reviewable RawInt
increment:
`Solidity/Backend/CalldataPackets/RawInt/{Execution,Controls}.lean` (additions
on top of the copies already on master), `docs/feature-work/calldata-packets-1105-RawInt.md`,
`tests/calldata-packets-1105/RawInt/{Axioms.lean,H44-manifest.json,bounded.py,lake}`.
Drop `tests/calldata-packets-1105/RawInt/lake` (a Codex-VM wrapper) unless a gate needs it.

The lane has two scopes, and both stay assigned:
- **Original SOL-CB (G13 constant depth).** `Solidity/Frontend/ConstantDepth/{Rank,Lookup,Complete}.lean`
  are on master already. They contain `rank_lt`, `rank_le_decls`,
  `rank_resolved_dependency_lt`, `nconst_rank_complete`, `nconst_levels_complete`,
  `evalConst_complete`, `evalConst_resolved_complete`, `evalConst_iff` and
  `evalConst_none_iff`. Work-queue items 1–3 are therefore in place, except the
  arrayLenB corollaries.
- **Refill G35-INT-RAW-1105 (coordinator, H10/H12 idle-lane rebalance).**
  Raw intN calldata-to-memory packet with sign-extension validation and a revert
  on dirty input. Template: `Solidity/Backend/CalldataPackets/RawUint/**`
  (read-only). Write scope: `Solidity/Backend/CalldataPackets/RawInt/**`,
  `tests/calldata-packets-1105/RawInt/**`, `docs/feature-work/calldata-packets-1105-RawInt.md`.
  The integrator is V11. Registration, pins and module-map rows go to the
  coordinator: list them under "register".

## Remaining queue
RawInt, taken from the feature document's finder/skeptic lists:
- Width-specific accepted-range arithmetic: an independent signed-extension
  accepted-word equivalence for every intN. `signed_decode_range` exposes only the
  256-bit signed branch.
- Copying of actual raw negative bytes and mixed offsets. The negative roundtrip
  controls do not yet establish this.
- Frame binding: `guarded_run` deliberately does not identify its data bytes
  with `F.cd`. Prove it, together with selector/guarded-entry controls.
- Partial-word padding and near-width controls, plus exact guarded axiom pins in
  `tests/calldata-packets-1105/RawInt/Axioms.lean`.
- Already closed: observations (`copy_observations`), empty/EOF and horizons 0/1.
  Keep them closed.

ConstantDepth (original queue):
- Item 3 corollaries: arrayLenB completeness where the existing ArrayLenOK
  supports it. No such theorem exists in `ConstantDepth/` on master.
- Item 4: controls for chains at or near the declaration count, shared diamonds,
  multiple scopes and shadowing, cycles and unused cycles, and overflow. Also the
  scope-complete acceptance checker `scripts/check-sol-constant-depth.py`,
  `tests/sol-constant-depth/**` (with its registration manifest),
  `docs/feature-work/constant-depth.md`, and axiom pins for every new theorem.
  None of these files is on master or on the move branch. The VM's earlier
  ConstantDepth packet is not available. The coordinator still owes the 79
  ConstantDepth axiom-pin registrations (answer to Q-PIN-1: coordinator-applied
  at a scheduled merge). Regenerate the pin proposal from the current master
  declarations rather than citing the old packet.
- Backfill: rank monotonicity, exact lookup/dependency correspondence, and the
  array-length consumers that master can already express.

## Bulk evidence (stays on the Codex VM; H44)
The RawInt bulk is outside the checkout at `/workspace/raw-int-h44-4d2cc5f8ae16`
on Codex env `ccarenv_b64_Y2NhcmVudl80NThjZjM0YjU3MDg4MTkxODE4YTMyNjRmMDUxZTk3Zg`:
135 files, 174,815,175 bytes, manifest sha256 `de506561ef1b7261ffc18455076d20959a381be157406c656e26d5e6ed466fbf`.
The committed index is `tests/calldata-packets-1105/RawInt/H44-manifest.json`.
Other VM-only items are the seal logs in `/tmp/constant-depth-*.log` and
`/tmp/raw-int-*.log`, and the local backup branches `codex/solidity-sol2-20261104/constant-depth-pre-*`
(pre-H44 history 4d2cc5f8). Claude VMs cannot reach any of this. Re-run
validation fresh instead of citing the old bulk or seals. Commit only reviewable
evidence, and keep any new bulk off git with a sha256 manifest.

## Interfaces and owners
- Read-only inputs: `Solidity/Frontend/Static/{Consts,Closure}.lean`,
  `Solidity/Source/{ConstCheck,Resolve,Decls}.lean`, and the RawUint template.
- Do not edit `Solidity/Source/**`: VY5 owns it (H16/H19/H25). Also leave alone
  the frozen H22 Core ExtCall, existing Checked/Static implementations, shared
  tests and trust inventory, and other owners' areas.
- Registration follows the current master convention (AGENTS.md):
  `scripts/coord-tools/register.sh` for the roots, plus a per-lane module-map
  fragment `docs/module-map/<area>.d/<lane>.md` and `scripts/coord-tools/fragments.sh`.
  Pins and shared roots stay with the coordinator/integrator (H28). Propose the
  rows and imports in the handoff if you do not land them.

## Gates
- Lean MCP diagnostics clean (`severity=error`) on every touched file. Build
  touched modules one at a time; report any module above 60 s.
- `./run-lean.sh`, `bash scripts/coord-tools/register.sh --check`,
  `bash scripts/coord-tools/fragments.sh --check`, `node scripts/check-orphans.mjs`.
  `#print axioms` for the headline theorems must show standard axioms only.
- Separate read-only finder and skeptic reviews per checkpoint, neither using
  the Lean server. Fix confirmed findings and record them in the feature document.

## Exclusions
No sorry/admit/axiom/unsafe or native_decide shortcuts, and no `maxHeartbeats`
increases. Do not weaken statements, premises, exclusions, observations,
refusals or budgets. Escalate a new premise or scope change with 2–3 options.
Use no Codex tooling (`ship-cache.sh`, Docker caps, the `codex/*` branch).

## Original assignment (Codex prompt; replace Codex-specific tooling with the preamble's rules)
You are the Codex Cloud worker for batch "solidity-sol2-20261104", task "constant-depth": G13 acyclic named-constant finite-depth completeness.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-sol2-20261104/constant-depth` from that exact commit;
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
  "batch": "solidity-sol2-20261104", "slug": "constant-depth", "status": "done | partial | blocked",
  "branch": "codex/solidity-sol2-20261104/constant-depth", "base": "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5", "head": "<full committed SHA>",
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

SOL-CB: G13 acyclic named-constant finite-depth completeness

Exclusive write scope: Solidity/Frontend/ConstantDepth/**; tests/sol-constant-depth/**; scripts/check-sol-constant-depth.py; docs/feature-work/constant-depth.md

Gap and value: Consts.lean documents that enough-level completeness is proved but levels E = E.decls.length + 1 sufficiency for acyclic constants remains unproved.

Read-only master inputs: Solidity/Frontend/Static/Consts.lean; Solidity/Frontend/Static/Closure.lean; Solidity/Source/ConstCheck.lean; Solidity/Source/Resolve.lean; Solidity/Source/Decls.lean

H26 pre-approves this independent Sol lane. Work 8–10 hours where scope supports it; estimates are not completion evidence. All listed inputs are on pinned master. Preserve intrinsic existing Source/Syn/types; core remains dependency-free. Never edit H16/H19/H25 Source modules (VY5-only), frozen H22 Core ExtCall, H21 shared roots/registries/layout, any other owner area, existing Checked/Static implementations, shared tests/trust inventory, or generated library roots. All inputs read-only. Register new modules/module-map rows through coordinator at integration; include a registration manifest in your own tests directory. No push/merge. New premise/interface/scope changes require ESCALATE with 2–3 concrete options; no sorry/admit/axiom/unsafe or weakened statements, premises, exclusions, observations, refusals or budgets. Do not raise maxHeartbeats. Check speed-motivated git history and warn before a potentially slower refactor; this lane should add modules only.
Use attached executor; fetch pinned published base and verify ancestry. Discover actual toolchain/commands and follow AGENTS.md, intrinsic.md Gate G0, module-map/docs README and matching conventions. VM Lean work serial: LEAN_NUM_THREADS=1 explicit -j1, MemoryMax 12 GiB/no swap, H1 4 GiB free VM reserve; MCP diagnostics preferred and one heavyweight check at a time. Do not run bare lake env/lean if worker policy blocks it; use Lean MCP and ./run-lean.sh. Record actual Lean/Lake versions and passing permitted KeySort check before RUNTIME_GATE_PASS. Use scripts/coord-tools toolkit for timings/gate/seal/handoff if available.
Every checkpoint: implement actual definitions/proofs/tests; separate read-only finder and skeptic reviews, neither using Lean server; fix confirmed findings. Acceptance enumerates every new module/declaration, syntax constructor or case family, control and open obligation, checks all fixtures and exact source pins; a file-presence check alone is insufficient. Prove arbitrary structures/lengths rather than native_decide-only examples. Keep missing proofs and failed/time-limited checks explicit. Final committed packet: short commit, exact base/head/branch, full patch/bundle, immutable hashes, commands/exits/timings/peak RSS, theorem signatures and actual axiom sets, independent review verdicts, scope-complete acceptance, inhabited witnesses and negative controls, unclosed obligations. End each turn with CLOUDVM-RESULT JSON including questions; no empty status turn or marker-only commits. If waiting on an unavailable future input, use only the assigned backfill; do not widen scope.

## Work queue
1. Pin existing TEval/NamedConst, ConstsAcyclic, constDeps/constNodes, lookup identities and levels. Build the complete named-dependency/rank ledger with duplicate declarations, shadowing, scopes and unused cycles handled exactly as current resolution does. No new resolution checker and no dependency on SOL-QN.
2. Prove acyclicity yields a strictly decreasing finite rank on every actually resolved named-constant dependency. Derive the existing levels bound from E.decls membership rather than assuming a depth bound or the evaluation result. Reuse but do not merely repackage the existential teval_complete/nconst_complete.
3. Prove named-constant and typed-expression evaluation at the actual public evalConst bound returns the independently derived TEval/NamedConst value under the existing well-formedness/acyclicity contract. Preserve exact conversions, overflow refusal, declared integer type, rational literal behavior and scope. Add arrayLenB completeness corollaries where existing ArrayLenOK supports them. If the advertised bound is false under existing contracts, supply an inhabited kernel counterexample and implement/prove an additive rank-derived evaluator in this namespace without changing old APIs; record original-bound obligation as false/open rather than adding a new premise.
4. Controls for chains at/near declaration count, shared diamonds, multiple scopes/shadowing, cycles/unused cycles and overflow; scope-complete acceptance, all new theorem axiom pins, finder/skeptic and final evidence.

## Backfill queue
Strengthen rank monotonicity and exact lookup/dependency correspondence; extend array-length consumers already expressible on master. No Source/Static producer edits.
