# Moved lane: expression-uniqueness (from a Codex VM)

The user decided (2026-11-05) to move idle Codex lanes to Claude VMs: this lane
finishes on a Claude VM with the same branch and scope. The Codex thread is idle
with its goal blocked. Its last result (head e48d82a2, status partial) was the H44
split, and no Codex worker is editing the checkout. The coordinator's sweep
still merges origin/master into the Codex branch on that VM.
Start from `origin/cloud/expression-uniqueness-move` (c2e862c1825d00567bd8def1b2b79716a022ed62),
merging current origin/master into it. Push to your session branch only.

## Start point and rescue commit
`cloud/expression-uniqueness-move` is the VM lane head d09db89c, which was never
on origin. It holds the G10 proof history up to c37868a4 "Prove certified
expression yield uniqueness and accepted-tree equality", the H44 split e48d82a2,
and coordinator merges of master up to aec9adf1. On top of that sits one WIP
commit c2e862c1 with the VM's stashed refill drafts (`stash@{0}`
"imul-drafts-isolated-from-proof-gate"; stashes 1 and 2 hold the same drafts):
`Solidity/Backend/PrimitivePackets/SignedCheckedMul/{Source,Selected,Target,Agreement,Controls}.lean`
and `docs/feature-work/primitive-packets-1105-SignedCheckedMul.md`.
**These drafts were never checked; Target is known to need repair.** The
SignedCheckedMul modules are not in `Solidity.lean`, so they do not break the
library build until you register them.

The delta against master is 94 `Solidity/Frontend/ExpressionUniqueness/*` modules
(only 7 are on master: Statement, Fixtures, Fragments, Families, Refusals,
SeparatorSplit, TokenSplit), `scripts/check-sol-expression-uniqueness.py`,
`docs/feature-work/expression-uniqueness.md`, 27 files under
`tests/sol-expression-uniqueness/` (control, pin, declaration and registration
JSON) and 93 `+import` lines in `Solidity.lean`. Drop the Codex-only tooling
(`runtime-bin/lake`, `runtime-lakefile.toml`, `runtime-mcp.sh`, `serial-build.py`,
`inside.py`, `bounded.py`) unless a gate needs it.

The lane has two scopes, and both stay assigned:
- **Original SOL-EU (G10 expression yield uniqueness).** The public uniqueness
  theorem and the parseCat accepted-tree corollary are proved on the branch.
  What remains is integration and validation.
- **Refill G25-IMUL-CHECKED-1105 (coordinator, H10/H12 idle-lane rebalance).**
  Checked int256 multiplication, including min*-1: signed overflow/success
  classification through selected code. Template: `Solidity/Backend/PrimitivePackets/CheckedAdd/**`
  (Source/Selected/Target/Agreement/Controls; read-only). Write scope:
  `Solidity/Backend/PrimitivePackets/SignedCheckedMul/**`, `tests/primitive-packets-1105/SignedCheckedMul/**`,
  `docs/feature-work/primitive-packets-1105-SignedCheckedMul.md`. The integrator
  is V09. Reuse `Evm.Signed.smul_ok`/`smul_tail`; do not duplicate arithmetic producers.

## Remaining queue
SignedCheckedMul:
1. Check and repair Source, then Selected, Target (known broken) and Agreement,
   then Controls.
2. Selected-code execution controls on arbitrary saved-stack, populated frames,
   covering both operand orders of min*-1, lower and upper overflow, and regular
   products. The present Controls file has range controls only.
3. Positive and negative controls, axiom inventory under
   `tests/primitive-packets-1105/SignedCheckedMul/`, finder/skeptic review, a
   short commit, and a "register" list.

Expression uniqueness, from `tests/sol-expression-uniqueness/obligations.json`:
- **EU-12 partial:** the full library, TestSuite, corpus and strict integration
  gates have not passed. The global root/orphan check showed 100 missing and the
  central inventory 1241 unrecorded declarations; trust and layers passed. Land
  the registration through the current convention:
  `scripts/coord-tools/register.sh`, a per-lane fragment
  `docs/module-map/<area>.d/expression-uniqueness.md`, and `scripts/coord-tools/fragments.sh`.
  Axiom pins go through `scripts/g07-axiom-pins.json` fragments, or are proposed
  to the coordinator. Then run the full gates fresh.
- **EU-14 open:** the sealed final handoff.
- **EU-01** is `proved-inventory` (29 constructors). Re-check that the checker
  still enumerates every constructor against current master.
- Post-split finder/skeptic reviews of e48d82a2 are still pending. Confirm that
  no theorem-bearing file was externalized.

## Bulk evidence (stays on the Codex VM; H44)
These files are on Codex env `ccarenv_b64_Y2NhcmVudl9kOWM3YjYwZmU2ZTA4MTkxYjc3ZTFhMjNiNzMyODNjNw`:
- The archive `/tmp/sol-eu-h44-bulk-20261105/bulk.tar.gz` (40,669,379 bytes,
  sha256 `92a82be817495dd416f09b1d67b1910258af4952391ff4253614e1651e6943fc`)
  and its file list `/tmp/sol-eu-h44-bulk-20261105/files.json` (1137 files,
  58,093,229 bytes). It sits in /tmp, so it is volatile.
- The untracked originals in the checkout, `tests/sol-expression-uniqueness/evidence/`
  (38 MB) and `kernel-{declarations,emissions,module-declarations}.json(.gz)`.
- The committed index is `tests/sol-expression-uniqueness/bulk-manifest.json`.
  Its absolute VM paths are provenance only.

Claude VMs cannot reach any of this. Regenerate the kernel inventories and
evidence fresh if a gate needs them, and keep them off git with a sha256
manifest.

## Interfaces and owners
- Read-only inputs: `Solidity/Frontend/Checked/{Print,Prec,Parser,Check}.lean`,
  `Solidity/Source/Syntax.lean`, `tests/upstream/grammar-0.8.38/SolidityParser.g4`
  and the CheckedAdd template.
- Do not edit `Solidity/Source/**`: VY5 owns it (H16). Also leave alone the frozen
  H22 Core ExtCall, existing Checked/Static implementations, shared
  tests/trust inventory and other owners' areas.
- Statement, function and unit uniqueness, and parser edits, are out of scope.

## Gates
- Lean MCP diagnostics clean (`severity=error`) on every touched file. Build
  modules one at a time; report any module above 60 s. Before this split,
  `ExpressionUniqueness.Families` took about 188 s as a dependency build, so
  warn before anything that slows it further.
- `./run-lean.sh`, `register.sh --check`, `fragments.sh --check`, `node scripts/check-orphans.mjs`.
  `#print axioms` on the headline uniqueness theorem and the SignedCheckedMul
  agreement theorems must show standard axioms only.
- Separate read-only finder and skeptic reviews per checkpoint, neither using
  the Lean server. Fix confirmed findings and record them in the feature document.

## Exclusions
No sorry/admit/axiom/unsafe or native_decide shortcuts (`decide +kernel` is
fine), and no `maxHeartbeats` increases. Do not weaken statements, premises,
exclusions, refusals or budgets. If the certificate truly admits an ambiguity,
commit a kernel counterexample and keep the original target open. Use no Codex
tooling (`ship-cache.sh`, Docker caps, the `codex/*` branch).

## Original assignment (Codex prompt; replace Codex-specific tooling with the preamble's rules)
You are the Codex Cloud worker for batch "solidity-sol2-20261104", task "expression-uniqueness": G10 certified expression yield uniqueness.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-sol2-20261104/expression-uniqueness` from that exact commit;
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
  "batch": "solidity-sol2-20261104", "slug": "expression-uniqueness", "status": "done | partial | blocked",
  "branch": "codex/solidity-sol2-20261104/expression-uniqueness", "base": "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5", "head": "<full committed SHA>",
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

SOL-EU: G10 certified expression yield uniqueness

Exclusive write scope: Solidity/Frontend/ExpressionUniqueness/**; tests/sol-expression-uniqueness/**; scripts/check-sol-expression-uniqueness.py; docs/feature-work/expression-uniqueness.md

Gap and value: G10 translation validates accepted trees against Syn.yield/Syn.prec but the published roadmap explicitly leaves expression unambiguity open.

Read-only master inputs: Solidity/Frontend/Checked/Print.lean; Solidity/Frontend/Checked/Prec.lean; Solidity/Frontend/Checked/Parser.lean; Solidity/Frontend/Checked/Check.lean; Solidity/Source/Syntax.lean; tests/upstream/grammar-0.8.38/SolidityParser.g4

H26 pre-approves this independent Sol lane. Work 8–10 hours where scope supports it; estimates are not completion evidence. All listed inputs are on pinned master. Preserve intrinsic existing Source/Syn/types; core remains dependency-free. Never edit H16/H19/H25 Source modules (VY5-only), frozen H22 Core ExtCall, H21 shared roots/registries/layout, any other owner area, existing Checked/Static implementations, shared tests/trust inventory, or generated library roots. All inputs read-only. Register new modules/module-map rows through coordinator at integration; include a registration manifest in your own tests directory. No push/merge. New premise/interface/scope changes require ESCALATE with 2–3 concrete options; no sorry/admit/axiom/unsafe or weakened statements, premises, exclusions, observations, refusals or budgets. Do not raise maxHeartbeats. Check speed-motivated git history and warn before a potentially slower refactor; this lane should add modules only.
Use attached executor; fetch pinned published base and verify ancestry. Discover actual toolchain/commands and follow AGENTS.md, intrinsic.md Gate G0, module-map/docs README and matching conventions. VM Lean work serial: LEAN_NUM_THREADS=1 explicit -j1, MemoryMax 12 GiB/no swap, H1 4 GiB free VM reserve; MCP diagnostics preferred and one heavyweight check at a time. Do not run bare lake env/lean if worker policy blocks it; use Lean MCP and ./run-lean.sh. Record actual Lean/Lake versions and passing permitted KeySort check before RUNTIME_GATE_PASS. Use scripts/coord-tools toolkit for timings/gate/seal/handoff if available.
Every checkpoint: implement actual definitions/proofs/tests; separate read-only finder and skeptic reviews, neither using Lean server; fix confirmed findings. Acceptance enumerates every new module/declaration, syntax constructor or case family, control and open obligation, checks all fixtures and exact source pins; a file-presence check alone is insufficient. Prove arbitrary structures/lengths rather than native_decide-only examples. Keep missing proofs and failed/time-limited checks explicit. Final committed packet: short commit, exact base/head/branch, full patch/bundle, immutable hashes, commands/exits/timings/peak RSS, theorem signatures and actual axiom sets, independent review verdicts, scope-complete acceptance, inhabited witnesses and negative controls, unclosed obligations. End each turn with CLOUDVM-RESULT JSON including questions; no empty status turn or marker-only commits. If waiting on an unavailable future input, use only the assigned backfill; do not widen scope.

## Work queue
1. Inventory all intrinsic expression constructors, their token boundaries/layout witnesses and Syn.prec conditions; reproduce the documented prefix/postfix and conditional-assignment refusals without changing expected verdicts. State uniqueness over existing Syn .expr, token yields and precedence, accounting exactly for syntactic layout witnesses that do not affect tree identity. No second untyped AST.
2. Develop reusable token-splitting/balanced-delimiter lemmas and precedence-level root reconstruction. Prove operator associativity and precedence unambiguity for arbitrary-size trees across arithmetic/bitwise/logical/relational/exponent/conditional/assignment roots.
3. Extend uniqueness through primary, grouping/tuple, member/index/slice, call/options/named/positional argument syntax and prefix/postfix constructors, using an exhaustive constructor ledger. Derive a public theorem that any two certified expression trees with the same token sequence are equal, and its parseCat accepted-tree corollary. Do not assume the desired root split or uniqueness as a premise. If the existing certificate truly admits an ambiguity, commit a kernel-checked counterexample, preserve the original theorem target as open, and report the exact producer-interface repair; never silently replace uniqueness with parser determinism.
4. Add nontrivial arbitrary-family controls and all precedence/association boundary classes, checker enumerating every constructor and obligation, standard-only axiom pins, separate finder/skeptic review and sealed handoff.

## Backfill queue
Improve delimiter disjointness, root decomposition and nearest-else-independent expression helpers in this namespace. Statement/function/unit uniqueness and parser edits are outside scope.
