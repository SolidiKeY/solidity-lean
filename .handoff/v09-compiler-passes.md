# Moved lane: v09-compiler-passes (from a Codex VM)

The user decided (2026-11-05, H38) to move this whole lane to a Claude VM: the G25
packet integration and the TF-gate fix. Start from `origin/cloud/v09-move`
(504c2d17), merging current origin/master into it; the TF-gate work is on
`origin/cloud/v09-tf-move` (1b7b365f, not yet in the lane head). Push to your
session branch only.

## Added checkpoint: machine SAR (user decision H39, 2026-11-05)
The memory machine has no SAR: `Evm.Machine.Instr` lacks it, and `Evm.Layout.sTail`
emits nothing for signed shr. Add SAR to the machine instruction set, its semantics
and the layout, with kernel proofs that it agrees with the Scalar endpoint `intShr`.
Then lane v14 reproves its G25-SAR-1105 target at machine level. Keep the change
minimal and in the Evm machine and layout files; do not edit Solidity/Source/**
(VY5) or Core ExtCall.

## Original assignment (Codex prompt; replace Codex-specific tooling with the preamble's rules)
You are the Codex Cloud worker for batch "solidity-v07-v11-20261030", task "v09-compiler-passes": V09: compiler certificates and expression sequencing G24-G26 G31.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: fb379ae20f10e2c92113453ddd9d40d8f2efbe09. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-v07-v11-20261030/v09-compiler-passes` from that exact commit;
  verify its ancestry before continuing an existing branch. Preserve unexpected
  local work and report a checkout/base mismatch rather than resetting it.
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
  "batch": "solidity-v07-v11-20261030", "slug": "v09-compiler-passes", "status": "done | partial | blocked",
  "branch": "codex/solidity-v07-v11-20261030/v09-compiler-passes", "base": "fb379ae20f10e2c92113453ddd9d40d8f2efbe09", "head": "<full committed SHA>",
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

# V09: compiler certificates and expression sequencing G24-G26 G31

Owned new modules: `Solidity/Backend/Passes/**`. Owning feature document: `docs/feature-work/roadmap-v09-compiler-passes.md`. Groups/children: G24.01-G24.04, G25, G26, G31.

You are assigned one complete roadmap lane from the next five lanes V07-V11, including implementation, kernel proofs, relevant tests, per-checkpoint reviews and final handoff. Read docs/coverage-plan.md and your G groups/child packages as the authoritative obligations. Aim for eight to ten hours of useful work including checks, without treating elapsed time, a checkpoint or a smaller preparation result as full lane completion.

## Dependency and ownership contract
The base is the freshly fetched origin/master recorded by the preamble. At this base V05 and V06 are PARTIAL, G15 has not started, and V04 source semantics is still owned by Claude session session_01BtDs9SxyZWBwRRekThueMB on cloud/roadmap-l2-20261029/lane-semantics. The roadmap's final checks are a dependency chain V06 -> V07 -> V08 -> V09 -> V10 -> V11. These five VMs run concurrently ONLY for independent implementations and proofs against published interfaces. Missing semantic/coverage hypotheses are explicit prerequisites, never assumptions disguised as closed proofs. Do not mark a parent G group or lane done with missing prerequisites. Start by reproducing a concrete current gap and tracing relevant manifest localEvidence against actual source. Do useful independent checkpoints/backfill before stopping on a dependency. If no assigned independent work remains, report blocked/partial honestly under the goal tool's rules.

2026-10-30 ownership snapshot: existing Codex batches reserve all existing Solidity/Evm/** and Bridge byte-memory/numeric-storage/control-flow/Widths modules, memory loops, memory-to-storage copying, reference arrays/structs/internal calls, readonly-call preservation, function-reference arguments, lazy/noncanonical calldata decoding, getter/entrypoint integration, differential generator, SolKey re-pin, TestSuite/Derived*, calculus revert/diamond/payment and closer work. In solidity-independent5-20261029, scalar-lowering remains active and owns Backend/Scalar/** (G25); storage-values reserves its G27 representation/recursive frame proofs; environment-lowering owns Backend/Environment/** (G31); failure-emission owns Backend/Failure/** (G38); creation-artifacts owns Backend/Creation/** (G44.02). Some report component completion but are not integrated: reuse only published checked results; do not duplicate their queues or import unmerged branches. Idle/blocked work stays reserved. Do not recreate or rephrase any platform-restricted task in another VM; leave it with its existing owner. Claude reserves Source/**, source static/parser modules, Semantics source-foundation edits, Roadmap/Controls and G01 interfaces, Hash/**, Hashed* layouts, Language/FixedPoint/**, Precompiles/**, Stipend/** and existing Backend/{Opcode,Jumpdest,Assembler,Control,Checks,EvmVectors}.lean and decoder/precompile adapters. Keep all existing owners' source untouched.

Your owned namespace and document are below. New independent modules there may import published intrinsic definitions read-only. Do not invent another untyped AST, IR, value/state layer or duplicate semantics to evade a missing proof. Existing semantic relations must be independent of the compiler and relations may not assume their desired preservation result. You may add sound adapters/certificates over the existing intrinsic interfaces; a parameterized composition theorem does not discharge its missing premises. Source lowering must eventually relate the independent Source semantics to the actual intrinsic program, not compare two invocations of the same evaluator. Never replace an unavailable source semantics by the emitted target's execution. Do not import another new V07-V11 lane until its prerequisite is published and independently validated. Do not fetch/cherry-pick/merge another worker's unpublished branch. A coordinator can arrange integration later; this launch does not authorize any push/merge/PR. Keep the exact pinned base and record prerequisite revisions.

Read AGENTS.md, docs/module-map.md, docs/README.md, docs/intrinsic.md (Gate G0), docs/parallelism.md, docs/contributing.md and .agents/skills/lean-verify/SKILL.md. Read the matching .claude/rules conventions (typing, derivations, soundness as applicable), G01 contracts, G03 dependency ledger and G04 restrictions, G06 EVM pin, actual human decisions in docs/solidity-scope.md and roadmap-decisions-impact.md. Statements, values, terms, formulas and states stay intrinsic; the core stays dependency-free. Preserve all refusals, observations, admitted source profile, Fml.inTarget, verdicts, SolKey names/branches and proof budgets. No new axioms, sorry in deliverables, native_decide trust shortcuts, implemented_by shortcuts or maxHeartbeats increases. Warn before a potentially slower refactor and inspect speed-motivated git history first. Representation changes need the intrinsic gate; don't perform a broad refactor merely to make this lane look complete.

Write only owned new modules, your feature document, new lane-specific tests/fixtures/scripts. Append-only registration imports in Solidity.lean, module-map rows and a docs/README entry are allowed; serialize these within your VM. Do not rewrite global coverage status, the generated G03 ledger, manifests, TrustAudit pins owned by another task, existing semantic files or reserved directories. Record proposed ledger changes and exact feature IDs in your own handoff for coordinator reconciliation. Keep imports local/acyclic and core below elaborators.

## Runtime, checks and reviews
Use the attached executor and discover real checkout/tool availability. Record actual Lean and Lake versions, RAM/cgroup limits and successful `lake build Solidity.KeySort` command output before reporting RUNTIME_GATE_PASS. Follow actual platform/build permissions; if a command is forbidden, retain pending evidence rather than bypassing it. Verify exact base and clean isolated codex branch. Respect writer locks if another writer exists. Use LEAN_NUM_THREADS=1 and explicit -j1, a process-group MemoryMax=12G/MemorySwapMax=0 cap on the 16 GiB VM with remaining RAM for OS, monitor aggregate RSS/cgroup peak and avoid concurrent LSP/builds. The local coordinator's 12 GiB free-memory reserve is not an extra reservation in this VM. Keep heavy work serial and reuse source/toolchain-keyed disk caches after one cold build. Read G02 measurements (its older lane numbers are historical); do not increase process/TestSuite time budgets or kill other sessions.

After editing a Lean file use per-file Lean MCP diagnostics (interactive=false, severity=error) when available, then focused target checks; new imports/final confirmation need the repository's bounded import-closure/full gate. Use ./run-lean.sh when permitted, and report any actual command restrictions. No claim of complete whole-lane proofs with required gates missing. Require inhabited nontrivial witnesses, relevant negative controls, feature-combination regressions and #print axioms for headline theorems. Run applicable layer/orphan/trust/structural checks and new lane-specific tests. For docs, require valid owned paths/relative links and no NEW check-doc-paths findings against exact base. Retain the raw full checker failure, even if identical historical debt passes the explicitly separate no-new-findings gate. Compare any inherited build failure against exact base rather than automatically waiving it; don't relabel failed gates green. Kernel proofs, bounded external EVM/compiler tests and remaining coverage are distinct evidence.

End EVERY checkpoint/milestone with separate independent read-only finder and skeptic reviews per area, neither using Lean server/builds. Use review subagents if available; this assignment explicitly authorizes them for those reviews only. Fix confirmed findings and record them in the feature document. Final review must inspect the actual diff, hypotheses, non-vacuity, ownership and handoff, not just green logs. Commit short reviewable checkpoints on your assigned branch with base/head and artifact evidence; no push, merge or PR. Supply original patch, git bundle if feasible, owning document, final handoff, command logs, checksums and absolute VM paths. Report every work/backfill item, exact theorem names/premises and open dependencies. A full lane remains partial/blocked if reserved pieces or final composition are unavailable. Preserve the existing persistent goal; mark complete only when its entire assignment and checks are achieved. Finish with the preamble's CLOUDVM-RESULT JSON and exact statuses.

## Work queue
1. G24.01-.04: audit actual Compiler.Compilation branch-indexed certificates, Input/Rep/Agrees and existing core/memory entry recognizers against G01 Lang/Cert. Implement intrinsic adapters that preserve correlated program/context/state relations, explicit failure and resource-prefix observations, then typed sequencing/composition for mixed programs where current semantics permits it. Existing Evm modules are read-only. Prove useful independently inhabited cases instead of merely restating generic Cert.comp or erasing fragment predicates in names.
2. G25: map every scalar family and exception guard to the active scalar-lowering owner's published/current interface. The owner retains opcode selection and arithmetic proofs. Implement only the independent pass/value certificate adapters and composition obligations around committed scalar semantics; record absent Backend.Scalar artifacts as a dependency. Do not reproduce its arithmetic queue or assume its future theorem.
3. G26: implement/prove typed stack/frame/tail and expression sequencing/capture adapters over existing Instr/Compilation and intrinsic values: short-circuit, conditional references, tuples and effect ordering, with positive mixed cases and wrong-order/stack-corruption negative controls. No alternate Instr/IR or edits to reserved Evm/control-flow/assembler modules; emitted programs must use existing target constructors.
4. G31: map approved environment/metadata/crypto component obligations to the environment-lowering owner's published evidence, then implement only certificate composition and per-run-premise transport where available. Prove exact scope of composed results, including argument effects, resource adequacy and failure preservation. Final G24-G26/G31 and source-to-bytecode closure waits for V08 and real primitive/EVM proofs; no always-revert/vacuous compiler result.

## Backfill queue
A. Prove independent context/frame extension, stack-tail noninterference, sequencing associativity and two-sided failure/prefix transport for the new concrete compiler adapters, with reachable nontrivial witnesses.
B. Add mixed core/memory pass regression certificates and counterexamples to fragment cherry-picking, empty-acceptance and always-revert claims. Coverage gaps stay named obligations. Do not duplicate old compiler fixes, scalar opcode families or environment instruction selection.
