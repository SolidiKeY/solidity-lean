# Moved lane: vt1-solc-validation (from a Codex VM)

The user decided (2026-11-05) to move idle Codex lanes to Claude VMs: this lane
(batch `solidity-fullscope-20261104`, VT1: T01, T02) is finished on a Claude VM
with the same branch scope and exclusive writes. The Codex thread is idle with its
goal blocked (11 turns; last turn was a history-only rebase onto master). Start
from current **origin/master**: the lane head 70845978 (and the preserved previous
head 6d1cd27d) are already on master. Push to your session branch only.

## Start point and rescue contents
No rescue branch. The VM checkout (`/workspace/solidity-lean`, branch
`codex/solidity-fullscope-20261104/vt1-solc-validation` @ 70845978) is clean, with
no unpushed commits. Everything reviewable is on master:
`Solidity/SolcValidation/{Dialect,DataLayout,DataResolution}.lean`,
`Solidity/Frontend/SolcJson/{IrImport,IrImportControls}.lean`,
`docs/feature-work/fullscope-vt1.md` (checkpoints C01-C05) and
`tests/fullscope-20261104/vt1/**` (fixtures `Census.sol`, `ObjectData.yul`, check
scripts, `ImportFollowup/` Signatures/ParserChecks, and older committed evidence).

## Bulk evidence that stays on the Codex VM (H44)
Codex env `ccarenv_b64_Y2NhcmVudl8xNzhiYzI5M2EyZDA4MTkxODM5ZWQxYmExNjM2MGQ0Yg`,
checkout `/workspace/solidity-lean`, ignored dirs:
`tests/fullscope-20261104/vt1/ImportFollowup/{evidence,seal}/`,
`tests/calldata-packets-1105/RawBool/{evidence,seal}/` and
`tests/calldata-packets-1105/RawBool/PinFollowup/{evidence,seal}/` (latest seal
`.../PinFollowup/seal/70845978.../{HANDOFF.md,SHA256SUMS}`, SHA256SUMS sha256
209cd75cbec01f4c62a76e508b72f34e7fb64d84ce35854c7cff4dfcc4fb1636).
Claude VMs cannot reach them: re-run validation fresh instead of citing these seals.

## Remaining queue
T01 (partial). Done: object-dialect operation syntax interface (`Dialect`, reusing
the owner's arity-indexed builtins; string literals as metadata), checked
object-data references into assembled bytes (`DataLayout`), unique label
resolution (`DataResolution`), exact `--ir`/`--ir-optimized` channel extraction
from solc JSON with full-path lookup completeness and 22 kernel controls
(`IrImport*`), real-solc channel fixtures (IR_CHANNEL_FIXTURES_PASS4). Open:
- Yul text parsing of imported IR with parser provenance (the Lean `Json.parse` is
  partial: only external tests so far), canonical nested object names, object
  assembly/serialization;
- interpretation of the full dialect on the core Yul semantics via new adapters:
  remaining builtins, `datasize`/`dataoffset`/`datacopy` execution,
  `setimmutable`/`loadimmutable` and immutable/linker layout, `linkersymbol`,
  `memoryguard`, objects; memory/gas/resource composition;
- the final check needs VX4's physical byte-memory view (X06), not yet launched.
- publish concrete dialect/import interfaces as path@commit handoffs for VT2/VT3.
T02 (not begun): unoptimized via-IR matcher for each `fun_<name>_<id>` and helper
(`checked_add_*`, `abi_decode_*`, `array_push_*` ...) against `Stmt`/runtime
definitions, per-function simulation proofs, per-contract dispatcher/constructor
composition using X01/G01 relations; generalizes `Evm/Signed.lean`, `Evm/Exp.lean`
by adapters (do not edit those). T02 relations wait for X01's frozen G01 relations
(VX1 stub 06f5ae081 is unfrozen; do not prove against it as final).
Backfill: more pinned real solc 0.8.38 output fixtures, helper/dialect census,
malformed/altered/rejected-input controls, inhabited matches, parser provenance.
Coordinator-owned registration still requested: theorem inventory for
`IrImportControls` (module is registered); RawBool registration requests.
Pending cache request: source-hashed .olean closure for
`Solidity.Backend.Environment.ByteConstants` (Codex-VM specific; ignore on Claude VM).

## Producers this lane waits on
- X01 / VX1 (G01 relations, D1-D6): idle, goal blocked, no frozen stub.
- VX4 / X06 physical byte-memory view: wave B, not launched.
Parsing, dialect interpretation adapters, fixtures and controls are independent;
final T01/T02 closure is not, so the lane stays partial until they integrate.

## Interfaces and owners
Exclusive writes: `Solidity/SolcValidation/**`, `Solidity/Frontend/SolcJson/Ir*`,
`tests/fullscope-20261104/vt1/**`, `docs/feature-work/fullscope-vt1.md`. Do not edit
VY1/VY2/VY3/VY4-owned Yul modules, H16 Source (VY5), SolcJson producer files
outside `Ir*`, `Evm/Signed.lean`, `Evm/Exp.lean`, Core ExtCall, generated roots,
module-map fragments or trust pins; request owner changes and consume committed
stubs.

## Gates
- Lean MCP diagnostics clean on every touched file; `./run-lean.sh` for focused
  targets; `#print axioms` for headline theorems; real pinned solc 0.8.38 fixtures
  (record the solc binary hash); negative/altered-input controls.
- Separate read-only finder and skeptic reviews per checkpoint, neither using the
  Lean server; record fixes in the feature doc.

## Exclusions
No sorry/axioms/unallowed native_decide, no maxHeartbeats or budget increase, no
theorem/premise/exclusion weakening; unmatched steps are open work, never
exclusions. Codex-only tooling (`ImportFollowup/{run.py,run.sh,server.sh,
lake.serial.toml,bin/lake}`, Docker envelope, H35/H41 cache packets) need not be
reused or extended.

## Original assignment (Codex prompt; replace Codex-specific tooling with the preamble's rules)
You are the Codex Cloud worker for batch "solidity-fullscope-20261104", task "vt1-solc-validation": VT1 T01, T02 full scope.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-fullscope-20261104/vt1-solc-validation` from that exact commit;
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
  "batch": "solidity-fullscope-20261104", "slug": "vt1-solc-validation", "status": "done | partial | blocked",
  "branch": "codex/solidity-fullscope-20261104/vt1-solc-validation", "base": "e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3", "head": "<full committed SHA>",
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

AUTHORIZED H37 full-scope wave A; batch solidity-fullscope-20261104; model gpt-6.1-sol. Pinned base e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3 = freshly fetched origin/master. This is concrete implementation/proof work, not an audit-only assignment. Use your same attached VM and isolated branch; goal owns continuation, never create/reset a VM or goal. Freeze an interface before dependent implementation. Coordinator ownership reservations precede dispatch; usual merge job owns integration, no new publication authority.
Read AGENTS.md, docs/module-map.md, docs/README.md, docs/intrinsic.md Gate G0 and matching area conventions before changes. Keep core dependency-free and types intrinsic; local acyclic imports. Never weaken theorem statements, premises, observations, exclusions or expected verdicts, add axioms/sorry/sorryAx, unallowed native_decide, or raise maxHeartbeats. Warn and inspect git log before a slowdown-risk refactor; measure before/after. Approved full scope withdraws all language exclusions; a proof limit/refusal is open work.
Do NOT edit H16 Source modules (VY5 exclusive), Core ExtCall/Solidity/Syntax/Scoped.lean while H22 frozen, or any other lane's files. Evm compiler/backend/storage/memory, Yul core/World/Views/Compilation/Composition and existing frontend producers retain their owners. Request a relayed change from the exact owner through coordinator CLOUDVM-RESULT; never write the owner's stub or interface. Coordinator answers paths/commit/owner/already-master lookups. Generated library roots, area module maps and trust pins remain COORD: use registration tooling to prepare a per-lane registration/map proposal for central serialized integration; do not co-edit them. X01 alone owns the explicitly listed feature catalog outputs.
H35: run build, axiom inventory, semantic/negative controls and all checkpoint gates ON THE VM, and ship-cache (scripts/coord-tools/ship-cache.sh / installed coord toolkit, preserving source/toolchain/checksums) BEFORE reporting checkpoint readiness. Cache export failure is not PASS; send its exact repairable blocker. One heavy Lean check at a time, LEAN_NUM_THREADS=1, -j1, enforce <=12 GiB/no swap with observed aggregate RSS, 4 GiB free-RAM admission reserve. Outer16GiB alone is not an adequate Lean scope. Verify actual Lean/Lake versions and allowed KeySort gate before RUNTIME_GATE_PASS; prefer MCP per-file diagnostics and ./run-lean.sh, do not bypass blocked bare Lean/Lake policy. VM resource envelope must be measured, not inferred from active status. 300s per proof/group, 14400s aggregate build window; one additional serial prerequisite <=180s per checkpoint allowed, otherwise split. Never lift guard. Reuse/ship existing caches before prerequisite rebuilds. H1 allows own regenerable disk cleanup preserving commits/latest seals/checksums; capacity/offline: request reattach of SAME executor, retain uncertain receipts, retry after 600s; no replacement. Missing historical evidence is UNVERIFIABLE, never reconstructed. Standard axioms/propext/Classical.choice/Quot.sound and already-pinned Lean.ofReduceBool are coordinator re-pin work; new axioms/sorry/unallowed native_decide block.
Every milestone has separate read-only finder and skeptic reviews, neither using Lean server; fix findings and record them in the lane feature doc. Short commits with no author text. Keep checkpoint handoffs separately reviewable; no merge/push to master. Preserve original base/head/branch, exact theorem signatures/premises, command/exit/wall/RSS logs, controls, reviews, hashed sealed artifacts and shipped caches. Distinguish source complete, kernel checked, compiler/EVM evidence, dependencies pending and integrated/published.
End every turn CLOUDVM-RESULT JSON (questions=[] if none) including queue accounting, gates, reviews, artifacts/checksums, limitations, ownerRequests and stubReady path@commit/signatures/consumers. A stubReady is an immediate coordinator relay request to all relevant original lane threads; retain it until relay receipt. No claim that a stub is proof of its contract. Human-only design/scope or producer interface changes: ESCALATE line with 2–3 options; D1–D6 are already approved, X01 freezes them.

Exclusive writes: Solidity/SolcValidation/**; Solidity/Frontend/SolcJson/Ir*; tests/fullscope-20261104/vt1/**; docs/feature-work/fullscope-vt1.md

## Work queue (in order)
1. T01 implement the full solc 0.8.38 EVM Yul dialect and --ir/--ir-optimized import in the reserved paths. Extend via new adapters over the core Yul semantics; do not edit VY1/VY2/VY3/VY4-owned Yul modules, Source or SolcJson producer files outside Ir*. Request exact owner changes and consume their committed stubs.
2. T01 publish concrete dialect/import interfaces as committed path@commit handoffs for VT2/VT3; VX4 physical byte-memory view is required for the final check. Prepare against frozen interfaces; missing interface waits for owner. Full dialect includes builtins, datasize/dataoffset/datacopy, setimmutable/loadimmutable, linkersymbol, memoryguard, objects.
3. T02 match unoptimized via-IR fun_<name>_<id> and helpers (checked_add_*, abi_decode_*, array_push_*, etc.) to intrinsic Stmt/runtime definitions; produce per-function simulation proofs and per-contract dispatcher/constructor composition using X01/G01 relations. Generalize by adapters, without co-editing Evm/Signed.lean or Evm/Exp.lean.
Backfill within scope: pinned real solc output fixtures, helper/dialect census, malformed/altered/rejected-input controls, inhabited matches, parser provenance tests. Do not claim final T01/T02 closure before VX4 and G01 dependencies integrate; name unmatched steps as open work, never exclusions.

## Group deliverables verbatim
| T01 | **solc's Yul dialect.** The full EVM Yul dialect solc emits (builtins, `datasize`/`dataoffset`/`datacopy`, `setimmutable`/`loadimmutable`, `linkersymbol`, `memoryguard`, objects) on the core Yul semantics, pinned to 0.8.38; import of `--ir` and `--ir-optimized` output. | `Yul/`, X06 memory view |
| T02 | **IR matcher.** Unoptimized via-IR Yul against the source: match each `fun_<name>_<id>` and helper (`checked_add_*`, `abi_decode_*`, `array_push_*` …) to its `Stmt`/runtime definition, emit a simulation proof per function, then per contract (dispatcher, constructor). Generalizes `Evm/Signed.lean` and `Evm/Exp.lean`. | T01, G01 relations |

## Approved D1–D6

Proposed with the plan; X01 freezes them in G01's contracts before the X lanes
pass their final checks.

- **D1 — compiler-dependent values.** `gasleft()`, `gas`, `msize`, `pc`, own
  `codesize`/`codecopy` and `type(C).creationCode`/`runtimeCode` read the
  compiled artifact. The source semantics takes the artifact table as a
  parameter (the G00 Q5 pattern, extended), plus a gas oracle the target
  execution supplies. The non-circularity whitelist of G07 records why this is
  not defining the source by the compiler. Supersedes G06 D6 and YQ2.
- **D2 — exact gas.** The pinned EVM semantics charges the Osaka schedule
  exactly (memory expansion, warm/cold access, refunds, the 63/64 rule,
  stipends). Gas exhaustion stays a failure the source allows; gas *values*
  become observations through D1. Code-size limits (EIP-170, EIP-3860) are
  modelled as creation failures, replacing the G01 Q2 idealization.
- **D3 — solc's physical layout.** Storage and transient slots, packing, `layout
  at`, and memory (scratch `0x00`–`0x3f`, free-memory pointer `0x40`, zero slot
  `0x60`) follow solc's documentation, so raw observations agree with solc.
  This compiler's representation must agree with it (G27, G32, Y04, Y05);
  the word-cell machine of `Solidity/Evm/Machine.lean` is refined by a byte
  memory before X lanes close.
- **D4 — non-memory-safe assembly.** Admitted. The memory view loses the
  `MemOK` guarantee inside such a block and recovers it only through a proved
  writeback; the optimizer treats the block as opaque (as solc does).
- **D5 — premises that stay.** Only cryptographic and chain premises remain:
  the per-run hash non-collision premise (G01 Q3), the approved crypto
  functions, and environment inputs universally quantified. These are not
  language exclusions.
- **D6 — optimizer correctness relation.** Passes preserve every observation
  except gas values; with D1, a program that reads gas is related to the
  artifact the optimizer actually produced, so the public theorem stays exact.
  Gas improvement is measured (benchmarks), and proved only where a pass
  carries a cost lemma.


## VM execution contract verbatim

The schedule is **18 lanes** (see [VM assignments](#vm-assignments-revised-2026-10-29)),
each on an isolated **16 GiB VM** for **eight to ten hours including
validation**, with one branch/worktree and a reviewable patch per
checkpoint. The 118 proof work packages below are checkpoints within
those assignments, **not 118 separate VM launches**. An assignment performs
its checkpoints sequentially, reusing the environment, caches and context.

These are unmeasured allocation estimates, not a guarantee that an open research
proof finishes within ten hours. G02 calibrates costs before the implementation
launches; the first batches' measurements are in the sizing rules below. Rebalance checkpoints between assignments when measurements support it;
add a continuation assignment only for actual unfinished work. Keep all theorem
obligations open until integrated. Splitting a proof into smaller lemmas does
not automatically allocate another VM. Never replace an unfinished deliverable
with a refusal, a new exclusion or a promise of a later proof.

- Start with `LEAN_NUM_THREADS=1`, explicit `-j1`, a process-group
  `MemoryMax=12G` and `MemorySwapMax=0`; leave the remaining RAM for the OS.
  Use disk-backed private caches, monitor aggregate RSS and available memory,
  and stop before exhausting the VM. Run Lean MCP or a build, not both.
- A cold build is a prerequisite to measure, not a free operation hidden in
  every estimate. Publish a reproducible dependency cache with source/toolchain
  identities; if clean validation exceeds one timebox, split validation targets
  into VM groups and check their final joint import closure.
- Use [module-map.md](module-map.md), the feature's `localEvidence` and current
  source before editing. Reproduce current behavior and audit existing proofs;
  do not rebuild integrated foundations. Follow [intrinsic.md](intrinsic.md),
  [parallelism.md](parallelism.md) and the matching repository conventions.
- Freeze shared interfaces in G01. Same-wave groups may run concurrently only
  where their writes and proof interfaces are independent. Record ownership of
  shared files; serialize shared edits and integration. A local shared checkout
  also requires the [writer lock](refactoring-progress.md#resource-bounds-and-resuming-work).
- Every group delivers its specified artifact, checks and updated
  coverage/proof ledger. Implementation groups additionally deliver code,
  kernel-checked proofs, inhabited nontrivial witnesses, relevant negative
  controls and feature-combination regressions; audit/measurement groups deliver
  reproducible evidence rather than invented implementation theorems. No `maxHeartbeats` rescue, new axioms, weakened
  observations, changed expected verdicts or extra profile restrictions.
- Handoff: base/patch revision, feature IDs/source constructors, new theorem
  names and exact premises, dependencies, before/after fixtures, checks, audit
  results, elapsed time/peak RSS, and every remaining child obligation. Resource
  stops and timeouts remain open work.
- After each milestone, perform separate read-only finder and skeptic reviews,
  neither using the Lean server. Record and fix confirmed findings in the
  owning feature document. Rebase dependent work on integrated prerequisites;
  the coordinator validates the combined imports and proofs before pushing.


## Sizing rules verbatim

- **Fill eight to ten hours.** A lane holds enough checkpoints for eight to
  ten hours of work, including validation — in practice three or four of the
  old roadmap groups, a whole dependency chain rather than one link of it.
  Every lane contains implementation checkpoints with kernel-checked proofs.
- **No lone audits.** An audit, specification or measurement never gets its
  own VM. It becomes the first checkpoint of the lane that consumes its
  result.
- **Keep going.** When a checkpoint is finished (gates pass, finder/skeptic
  reviews applied, pushed to the lane branch), the VM starts the next
  checkpoint in its queue on the same branch, reusing the build cache. It
  stops only when:
  - the queue and the backfill queue are empty;
  - every remaining item needs an unmerged prerequisite from another lane;
  - about ten hours are spent;
  - or a resource limit stops it.
- **Backfill before stopping.** A blocked or empty lane takes the next ready
  item from the [backfill queue](#backfill-queue) before it stops.
- **One cold build per lane.** The cold build is paid once. Later
  checkpoints use per-file Lean server diagnostics and warm rebuilds.
- **Handoff per checkpoint.** Each checkpoint records its own handoff
  (revision, theorems, premises, checks, remaining obligations) in its
  feature document, so the coordinator can integrate a lane in parts.
- **Fewer, longer lanes.** Prefer one lane that runs a dependency chain end
  to end over several lanes that wait on each other; parallel lanes are for
  independent chains.

