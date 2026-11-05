# Moved lane: vy5-composition (from a Codex VM)

The user decided (2026-11-05, H37) to move this lane to a Claude VM with the same
branch content and scope, keeping H16 Source ownership. Start by `git fetch origin
cloud/vy5-move` and continuing from that head (5209dc72), merging current
origin/master into it first. Push to your session branch only.

Immediate blockers, from the coordinator:
- The 2026-11-05 merge skipped this lane: touched gate failed. Details below.
- Monetary.wide blocks the lane's checkpoint; resolve it first.

## Gate failure relay
Gate failure (scheduled merge 2026-11-05 12:52, base master 85c4dc24): your checkpoint was skipped at "touched gate failed". Log: receipts/sched-20261105T1200Z/lanes/vy5-composition/touched/1.log.
Failing check: build-touched, module Solidity/Yul/Composition/MonetaryLifecycleControls.lean.
- 25:58 Unknown identifier `Monetary.wide` (not on master). The follow-on errors come from it: 29:68 rfl on destructTransfer wideState = none, 34:12 HPow Nat Nat Roadmap.Word, and the #guard_msgs/Unknown constant errors for old_self_keeps_exact_wide, fresh_self_burns_exact_wide, wide_distinct_refused.
Fix needed: you own H16 Source, so commit the Source `Monetary.wide` definition in this checkpoint, ordered before the controls module and registered in Solidity.lean. If it stays under the existing hold, leave MonetaryLifecycleControls out of the checkpoint. At 34:12, add a type annotation to the numeral (for example `(2 ^ 256 : Nat)`) so that no HPow into Word is needed. Do not change the statements of the controls. Rerun `scripts/coord-tools/gate.sh touched` on fresh origin/master (-j1), then seal and report the head in CLOUDVM-RESULT.

## Original assignment (Codex prompt; replace Codex-specific tooling with the preamble's rules)
You are the Codex Cloud worker for batch "solidity-inline-assembly5-20261031", task "vy5-composition": VY5: assembly composition proofs and differential tests.
Other workers use their own VMs. The local coordinator audits your saved task;
you do not need to message it or create empty result-marker commits.

- Starting commit: 0b078cefaf7daad79007b87b72df64eb6936420f. Before editing, inspect the actual checkout and
  repository instructions. Use branch `codex/solidity-inline-assembly5-20261031/vy5-composition` from that exact commit;
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
  "batch": "solidity-inline-assembly5-20261031", "slug": "vy5-composition", "status": "done | partial | blocked",
  "branch": "codex/solidity-inline-assembly5-20261031/vy5-composition", "base": "0b078cefaf7daad79007b87b72df64eb6936420f", "head": "<full committed SHA>",
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

Implement the assigned inline-assembly lane from Claude's proposal at base 0b078cefaf7daad79007b87b72df64eb6936420f.
The explicit human authorization below supersedes the proposal's pending YQ1–YQ7 status, but does not waive dependency gates. The base still contains the original proposal: record the approved decisions in docs/solidity-scope.md (preserve earlier decisions) and cite them in your handoff. Never treat an authorized feature as already supported.

## Inline assembly decisions (2026-10-31)

The human requested one CloudVM per lane VY1–VY5 to solve the inline assembly
extension, reopening assembly through tiers A–C. The coordinator asked:

> For all five assembly lanes, approve these proposed semantics: refuse gas/msize/pc and own-code inspection; allow nondeterministic valid allocation addresses with a refinement theorem; preserve dirty high bits as solc does in each pipeline; mark Yul calculus rules as Lean-only; expose both Yul logs and Solidity emit as observations; and refuse non-memory-safe assembly blocks? Your request covers reopening assembly through tiers A–C.

The human answered exactly:

> Approve these choices for all five lanes

- YQ1: authorize tiers A–C through all five lanes.
- YQ2: keep gas/msize/pc and own-code codesize/codecopy refused at admission.
- YQ3: nondeterministic allocation addresses satisfying documented layout;
  prove refinement and amend G01's contract explicitly.
- YQ4: preserve dirty high bits according to solc in each pipeline; record
  pipeline differences rather than silently cleaning or refusing them.
- YQ5: accept Lean-only Yul rules, explicitly marked in the rule map.
- YQ6: expose Yul logs and Solidity emit together as observations; amend G01.
- YQ7: refuse non-memory-safe blocks. Preserve the existing canonical rethrow
  behavior as the documented pre-existing exception.

These are implementation directions, not evidence of implemented support. The
current manifest continues to report actual admission; affected exclusion rows
are reopened only by reviewed implementation with its evidence and decision
reference. Compiler-dependent observations remain excluded. Dependency gates,
existing worker ownership and validation still apply. This request does not
authorize merging or pushing this new batch.


## Shared execution and ownership contract
- Use the actual attached Codex executor in environment solidity-lean; discover its checkout/toolchain/tools. Read AGENTS.md, docs/module-map.md, docs/README.md, docs/coverage-plan.md VM execution contract, docs/intrinsic.md Gate G0, docs/parallelism.md, docs/contributing.md and the matching rule/typing/soundness/derivation conventions. Read docs/solidity-upstream-tests.md and the local evidence before implementing. Inspect git log before representation changes; warn if checking may slow.
- All new ASTs, terms, formulas, statements, states and values remain intrinsic. Index Yul variables by context and functions by arity. No untyped intermediate representation, axioms, sorry/admit, weakened theorem premises/observations, changed expected verdicts, raised proof budgets or renamed residual fragment predicate to claim coverage. Parameterized preparation laws must state their real premises and never substitute for concrete final composition proofs. Core remains dependency-free; external EVMYulLean adapters only in Bridge/.
- Heavy checks run serially, LEAN_NUM_THREADS=1 and explicit -j1, enforced 12 GiB process-group/cgroup memory limit, no swap, actual VM OS headroom and aggregate RSS/disk monitoring. Do not impose a second 12 GiB OS reservation on a 16 GiB VM. Use disk caches, per-file Lean MCP when present, never simultaneous MCP/build. Respect the repository's build policy and writer lock. For the required lake build Solidity.KeySort use ./run-lean.sh where policy requires it; preserve exact command/output, actual Lean and Lake versions and exit 0 before RUNTIME_GATE_PASS. No fabricated gate markers. Discover a supported hard bound (systemd/cgroup/container), or report the gate blocked.
- Current local catalogs/live reads show V07–V17 have existing independent VMs. V04b remains owned by Claude roadmap-l3 lane-soundness. Existing source/type/lexer/checker, G24–G55 compiler passes and EVM/Bridge/legacy TestSuite component owners are read-only prerequisites. Existing V10/V11 storage/memory jobs already started: your Y04/Y05 agreement obligations must be explicit inputs, never replace their layouts silently. Do not redo or repair any paused/blocked/restricted legacy assignment, particularly function-ref-args or abi-lazy-calldata. New assembly work is confined to new Yul namespaces/adapters/tests and narrow append-only registrations. If a shared definition must change, prepare an isolated reviewed amendment and report owner/dependency; do not concurrently rewrite the existing implementation. No messaging other chats, no pushing, PR, master merge or integration of other worker branches.
- Within this batch: VY1 owns intrinsic Yul Syntax/Static/Words and pure calculus; VY2 owns Yul physical Views/Inputs and physical calculus; VY3 owns Yul compilation/correspondence adapters; VY4 owns Yul world effects and effect calculus; VY5 owns Yul composition/differential harness and coverage ledger. Shared files (Solidity.lean, frontend dispatch, rule map, scope and this feature doc) get minimum lane-specific append-only changes; coordinate via explicit dependency contracts, not duplicate definitions. VY1 records authorization; each branch may carry the identical decision record until combined integration. VY2 owns allocation G01 amendment and VY4 owns log/emit G01 amendment in separate extension modules/docs for eventual joint review.
- One VM per lane is authorized now, including dependency preparation. Implement independent backfill while a prerequisite is missing. Do not claim final lane completion until its concrete prerequisites and full kernel/import/composition gates exist in the validated tree. Record every missing prerequisite, including V04/V04b, V12/V13/V15/V16 as applicable. Do not wait idly when assigned backfill remains, or fabricate stub prerequisites. Goal stays unfinished for remaining original work.
- Read current source and establish before/after controls. At base, Solidity/Frontend/SolcJson/Body.lean InlineAssembly branch accepts only memoryRethrow? then emits its canonical rethrow; docs/solidity-features.json inlineAssembly row is excluded with no localEvidence. Preserve valid rethrow semantics and negative shape/declaration controls during generalization. Use pinned solc 0.8.38 commit 1835d247de183f23e7b0e2bc4a50732af525b77c and Osaka; retain evidence of upstream files/fixtures and both legacy/via-IR pipelines. Kernel proofs and external compiler/EVM tests must be reported separately.
- Each checkpoint requires inhabited nontrivial witnesses, refusal/negative controls, feature-combination regressions, exact theorem signatures/premises and scoped axiom reports. Import new modules through correct acyclic local layers/Solidity.lean when ready; final joint import closure is required. Per-file diagnostics after edits, focused tests and bounded affected/full builds appropriate to imports; docs paths/links and no-new-findings against the exact base. Preserve raw baseline failures instead of relabeling them passes.
- After each milestone, use separate independent read-only finder and skeptic reviews per area, neither using the Lean server; fix confirmed findings and record them in your lane document. This explicitly authorizes those review subagents. No concurrent heavy Lean work.
- Commit reviewable checkpoints on the assigned codex branch, with very short commit messages. Update a lane-owned docs/feature-work/inline-assembly-vyN.md, append a handoff to the parent feature doc, and minimally register it in docs/README.md. Include queue and backfill accounting, full base/head/branch, theorem premises, concrete versus conditional proofs, checks and resources, reviews, pending dependencies/decisions, exact artifact paths, patch/git bundle and SHA256 checksums. Finish with the required CLOUDVM-RESULT JSON. A bounded checkpoint does not finish the full lane. A fresh eight-to-ten-hour useful-work queue is guidance, never a completion criterion.

## Authoritative proposal snapshot at the pinned base
# Inline assembly (Yul): proposed extension

Status (2026-10-31): **proposal, not started.** `inlineAssembly` is an approved
exclusion ([G00 Q1](../solidity-scope.md#user-decisions-2026-10-29)); only the
whole-buffer rethrow `assembly { revert(add(data,32), mload(data)) }` is
recognized (`canonicalRethrow`, `memoryRethrow?` in
`Solidity/Frontend/SolcJson/Body.lean`). This document plans the groups and
lanes that would cover inline assembly. **No lane starts before the user
answers the [decisions](#decisions-needed-before-any-lane) and they are recorded
in [solidity-scope.md](../solidity-scope.md).** A worker must not reopen an
exclusion or change a manifest status on its own.

Pinned references (solc 0.8.38, commit `1835d247de183f23e7b0e2bc4a50732af525b77c`):
`docs/assembly.rst`, `docs/yul.rst`, `docs/internals/layout_in_storage.rst`,
`docs/internals/layout_in_memory.rst`, the Yul rules of
`docs/grammar/SolidityParser.g4` (from line 520), `libyul/AsmAnalysis.cpp`,
`libsolidity/analysis/ReferencesResolver.cpp` and the
`test/libsolidity/semanticTests/inlineAssembly/` corpus
([solidity-upstream-tests.md](../solidity-upstream-tests.md)).

## What exists

- `Solidity/Backend/Opcode.lean`: the full Osaka opcode set, byte encoder and
  decoder, jump-destination analysis and vectors
  ([backend-assembler.md](backend-assembler.md)).
- `Solidity/Evm/Machine.lean`: the compiler's target machine, 46 instructions
  with word-cell memory (G06 disagreement D2).
- `Solidity/Storage/Hashed*.lean`: the hashed storage layout and its
  separation ([storage-hashed-layout.md](storage-hashed-layout.md)); value
  representation, widths and packing remain (G27.05).
- `Solidity/Source/State.lean`: logical source state (S04), storage typed by its
  layout, logical transient roots ([transient-storage.md](transient-storage.md)).
- `Solidity/Evm/Signed.lean`, `Solidity/Evm/Exp.lean`: word arithmetic.
- `Bridge/SolidityBridge/ExternalEvm/`: projected opcode agreements with
  EVMYulLean (M6 in [roadmap-g06-evm.md](roadmap-g06-evm.md)).
- SolKey has no assembly support: no taclet exists to mirror.

## Exclusions it reopens

Yul builtins reach most of the 30 approved exclusions in
`docs/solidity-features.json`:

| Builtins | Excluded rows | Tier |
|---|---|---|
| `mload`, `mstore`, `mstore8`, `mcopy`, free-memory pointer | `memoryLayout` | B |
| `sload`, `sstore`, `x.slot`, `x.offset` | `storageLayout` | B |
| `tload`, `tstore` | `transientLayout` | B |
| `calldataload`, `calldatasize`, `calldatacopy` | `rawCalldata` | B |
| `returndatasize`, `returndatacopy` | `rawReturndata` | C |
| `call`, `staticcall`, `delegatecall` | `lowLevelCall`, `lowLevelStaticcall`, `delegatecall` | C |
| `create`, `create2`, `selfdestruct`, `extcodesize`, `extcodecopy`, `extcodehash` | `create2Salt`, `selfdestruct`, `addressCode`, `addressCodehash` | C |
| `log0`–`log4` | `eventLog` | C |
| `coinbase`, `number`, `timestamp`, `prevrandao`, `gaslimit`, `chainid`, `basefee`, `blobbasefee`, `blockhash`, `blobhash`, `origin`, `gasprice` | the 13 block/tx rows | B |
| `gas`, `msize`, `pc`, own `codesize`/`codecopy` | `gasleft`, `machineResources` | stays excluded |

The last row returns values that depend on how the program was compiled, so it
has no compiler-independent source meaning (and contradicts G06 decision D6:
gas is a resource, never an observation). Admission refuses an assembly block
that uses one of them, with a precise reason.

## Tiers

- **Tier A — words only.** Yul control flow, functions and the pure builtins
  (`add` … `clz`, `byte`, `signextend`, `addmod`, `mulmod`, `exp`) over Yul
  locals and Solidity value-type locals. Covers `mulDiv`-style helpers. Needs
  only the `inlineAssembly` row reopened for this subset.
- **Tier B — physical state.** Adds storage, transient, memory, calldata,
  `keccak256` and environment reads. The source state gains physical views of
  its logical state.
- **Tier C — full Yul** minus the compiler-dependent row: raw calls,
  creation, logs, returndata, `selfdestruct`.

## Design constraints

- **Intrinsic.** The Yul AST is typed: variables are indexed by their scope
  context, functions by their argument and result counts, so out-of-scope
  references and arity errors are unrepresentable. No untyped intermediate
  layer ([intrinsic.md](../intrinsic.md), Gate G0). Yul has one type (`u256`),
  so a Yul value is the existing EVM word type.
- **Core stays dependency-free.** EVMYulLean agreement only in `Bridge/`.
- **Physical views are derived, not stored.** The logical state remains the
  source state. A physical view (slot map, byte memory) is a function of it
  through the documented layout, plus a residual part for locations outside
  every logical region (an assembly block can write a slot no declaration
  owns and read it back later). Writeback decodes the view back into logical
  state. Adding the residual part changes the state type: run Gate G0 and
  check `git log` for speed-motivated state changes first.
- **The source layout follows solc's documentation**, not the compiler of this
  repository. The compiler groups (G27, G32) then prove their representation
  agrees with it. So Y04/Y05 must be integrated before lanes V10/V11 start,
  or those lanes take Y04/Y05's layout definitions as an input obligation.
- **Notation.** Rules use `dl{ … }` / `tm{ … }` with printers. Every Yul rule
  gets a row in [lean-key-rule-map.md](../lean-key-rule-map.md) marked as a
  Lean-only extension without a SolKey taclet (decision YQ5).

## Groups

Each group follows the [VM execution contract](../coverage-plan.md#vm-execution-contract):
code, kernel-checked proofs, inhabited witnesses, negative controls,
combination regressions, finder/skeptic review, handoff in this document.

| Group | Deliverable | Depends on |
|---|---|---|
| Y01 | **Yul syntax and admission.** Intrinsic Yul AST (`Solidity/Yul/Syntax.lean`); import of solc JSON `InlineAssembly` (`AST`, `externalReferences`, `flags`, the `memory-safe-assembly` doc comment) in `Solidity/Frontend/SolcJson/Yul.lean`; builtin table pinned to Osaka and solc 0.8.38; admission per tier with precise refusals, including the compiler-dependent builtins; `canonicalRethrow` becomes an instance, not a special case. Checked Yul parsing over the G08–G11 lexer is child Y01.02. | S00, existing SolcJson frontend |
| Y02 | **Yul static semantics.** Scoping (functions visible in their whole block, no shadowing, function bodies see no outer variables), `leave`/`break`/`continue` placement, literal ranges; external references: value-type locals, `x.slot`/`x.offset` of storage references, `x.offset`/`x.length` of calldata, memory variables as pointers, `f.selector`/`f.address`. Checker sound and complete against the typing relation; solc's error tests as refusal controls. | Y01, S01 |
| Y03 | **Word semantics.** Statements, functions and pure builtins over words with EVM results (`div`/`mod` by zero is `0`, no Panic); fuelled divergence matching S03's horizons; embedding into S02/S03 statements. Solidity locals written from assembly with dirty high bits follow decision YQ4. | Y02, S02, S03 |
| Y04 | **Storage and transient views.** Physical slot map of persistent and transient storage from `Solidity/Storage/HashedLayout.lean` plus value packing and widths (the source half of G27.01–G27.05); residual slots; writeback; `sload`/`sstore`/`tload`/`tstore` with reset at transaction end and frame rollback (EIP-1153). Laws: decode∘encode = id; writeback of an unchanged view is the identity. | Y03, S04 |
| Y05 | **Memory view.** Byte memory from the documented memory layout (scratch `0x00`–`0x3f`, free-memory pointer `0x40`, zero slot `0x60`, length-prefixed arrays, word-per-member structs); `mload`/`mstore`/`mstore8`/`mcopy`; the `memory-safe` contract; allocation addresses per decision YQ3. Laws: logical memory reads agree with the view; memory-safe blocks preserve `MemOK` (V04b). | Y03, S04, V04b `MemOK` |
| Y06 | **Inputs and hashing.** `calldataload`/`calldatasize`/`calldatacopy` over the transaction's calldata bytes; `keccak256` over memory with the approved `Fixed` hash; environment builtins as universally quantified inputs (G00 Q2), which also reopens the Solidity `block.*`/`tx.*` rows. | Y05, S04.04 |
| Y07 | **World effects.** Y07.01: `call`/`staticcall` with raw bytes to known and environment callees, `returndatasize`/`returndatacopy` (the buffer of the last source-level frame; the compiler must not issue other calls), `create`/`create2` with raw initcode and the address formula. Y07.02: `delegatecall` (known callee: its code over the caller's storage; environment callee: storage havoc), `selfdestruct` under EIP-6780, `log0`–`log4` as observations (changes G01's event type; YQ6). `callcode` refused. | Y06, G22, G42 |
| Y08 | **Compilation.** Y08.01: Yul to the compiler's instructions with stack slots for Yul variables and frames for Yul functions; correctness against G24's state relation and the Y04/Y05 views. Y08.02: EVM correspondence of the new opcodes through G45/G46 and the Bridge (B05 rows). | Y04–Y06, G24, G27, G32, G45, G46 |
| Y09 | **Calculus.** Y09.01 rules for Y03; Y09.02 rules for Y04–Y06 (slot and byte terms with `save`/`find`-style update laws); Y09.03 rules for Y07. Soundness for each, rule-map rows, printed rules. | Y03–Y07, G51 interfaces |
| Y10 | **Composition and testing.** G03 ledger rows and combinations (assembly in loops, modifiers, `try`, `unchecked`, constructors, libraries); G48–G51 coverage with no residual assembly fragment predicate; G52 differential tests against solc 0.8.38 in both pipelines over the upstream `inlineAssembly` corpus. | Y01–Y09, V16 |

## Lanes

Sized by the [sizing rules](../coverage-plan.md#sizing-rules): three or four
groups, eight to ten hours each.

| Lane | Checkpoints, in order | Starts after | Tier |
|---|---|---|---|
| VY1 | Y01, Y02, Y03, Y09.01 | YQ1–YQ5 answered; V04 integrated | A |
| VY2 | Y04, Y05, Y06, Y09.02 | VY1; before V10/V11 start | B |
| VY3 | Y08.01, Y08.02 | V12 (Y08.01), V15 (Y08.02); backfill until then | B |
| VY4 | Y07.01, Y07.02, Y09.03 | VY2, V13 (G42); YQ6 answered | C |
| VY5 | Y10 | V16, VY3, VY4 | C |

Tier A is one lane, independent of the main chain. Tier B adds two, tier C
two more. VY2's layout definitions feed V10 (G27) and V11 (G32): if those
lanes start first, add "agrees with Y04/Y05's layout" to their checkpoints.
G27, G32, G46 and G47 grow by the corresponding opcode and view obligations;
that growth is counted in VY3/VY4, not in V10–V15.

## Decisions needed before any lane

| ID | Question | Recommendation |
|---|---|---|
| YQ1 | Reopen `inlineAssembly`, and which tier? | Tier A now; tiers B and C as separate decisions after VY1. |
| YQ2 | Keep `gas`, `msize`, `pc` and own-code `codesize`/`codecopy` excluded? | Yes: refuse at admission. |
| YQ3 | Memory pointer values depend on allocation order, which differs between pipelines. Make allocation addresses nondeterministic in the source (any choice satisfying the documented layout) with the final theorem a refinement, or fix one allocation discipline? | Nondeterministic with a refinement theorem; needs a G01 contract amendment. |
| YQ4 | A Solidity `uint8` local written from assembly with dirty high bits: model the bits, clean on write, or fail? | Model them exactly as solc does in each pipeline; record any pipeline difference in [solc-alignment.md](../solc-alignment.md). |
| YQ5 | Yul rules have no SolKey taclet. Accept Lean-only rules marked in the rule map? | Yes, marked; reconsider if SolKey gains assembly. |
| YQ6 | Logs become observations (tier C): extend G01's event type for Solidity `emit` too? | Yes, both at once, or tier C keeps `log*` refused. |
| YQ7 | Non-`memory-safe` blocks? | Refuse: via-IR's stack-to-memory mover depends on the flag. |

## Handoffs

None yet. Each checkpoint appends its handoff here (revision, theorems and
premises, checks, remaining obligations).


## Assigned lane VY5

Own Y10. Use docs/feature-work/inline-assembly-vy5.md.

## Work queue
1. Y10 composition: extend G03 assembly constructor/theorem ledger and combinations for loops, modifiers, try/catch, unchecked, constructors and libraries. Track every Y01–Y09 child and dependent G48–G51 obligation; prove concrete assembly coverage without a residual assembly fragment predicate. Requires actual V16/VY3/VY4 correctness interfaces; no generic theorem repackaging presented as full proof.
2. G52 assembly differential harness: pinned solc 0.8.38 upstream inlineAssembly corpus, compiler settings/source hashes and legacy/via-IR provenance; compare observable success/failure/bytes/storage/memory/world/logs as relevant. Include unsupported/compiler-dependent/non-memory-safe refusals and pipeline dirty-bit/allocation behavior; do not change expected verdicts to green results.
3. Concrete whole-pipeline witnesses, negative controls (including always-revert/malformed import/incorrect opcode), both-pipeline composition and final combined import/proof closure. Register proof/test coverage, record exact scope and feature rows honestly, retain failing/blocked cases and prerequisites.

## Backfill queue
A. Before compiler/world prerequisites: build the lane-owned pinned assembly corpus inventory, fixture extraction and differential runner/provenance validation with local mock tests; independently run actual solc outputs where tools exist. Preserve raw outputs and distinguish reference evidence from Lean correspondence. Do not copy/replace V17 or legacy TestSuite generated outputs.
B. Add assembly combination fixtures and independent expected outcomes/admission controls, ledger schema/coverage checks and stale/missing-proof rejection; map VY1–VY4 interface obligations precisely. Wire to concrete compiler/source/world proofs only when available and keep all missing correspondence/composition gates pending.
