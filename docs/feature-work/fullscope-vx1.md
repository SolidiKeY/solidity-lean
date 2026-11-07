# VX1: contracts and environment fields

Latest H121 status (2026-11-07): ownership resumed from move5 head90e39f89,
merged mastera8f684928, checked transferred V1 plus new backward-completion
consequences. Source/EVM production linkage remains open. Cross-module OpenLoops
checkpoint prototype is a non-module draft after a180s prerequisite stop; no
300s time-limit repair or full-gate clearance is claimed. See final H121 section.

Base: `e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`.
Branch: `codex/solidity-fullscope-20261104/vx1-contracts-environment`.
Repository: `/workspace/solidity-lean`.

Current status: H38 resolved Q-ORACLE-01 by authorizing option 2. The run-indexed proposal is source/kernel checked and submitted for producer review; full X01 freeze/readiness remains pending. Earlier blocking-question sections below are checkpoint history.

Current integrated prerequisite: published `38d38d87e74376d6b95daf9b792fa884333f20b3`, present in start head `90f79509d5882cf521249f52e71b50046d1f5898`. Original assigned base and pre-rebase histories remain preserved. Current proposal import is `Solidity.Language.EnvironmentFields.Contracts`, namespace `Solidity.Roadmap.FullScope`; H38 approval/freeze remains pending.

Current cache policy is H41 coordinator-pull: preserve verified VM packs, report path/SHA, never run ship-cache.sh on the VM. The checkpoint-02 pack is coordinator-received; the H38 pack remains coordinator-pending. Historical helper-transfer requests below are superseded.

## X01 interface checkpoint (in progress)

`Solidity/Roadmap/Contracts.lean`, namespace `Solidity.Roadmap.FullScope`,
contains contract statements, not implementation certificates. All X/O/T lanes
must consume full observations. Existing G01 producers remain pending adapters;
the legacy contracts are not full-scope certificates.

D1 uses `Inputs`, `CodeRef.bytes`, `ScalarQuery`, `Oracle`, `Source.meaning`
and `OracleAgreement`; G07 must extend its whitelist to those datatypes and
check source closures independently of compiler definitions. Oracle agreement
must be proved for the actual execution, not assumed for an arbitrary function.
D2 fixes creation limits with `creationFits`; exact Osaka gas semantics still
require an EVM owner adapter. D3 exposes byte memory and packed physical slots.
D4 exposes `UnsafeWriteback` and `Opaque`, each requiring producer proofs.
D5 retains quantified environment/crypto premises through `Lang`; a source
adapter must audit every allowed/guard premise. D6 uses `Optimizes`, which
normalizes only gas/gasleft scalar values (preserving occurrences and order) and preserves outcomes and all other
observations. No cost improvement is asserted.

Consumers requiring relay: every X/O/T lane; existing direct G01 consumers
`Roadmap/{Controls,TypedRun}`, `Source/{State,WellFormed}` (VY5),
`Yul/{Words,Views/Bytes,Composition/CorrectnessInstances}`,
`Lowering/{P8/FrozenInterface,P8b/{Frozen,Domain},Readonly/ReceiverCapture}`,
and `Backend/Failure/{Slice,Emit}`. Producer-owned files are not edited here.

## Queue and outstanding validation

X01 interface: provisional typed draft; per-file kernel check passed; full interface, producer contracts and readiness gates pending.
X01 manifest/catalog: pending all 30 former-exclusion rows, upstream ledger,
`Unmodelled` and `Feature.exclusion_complete` rescope and regeneration.
X02: pending source/admission/lowering/compiler implementation and owner adapters.
Owned backfill: census, witnesses, negative controls and combinations pending.
H35: build, axiom inventory, controls, final gates, sealed logs and cache export
pending. No checkpoint readiness or final correctness is claimed.

## Runtime evidence

Docker image `ubuntu:24.04`, digest
`sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`.
Verified cgroup memory.max=12884901888 and memory.swap.max=0, --cpus=1.
Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake 5.0.0-src+797c613. KeySort per-file gate passed (1.887s wall,
131891200 bytes cgroup memory peak, not aggregate RSS).
Logs: `/workspace/vx1-evidence/runtime-retry.log`; first probe failed because
GNU time is absent. Full runtime gate remains pending preserved KeySort output
and aggregate-RSS/headroom monitoring. Historical setup claims are not reused.

## Read-only draft reviews

Finder and skeptic independently reviewed without Lean server or writes.
Confirmed findings fixed in draft: `Exact` now requires `Cert` plus total domain;
`OracleAgreement` takes the actual reader as an external argument;
`ArtifactSound` binds source interpretation to compiler output and the resource-indexed target
reader for one directional soundness only; unsafe execution/writeback/correspondence are external parameters;
byte-memory extent is word-aligned and unallocated bytes zero; gas normalization
retains observation occurrences and order.

Still blocking interface freeze: full public contract preserving the six legacy
contracts' obligations, typed exact Osaka resource/failure obligations, physical
layout agreement/refinement and D5 premise audit. The draft is not `stubReady`.
Reviews: `/root/interface_finder` and `/root/interface_skeptic` (this session);
full review text must be sealed before checkpoint readiness.

Re-review found that the target reader lacked the resource bound: two executions
with different initial gas could not have different `gasleft` values. Fixed by
indexing `Target.read` by `lang.Res`. Replaced the overly strong family-based
`ArtifactOptimizes` draft by the explicitly one-directional `ArtifactSound`;
source/target resource alignment and two-sided adequacy remain open, never
substituted by this auxiliary statement.

Validation: first prerequisite build exited 1 after 12.814s (reserved keyword
`unsafe` used as a binder); corrected to `isUnsafe`. Prerequisites built once
(`Hash.CollisionBound`: 7.3s, `Roadmap.Evm`: 1.8s). Subsequent per-file MCP
diagnostics exited 0: `diag: 0 errors` before the resource-index correction.
Final draft per-file kernel check exited 0 in 4.511s with explicit `-j1`,
224555008 bytes cgroup memory peak and sampled peak aggregate RSS 391192 KiB.
This is not checkpoint readiness.

## Static gates on the current draft

`git diff --check`: exit 0.
`node scripts/check-layers.mjs`: exit 0, 603 core modules, zero paths to either
elaborator or checked parser adapters.
`bash scripts/check-trust.sh`: exit 0, 3835 sources, 285 inventoried
implementation/recovery sites, zero findings. This is a source trust scan,
not the required kernel axiom inventory.
`python3 scripts/solidity-feature-audit.py --check`: exit 0, 212 features,
30 exclusions still present; 783 upstream symbols classified. This is baseline
consistency, not completion of the rescope.
`node scripts/check-noncircular.mjs`: exit 1, 20 violations across producer-owned
`Source/Progress` and `Source/Preservation` import closures reaching Lowering.
Those modules were not edited; no baseline rerun or waiver is claimed.

## Producer requests (for coordinator lookup/relay)

- Catalog generator owner: adapt `scripts/solidity-feature-audit.py` for the
approved withdrawal of all 30 exclusions while preserving structured unsupported
feature diagnostics. Its generator currently builds `Unmodelled` from excluded
rows, derives `Inhabited`, and proves `Unmodelled.excluded`; simply setting all
rows to model would emit an empty diagnostic type and retain obsolete theorem
shape. VX1 owns catalog outputs, not this generator's path.
- EVM/G06 owner: exact Osaka charging/resource and creation-failure interface,
including EIP-170/3860; `Roadmap/Evm.pinned` still idealizes code-size limits.
Do not change a producer module from this lane.
- VY5 Source and lowering/compiler owners: actual artifact/oracle/resource
alignment, physical-memory/layout and writeback adapters. Exact requested
signatures await the full public contract; no producer proofs are assumed.

The whole assignment remains open. No frozen interface or relay readiness is
claimed by this provisional checkpoint. Next owned work is completing X01's
public-contract/resource/layout obligations and re-reviewing the complete stub
before advertising `stubReady`; X02 must follow X01 sequentially.

## Checkpoint 02: quotient proofs, controls and census

This checkpoint extends the provisional X01 draft. It is not the requested full
interface freeze, X01 readiness, or X02 completion.

### Kernel-checked statements and premises

All names below are in `Solidity.Roadmap.FullScope` unless qualified otherwise.

| Statement | Exact premises / conclusion |
| --- | --- |
| `Observation.withoutGas_idempotent` | Every `observation : Observation`; normalizing twice equals normalizing once. |
| `eraseGas_length` | Every `p : Prefix Observation Outcome`; normalized event length equals `p.events.length`. This says nothing about equality of lengths between two different prefixes in a refinement. |
| `eraseGas_final` | Every such `p`; normalized final equals `p.final`, retaining exact return/revert bytes. |
| `eraseGas_idempotent` | Every such `p`; `eraseGas (eraseGas p) = eraseGas p`. |
| `eraseGas_le` | `a b : Prefix Observation Outcome`, `h : a.Le b`; concludes `(eraseGas a).Le (eraseGas b)`. |
| `optimizes_of_refines` | `AS : RS → Prop`, `AT : RT → Prop`, `FS GS : RS → Prop`, `GT : RT → Prop`, source/target prefix families, and `h : RefinesUnder AS AT FS GS GT source target`; concludes `Optimizes AS AT FS GS GT source target`. No converse is claimed. |
| `ByteMemory.empty` | Inhabited zero-extent, aligned memory with every byte zero; no solc prologue/FMP initialization is asserted. |
| `CreationSizeFailures` | Statement only: for the producer's `attempt : Bytes → Bytes → Evm.Halt`, every pair failing `creationFits` must observe `(false, [])`. Necessary only: success and exact gas remain separate. |

The standalone kernel controls in
`tests/fullscope-20261104/vx1/ContractsControls.lean` include:

- inhabited byte memory, artifact creation/runtime byte tables, and two distinct
resource-indexed gas supplies;
- gas-value equivalence with raw inequality; exact `pc`, log data, log order,
code bytes and final outcome observations;
- a combined prefix containing logs, raw call bytes, gas, code/codehash, memory,
storage and transient reads;
- exact-limit creation success with nonempty runtime, oversized initcode/runtime
refusal, and refutation of an always-successful size-ignoring toy producer.

These are interface/toy controls, not production compiler or EVM evidence.
`CreationSizeFailures` alone permits an always-empty-reverting implementation
and does not distinguish exceptional failure gas from an empty-data revert.
No such necessary condition substitutes for full D2 correctness.

### Source census and fixtures

`tests/fullscope-20261104/vx1/environment-census.json` covers ten block fields,
two transaction fields and two hash functions, with exact result/argument types,
upstream opcodes and six fork-capability boundaries. Seven upstream files at
`1835d247de183f23e7b0e2bc4a50732af525b77c` were retrieved and SHA256/Git-blob
verified. Existing four manifest pins were checked unchanged; three additional
same-commit source identities are fixture evidence, not edits to trust pins.

Notable source facts: `slotnum` is `uint64`, Amsterdam-gated and selected as
`SLOTNUM` (`0x4b`), absent from the current Osaka `Backend.Op`. Both spellings of
`difficulty`/`prevrandao` use `0x44`: `prevrandao` before Paris produces warning
9432 and difficulty semantics; `difficulty` from Paris produces warning 8417.
A native-member metadata entry alone does not establish source admission.

Reproduction:
`python3 tests/fullscope-20261104/vx1/check-census.py --upstream /workspace/vx1-evidence/checkpoint-02/upstream`.
It passes 14 entries, seven source identities, six fork boundaries and arithmetic
consistency of eleven hash-window expectations. Five corrupted census fixtures
were rejected at their intended checks (types, opcodes, capabilities, arguments,
blockhash boundary). Five combination scenarios remain fixture expectations,
not executed production semantics. No chain premise was invented or assumed.

### Validation, resources and reviews

Runtime gate PASS: Lean 4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`),
Lake 5.0.0-src+797c613, retained KeySort toolkit PASS/log. Final serial kernel
group (KeySort, Contracts, controls plus actual axiom inventory) exited 0 in
6.759s; sampled aggregate RSS 391456 KiB; cgroup memory peak 222347264 bytes.
Verified memory.max=12884901888, memory.swap.max=0, explicit Lean `-j1`,
LEAN_NUM_THREADS=1, --cpus=1 and measured parent available memory never below
16415956992 bytes. These are distinct RSS/cgroup metrics, not inferred bounds.

Final per-file MCP diagnostics: zero errors for each file, serially; 22.835s,
cgroup peak 1012584448 bytes. Both files then passed the direct kernel group.
The 18 printed theorem inventories contain only `propext` and `Quot.sound`, or
no axioms; no new trust pin was written. Whole-library inventory/build remains
pending. Failed intermediate syntax/proof checks are retained in the evidence.

Final source trust scan: exit 0, 3835 sources, 285 inventoried sites, zero
findings. Generated-root check and baseline catalog audit: exit 0. Catalog still
has 30 exclusions, so this is consistency evidence only. Previous G07
non-circularity failure (20 producer-owned Source closure violations) remains
open; its original log was summarized in checkpoint-01, not reconstructed.

Separate read-only finder/skeptic reviews found and fixed the quotient-length
wording and missing positive creation execution control. Census validation was
strengthened to verify argument types, field/opcode mappings, capabilities and
arithmetic boundaries; mutation controls were added. Final reviews found no
new issue in these additions. Neither reviewer used Lean/server or edited files.

Evidence: `/workspace/vx1-evidence/checkpoint-02/` (bounded scripts, complete
runtime logs, RSS/reserve samples, kernel inventories, source receipts and
mutation controls). Latest sealed checkpoint-01 artifacts are preserved.

### Historical pre-H38 question (resolved by H38; not a current blocker)

Historical request, superseded by H38 option 2: `Q-ORACLE-01` [X01/G01, D1/D6]. The complete oracle/resource alignment
API is missing. Artifact/environment-only readers are insufficient, as the
checked counterexample and both reviews showed. D1–D6 and both refinement
directions remain binding. The options recorded before the decision were:

1. Obtain a joint Source/EVM producer signature before freezing the full
interface; retain the independent proofs and fixtures completed here.
2. Authorize VX1 to propose a run-indexed contract binding artifact, oracle and
resources, subject to producer review before freeze.
3. Authorize VX1 to propose an explicit oracle/resource-alignment adapter around
existing G01 contracts, subject to producer review before freeze.

This records the historical pre-decision state only. H38 subsequently approved
option 2; Q-ORACLE-01 is resolved and no new choice is requested. Source/EVM
producer review remains a separate prerequisite to freezing the proposal.

| Queue item | Accounting |
| --- | --- |
| X01 full committed interface/stubReady | Q-ORACLE-01 resolved by H38 option 2; run-indexed proposal committed. Blocked only on Source/EVM producer review/alignment before freeze. |
| X01 D2/D3/D4/D5 public obligations | Open: exact Osaka resource/failure and physical-layout/writeback producer interfaces, full public-contract preservation and premise audit. No producer proof assumed. |
| X01 all-30 manifest/catalog/ledger rescope | Pending after interface freeze; generator-owner adapter requested because the current generator ties diagnostics and their theorems to scope=exclude. No owner file edited. |
| X02 source/admission/lowering/compiler | Pending X01; VY5 Source and existing backend/lowering/compiler owners must integrate adapters. No duplicate G31 implementation. |
| Owned census backfill | Source census and checked fixture consistency complete; production semantics and fork admission remain pending X02. |
| Inhabited/negative/combination backfill | X01 kernel controls complete for the definitions above. X02 chain-input witnesses and semantic boundary/combination regressions remain dependent on the final environment/source interfaces; census expectations do not count as those proofs. |
| Catalog consistency backfill | Baseline audit passes; actual full-scope catalog gate remains pending rescope. |
| H35 final readiness | Full build/integrated closure, full axiom inventory, all semantic gates and ship-cache receipt remain pending. Local packet is not delivery. |

Producer requests additionally include resolution of the 20 G07 violations by
the exact Source owners, preserving the non-circularity gate; and coordinator
cache-helper transfer/receipt. `/home/agent/.local/share/cloudvm-coord/vmexec.py`
is absent. No push, merge, PR, VM replacement or goal reset occurred.

## Checkpoint 03: H38 run-indexed producer-review stub

**Human authorization (verbatim):**

> Coordinator decision H38 (user) on Q-ORACLE-01: take option 2. Write a VX1 run-indexed contract proposal that binds artifact, oracle and resources per run, so differing gas supplies are expressible. D1–D6 and both refinement directions stay binding. Submit it for producer review (VY5 Source, EVM/resource owners) as a stub before freezing; continue the X01 freeze on that stub and report it as a checkpoint.

Q-ORACLE-01 is therefore resolved; no new scope decision is requested. The
producer-review submission is **not** approval to freeze, an implementation of
producer semantics, a full G01 public theorem or H35 checkpoint readiness.

### Proposed interfaces and quantifiers

All declarations are in `Solidity/Roadmap/Contracts.lean`, namespace
`Solidity.Roadmap.FullScope.RunIndexed`, without new imports.

- `SourceIndex (source : FullScope.Source) (resolved : source.Resolved)
  (art : Artifact)` stores its source environment, `source.lang.Res`, and
  `Oracle art`. These are fixed before any target resource witness is selected.
  `SourceIndex.program` interprets the same indexed artifact/oracle;
  `SourceIndex.execution` uses that fixed environment/resource.
- `TargetIndex (target : FullScope.Target) (art : Artifact)` stores target
  environment/resource; `execution` loads that same indexed artifact.
- `SourceRuns source` has independently specified `Admitted`/`Specified`
  judgments, candidate `Legal` runs, typed query transcripts, and proofs that
  transcript kind/value observations and oracle reads agree with source runs.
  `Specified` must be the independently characterized source judgment, never
  the subset a compiler/target happens to match.
- `TargetRuns target` supplies actual-execution query transcripts, equality to
  scalar observations and agreement with `target.read art env resource`.
  Source/EVM owners must prove code/occurrence provenance from their operational
  semantics; kind/value projection alone does not establish that provenance.
- `Bound environment Aligned sourceRun targetRun` binds shared environment and
  the producer's operational resource/oracle plan relation. It is unconditional
  on Forward/hash guards; `Aligned` cannot contain desired refinement or a
  language restriction. Its operational characterization remains owner work.
- `Coupled domain machine environment Aligned direction sourceRun targetRun`
  extends `Bound` with ordered typed query transcripts. Forward has source
  transcript as a prefix of target transcript; backward reverses this prefix
  direction, permitting a source extension beyond a finite target cut.
- `Coupled.forward_oracle_agrees` assumes forward coupling, source legality and
  membership of `(query,value)` in the source transcript. It concludes
  `sourceRun.oracle query = target.read art targetRun.environment
  targetRun.resource query`. `Coupled.backward_oracle_agrees` has backward
  coupling and target-transcript membership instead. Neither theorem assumes
  equality on arbitrary unused queries; both kernel inventories have no axioms.
- `Mode.exact` retains every observation. `Mode.optimizer` applies only the
  existing D6 `eraseGas` projection. Public compilation must use `.exact`;
  optimizer certificates do not substitute for the exact public endpoint.

The data-carrying certificate signature is:

```lean
Certificate (source : Source) (target : Target)
  (domain : SourceRuns source) (machine : TargetRuns target)
  (compiler : source.Resolved → Option Artifact)
  (environment : target.lang.Env → source.lang.Env)
  (Aligned : (resolved : source.Resolved) → (art : Artifact) →
    SourceIndex source resolved art → TargetIndex target art → Prop)
  (mode : Mode) : Type
```

Its mandatory fields preserve both directions and expose, rather than assume,
the missing producer proofs:

1. `admission` is exactly `Admitted resolved ↔ (compiler resolved).isSome`;
   environments are sound and surjective.
2. `legality` requires `Legal resolved art run ↔ Specified resolved art run`
   for **every** run of the actual compiler output, without Forward/Guard
   antecedents. A candidate legality filter cannot remove a specified positive
   source run. Source-owner/G07 characterization of Specified is still required.
3. `sourceResourceCoverage` covers every allowed source environment/admissible
   source resource by a legal oracle instance, with no Forward/Guard antecedent.
   This is resource-totality only; the preceding legality equivalence is
   separately necessary to prevent selection of only Forward-false oracles.
4. Constructive `need` receives the fixed eligible source index, actual compiled
   artifact and universally fixed target environment before Forward/Guard.
   `sourceCoverage` proves target eligibility and `Bound` for this result,
   unconditionally. `targetCoverage` similarly covers every admissible target
   index by an eligible source index and `Bound`, without target Guard.
5. `forward` uses the original source Forward/Guard on that fixed run. It proves
   target Forward/Guard, forward `Coupled`, and source-prefix ≤ target-prefix
   after the explicitly selected mode observation map.
6. `backward` quantifies every eligible target run under its own Guard, and
   proves existence of an eligible source run, backward `Coupled`, its own
   source Guard, and target-prefix ≤ source-prefix.

No source/target `Allowed`, `Admissible`, `Forward` or `Guard` function was
rewritten by the proposal. Legacy G01 declarations are unchanged. Preservation
of the original SourceSpec admission, pipelines, whole source/Forward domain,
nonempty success/hashing/revert/divergence witnesses, world decoding and public
exact correctness still requires producer adapters/proofs. Abstract fields and
successful schema controls do not discharge those obligations.

### Checked inhabitation and adversarial controls

The existing owned `ContractsControls.lean` now includes namespace
`Solidity.FullScope.VX1Controls.RunIndexedToy`:

- `certificate` is an inhabited `.exact` certificate over every `Word` supply.
  Source and target resources are fixed supplies; `need` preserves the source
  supply. Independent source oracle/resource law and actual toy query lists are
  proved, not assumed. The shared execution helper makes this an interface
  inhabitation control, not independent production Source/EVM correctness.
- `gas_supplies_distinct` produces nonempty outcomes `[5]` and `[6]` at supplies
  5 and 6. `source_run_forward` witnesses their positive source obligations.
- `swapped_supply_refused` and `swapped_reader_refused` reject changing the
  resource or observed reader after fixing the source run.
- `backward_cut_allowed` and `forward_cut_refused` regress ordered transcripts
  with a one-query target cut and two-query source extension. They are transcript
  order controls, not a proof of production source-step granularity.
- `filtered_resource_coverage` covers every resource using a zero-valued oracle;
  `filtered_forward_false` shows why that alone could hide adequacy.
  `specified_run_cannot_be_filtered` refutes such a certificate using its required
  unconditional equality with the independent source judgment.
- `always_reverting_refused` refutes an exact certificate for a target preserving
  reads/resources but reverting rather than returning the positive source result.
- `wrong_artifact_refused` rejects substituting an artifact with equal table
  length and different bytes for the actual compiler output.

`Certificate` contains the constructive `need` function and lives in `Type`;
negative controls correctly refute `Nonempty (Certificate ...)`.

### Gates, reviews and evidence

Same VM/branch and original base are preserved. Runtime refresh: Lean 4.24.0,
Lake 5.0.0-src+797c613 and retained KeySort toolkit PASS, 1.616s. All new Lean/MCP
work was serial with explicit `-j1`, LEAN_NUM_THREADS=1, verified 12GiB cap,
zero swap and continuous 4GiB parent-reserve monitoring.

Final per-file diagnostics: zero errors in both files, 17.590s, sampled peak
aggregate RSS 1031836 KiB. The proposal/control kernel group exited 0 in 5.741s,
sampled peak aggregate RSS 402112 KiB, cgroup peak 242761728 bytes, and parent
available memory at least 16376463360 bytes. These are separate metrics.

There are 21 new actual axiom-inventory outputs (39 including previous controls):
only `propext`, `Quot.sound` or no axioms; the two operational reader-agreement
lemmas require no axioms. No trust pin or heartbeat limit was changed.
Failed intermediate type/proof diagnostics are retained, not counted as passes.

Separate read-only finder/skeptic reviews found and fixed: source legality could
filter Forward-positive instances despite resource-totality; backward query
coupling over-constrained finite prefix cuts; unconditional query coupling added
an unnecessary obligation when hash guards fail. The final schema uses legality
equivalence, directional transcripts, and unconditional Bound separated from
original guarded semantic correspondence. Final reviews report no new schema
or control defect. Neither reviewer used Lean/server or edited files; these are
local reviews, not VY5/EVM producer approval.

Evidence is under `/workspace/vx1-evidence/checkpoint-03/`. Committed-head replay,
sealed source hashes, cache packet and checksum manifest are recorded by the
external handoff. Previous checkpoint seals remain intact. Full integrated
build, complete production axiom inventory and ship-cache receipt remain pending;
no H35 readiness is claimed. Preinstalled historical cache provenance remains
UNVERIFIABLE rather than reconstructed.

### Immediate coordinator relay / producer review request

Relay the committed H38 stub path/signatures to **VY5 Source and EVM/resource
owners** for review before freeze; notify original X/O/T consumers that it is a
proposal and is not yet usable as a frozen final-check dependency. Retain this
relay request until receipt. Review must answer:

- Source: characterize Specified independently; prove legality equality and all
  source/Forward/resource coverage without a language exclusion, oracle
  cherry-picking, guard weakening or an assumed producer theorem.
- EVM/resources: derive actual query code/occurrence labels and `target.read`
  from the pinned execution; characterize Aligned as operational run/failure/
  horizon facts, not desired refinement; assess all coverage obligations.
- Both: check source/target prefix granularity and extension/oracle compatibility,
  exact public mode and optimizer mode, then provide approved adapter paths and
  commits. No producer-owned file was edited here.

No new module/import was added, so generated roots/maps remain unchanged. The
central map proposal is to extend the existing Roadmap/Contracts row with the
H38 RunIndexed contract namespace after producer approval; no central file was
co-edited.

### Remaining queue after H38 proposal submission

- X01: producer review and receipt, freeze on the approved stub, remaining
  D2/D3/D4/D5/public-contract fields and adapters, all-30 manifest/diagnostic/
  upstream-ledger/catalog rescope and final integrated gates remain open.
- X02: remains sequentially dependent on X01. Source/admission/lowering/compiler
  integration and production environment witnesses/negative/combination proofs
  remain open; the completed census/fixtures are not those implementations.
- Existing generator-owner adapter, 20 G07 Source closure violations and cache
  helper transfer/receipt requests remain outstanding. No relaxation is proposed.
- No push, merge, PR, VM replacement or goal reset occurred. H38 resolves the
  prior human question; subsequent review is requested from producers, not
  treated as already approved.

## H41 cache receipt and delivery-policy amendment

Coordinator-reported receipt for the checkpoint-02 H35 packet:

- Receipt (coordinator host):
  `/home/guilherme/.local/state/cloudvm-coord/receipts/vx1-contracts-environment-cache-received-20261105T020232Z.json`.
- Archive (this VM): `/workspace/vx1-handoff-830d2598/cache-packet.tar.gz`.
- SHA256: `eb7b14bbf7f75e173b0548c225fa1ef3beb7e9b24dbe7ef3903b87de78f4d745`.
- Coordinator verified against the reported SHA: yes, as stated in H41.
- Local SHA256 was recomputed and matches exactly. The remote receipt's contents
  are coordinator-reported, not represented as locally read evidence.
- Delivery status for this exact packet: **coordinator-received**.

**H41 amendment (verbatim):**

> Leave verified packs on the VM and record the path and sha; the coordinator pulls them; never run ship-cache.sh on a VM. Mark delivery coordinator-pending and continue.

This amendment supersedes requests to install/transfer a host cache helper or
run shipment tooling on this VM. No `ship-cache.sh` invocation is needed or made.
All existing verified packets and prior seals remain preserved.

The receipt above covers the older checkpoint-02 packet only. The H38 packet is
still available for coordinator pull:

- Archive: `/workspace/vx1-handoff-06f5ae08-final/cache-packet.tar.gz`.
- SHA256: `bfcecd39a46edb5c08ede4c387d10bc697c12a5adcbe5fcccdfbbd2348c2f0c4`.
- Local SHA256 recomputed: pass. Delivery: **coordinator-pending**.
- Its source head is `06f5ae081ca5e01a976b3ae3cb9b43a3d369d033`; this receipt-only
  documentation update does not change its checked Lean source or cache contents.

A received partial cache packet is not an integrated build, complete dependency
cache, producer approval, interface freeze or checkpoint readiness. H38's
producer-review relay/receipt remains pending, along with the remaining X01/X02
implementation and validation obligations. H41 closes the earlier packet's
transfer obligation and removes the host-helper blocker; it does not resolve
those independent source/EVM/generator prerequisites.

Validation for this documentation-only update: exact local hashes of both
preserved packets, matching the supplied receipt for checkpoint-02; `git diff
--check`. No Lean source changed, so no Lean rebuild or repeated proof checks
were performed. No new scope question, goal creation/reset, push or publication.

## Checkpoint 04: adopt independently published master

Published prerequisite: `8495f1deb0a95dd6b9301822d8649ab76b217681`.
Preserved VX1 parent: `d053582ca57b6a3da5706aef64529df2ecb0f3ac`.
Preservation merge: `38613ec0b319d866d7fbd597dc2285e115956b63`.
Original assignment base remains `e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`.

`git fetch origin master` obtained the exact reported SHA; `origin/master`
matched it, and the original base is its ancestor. The clean owned branch was
merged with that exact SHA, without reset, rebase, branch replacement or default-
branch publication. Both original parents remain reachable. There were no
conflicts or manual integration edits. Imported generated roots/maps/trust pins
are the published producer/coordinator versions, not VX1 co-edits.

Read-only finder and skeptic independently confirmed all ten existing files in
VX1 reserved paths are byte-identical to the VX1 parent. VX1's five changed paths
and master's 152 changed paths are disjoint; the merged tree is their union.
The published delta contains no protected `Solidity/Source/**` or
`Solidity/Syntax/Scoped.lean` edits. No protected producer repair was attempted.

The packet scope is `docs/feature-work/integration-20261105-checkpoints.md`:
27 bounded increments/58 Lean modules/two fixtures, plus previously published
VC1. These are bounded producer checkpoints, not whole-lane completion. The
reviewed VC1 opaque data fingerprints are exactly inventoried upstream; scanner
policy was not changed or relaxed here.

### Dependency assessment

No H38 Source/EVM approval, RunIndexed producer adapter or generator-owner
change arrived in the published tree. The Source, EVM contract interface,
feature-generator and all VX1 catalog files are unchanged by this adoption.
`Solidity/Optimizer/RoadmapComposition.lean` adapts the legacy `Roadmap.Cert`
boundary and explicitly supplies no D6/artifact-linking certificate. It does
not consume the new RunIndexed contract or authorize its freeze.

The held statement-grammar Gate G0 failure and VY5 Monetary.wide failure remain
producer work. The exact owners retain H16/H22 reservations; this lane must not
repair them or manufacture stubs. V16's described branch-history situation is
not treated as missing source or permission for duplicate recovery work.

### VM revalidation and cache boundaries

The owned contract/control import closure is unchanged: Contracts, its direct
Hash.CollisionBound/Evm/Keccak dependencies and lean-toolchain have identical
source to the prior VX1 parent. The owned closure was rechecked on the actual
merge head using the existing bounded tooling: runtime versions and KeySort,
Contracts kernel emission, controls and all 39 printed axiom inventories.
Exit 0, 7.146s; no producer proof, observation, premise or budget changed.
This does not check the full 152-file imported closure.

Current-tree static checks exited 0 in 13.041s:
3923 source files, 287 inventoried sites, zero trust findings; 628 core modules,
zero elaborator/checked-parser paths; generated roots current; baseline catalog
212 features and 783 upstream symbols current. All 30 exclusion rows still await
rescope. These checks do not establish full X01 or production readiness.

Every heavy check remained serial under explicit -j1/LEAN_NUM_THREADS=1,
verified 12GiB/no-swap cgroup and continuous 4GiB parent-reserve monitoring.
Logs/RSS/reserve records: `/workspace/vx1-evidence/checkpoint-04-integration/`.
No unrelated prerequisite rebuild or cold build was launched.

H21 shipping notice `sched-20261105T0200Z` is not a per-VM cache-freshness receipt.
The local materialized artifacts for Optimizer.Pass and
Backend.MemoryOps.SourceRawBoolCopy were absent when sampled; that fact does
not prove shipment absence, and neither pack availability nor full cache
freshness is claimed. H41 remains in force: preserve verified packs on this VM,
report exact path/SHA and let the coordinator pull. Never run ship-cache.sh here.
Earlier receipt covers only its exact archive, not this integrated tree.

Both local read-only adoption reviews found no graph/ownership defect. Neither
used Lean/server or wrote files; they do not substitute for producer approvals
or integrated VM gates.

### Continued queue and remaining requests

The owned queue remains X01 then X02. Continue X01 freeze after VY5 Source and
EVM/resource reviews of the committed H38 stub; preserve that relay request until
receipt. The integration supplies none of the missing approvals. Full public
D1–D6 contracts, all-30 manifest/diagnostic/ledger regeneration, X02 production
integration and dependent witnesses/negative/combination proofs remain open.
Existing generator and G07 owner requests remain; no source gate waiver or
language exclusion is proposed. Completed independent census and schema controls
remain available as scoped evidence, not production proofs.

Final integrated build/complete inventory, exact-head combined imports and
applicable cache receipts remain pending on actual prerequisites. Coordinator
publication claims are recorded as upstream evidence, not relabeled as VM checks.
No push, PR, goal creation/reset, VM replacement or host relay was performed.

## Checkpoint 05: follow-on publication adoption

Published prerequisite: `f77cf60d3cea8f7f1db8db29cc027532b0cd3fce`.
It contains the previous `8495f1deb0a95dd6b9301822d8649ab76b217681`.
Preserved owned parent: `cecce55114a0ea859ce8000ced268c9204bf002d`.
Exact preservation merge: `620772e25d14c81e6a5f1670ec55800a274fa34e`.
Original base remains `e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`.

Fetch/readback and ancestry verified the exact published master. The existing
clean branch was merged without conflicts, reset/rebase, discarded work or
manual integration edits. Separate read-only finder/skeptic reviews confirmed
both parents, previous publication/base ancestry, all ten reserved files
preserved, and no protected Source/Scoped change. Neither reviewer used Lean,
a server or writes. Imported generated roots/maps/pins are published coordinator
content; no lane co-edit was made.

The exact scope is `docs/feature-work/integration-20261105-deferred.md`:

- Type grammar adds ParserBasics/ParserChecks.
- Shared.Intrinsic is a relative obligation builder. Its loop/entry callbacks
  remain explicit producer dependencies and reference inputs remain refused.
- ExpressionUniqueness.Statement supplies the target statement; the exhaustive
  proof is not integrated.
- StorageOnlyHavoc derives the existing typed formula. It supplies neither an
  ExtCall implementation, callback restriction nor Source/native adequacy.

The cumulative 31 increments/63 modules/two fixtures are not whole-lane
completion. Statement-grammar G0 repair, VY5 Monetary.wide and all ownership
holds remain with their producers; no coordinator/consumer substitute was made.
The V16 history notice is not permission to duplicate integrated content.

No H38 producer approval, RunIndexed adapter or generator change arrived. The
Source/EVM interface, catalog generator, owned source and owned direct dependency
closure are unchanged. The H38 stub at `06f5ae081ca5e01a976b3ae3cb9b43a3d369d033`
still awaits VY5 Source and EVM/resource review before freeze.

VM revalidation at the actual follow-on merge head passed runtime versions,
KeySort and the owned Contracts/control closure with all 39 axiom inventories:
exit 0, 8.447s. Current static checks passed in 14.376s: 3938 sources, 287
inventoried sites, zero findings; 636 core modules, no elaborator/parser paths;
current generated roots; baseline catalog still 212 features/783 symbols with
30 exclusion rows awaiting rescope. G07 rerun failed in 28.428s with 20
producer-owned violations (4521 modules scanned). No failure or gate was waived.

All checks were serial in the existing verified 12GiB/no-swap envelope,
explicit -j1/LEAN_NUM_THREADS=1 with continuous 4GiB parent-reserve monitoring.
Evidence: `/workspace/vx1-evidence/checkpoint-05-follow-on/`. No unrelated cold
build was launched and full imported-closure validation remains pending.

H21 target outcomes (49 successes, one capacity skip, five failures under H30)
are coordinator-reported aggregate outcomes. They are not this VM's freshness
receipt. Applicable target receipt/cache provenance remains unverified; no
successful full consumer adoption or cache freshness is inferred. H41 still
requires verified packets preserved for coordinator pull, never on-VM
ship-cache.sh. Old packet receipt coverage is not extended to the new tree.

Queue accounting is unchanged: X01 complete D1–D6/public contract freeze,
all-30 manifest/diagnostic/ledger regeneration, X02 source/admission/lowering/
compiler and production controls, and final integrated gates remain open. The
completed census and schema controls remain scoped evidence only. Producer
review/adapter requests are retained until receipt; no new scope question is
introduced. No push, PR, goal creation/reset or VM replacement occurred.

## Checkpoint 06: scheduled 0840Z publication adoption

Adopted exact published 9584f9e7df09f638d9e0cb8930501d1660aa4b2f into the
owned branch from 1d78fc8381f96a76a57705b8caf9598ecf97d169 by preservation
merge 0c8b011f4c00b4cef15abc1e10ae8ab7a61bc4f4. Both parents and original
assigned base remain ancestors. Parent deltas are disjoint; all ten existing
VX1 files, protected Source/Scoped, Contracts direct imports/toolchain and
catalog generator are unchanged. No unexpected local work was discarded.

The publication records 35 bounded increments/83 Lean modules, not full lanes.
Its repaired statement-grammar fixtures are now published; the former G0 hold
is historical. VA1 checks facade and C3 additive Controls are integrated.
Standalone CallResume does not change opaque callback execution. Physical-byte,
precompile and arithmetic results do not establish whole Source/Osaka adequacy.
See integration-20261105T0840Z.md for producer hashes and exact scope.

No H38 producer review/approval, RunIndexed adapter or generator change arrived.
The proposal at Contracts.lean@06f5ae081ca5e01a976b3ae3cb9b43a3d369d033 remains
unfrozen; coordinator relay to VY5 Source and EVM/resource owners is retained.
VY5 Monetary.wide remains producer-owned. No source substitute was introduced.

Actual VM checks at this merge: Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613,
allowed KeySort PASS, owned Contracts/control kernel check and 39 inventories
PASS (standard propext/Quot.sound or none). This supplies scoped runtime evidence,
not whole-lane RUNTIME_GATE_PASS. Static trust: 4010 sources, 287 inventoried
sites, zero findings; layers: 641 core modules with no elaborator/parser reach;
roots current; baseline catalog 212 features/783 symbols still has 30 exclusions.
G07 FAIL: 4601 modules scanned, 20 producer-owned Source closure violations.
No gate, premise, whitelist or budget was weakened. No full imported closure
build or imported cache freshness is claimed. All checks serial with explicit
-j1, LEAN_NUM_THREADS=1, verified memory.max=12884901888/memory.swap.max=0,
continuous parent 4GiB reserve. Commands, wall/RSS and decisive output retained
in /workspace/vx1-evidence/checkpoint-06-publication/ (metrics.json and logs).

Separate read-only finder and skeptic found no adoption/preservation defect;
both verified exact ancestry/union, owned/protected preservation and retained
producer holds. Neither used Lean/server. Their results are reviews-final.txt.

Queue: X01 full D1-D6/public freeze and all-30 rescope remain open; X02 production
source/admission/lowering/compiler remains blocked on that contract/owner work.
Existing census, witnesses and negative schema controls are scoped backfill,
not production semantics. Full H35 build/axiom/semantic gates remain pending.
H41 requires preserving a verified source/toolchain-bound partial owned cache
packet for coordinator pull; no on-VM ship-cache, freshness or delivery claim.
Prior received packet/receipt remains preserved. No push/PR/VM or goal reset.
The manual stop_goal(blocked) call was rejected for missing trusted CCA context;
no goal transition is claimed and get_goal is unavailable in active tools.

## Checkpoint 07: scheduled 1200Z publication adoption

Fetched and adopted exact b86ae4568cef6d6226f4d170360bbb089debe3fb from
owned parent 1b118ac976a1d79ffe3dc5be3f6beb51403ffa8b by merge
35ea02206c0880f0be535854c39f64d11b628a45. Published base 9584f9e7 and
original assigned base remain ancestors. Disjoint deltas/exact merge union;
ten VX1 files, protected Source/Scoped, direct Contracts imports/toolchain and
catalog generator unchanged. No local work discarded, push or PR.

The 27 bounded increments are documented in integration-20261105T1200Z.md.
VT1 data-layout references and Yul PendingCoupling are distinct interfaces;
PendingCoupling explicitly supplies no instance and retains Source/G01/layout
owner review. Data-layout results do not authenticate assembly output or prove
memory-copy semantics. No H38 approval or RunIndexed adapter arrived. Producer
review request for Contracts.lean@06f5ae081ca5e01a976b3ae3cb9b43a3d369d033
remains active; no full D1-D6 freeze, catalog rescope or X02 blocker discharged.

Actual VM revalidation: Lean4.24.0/797c613, Lake5.0.0-src+797c613, KeySort PASS;
owned Contracts/control kernel closure and 39 axiom inventories PASS (standard
propext/Quot.sound or none), 8.296s. Current trust/layers/roots/catalog PASS,
15.814s: 4061 sources, 287 inventoried sites, zero findings; 643 core modules,
no elaborator/parser reach; 212 features/783 upstream symbols, still 30 exclusions.
G07 FAIL, 28.944s: 4654 modules, 20 producer-owned violations. No gate/premise/
whitelist/heartbeat weakened. Serial verified 12GiB/no-swap container envelope,
LEAN_NUM_THREADS=1, explicit -j1, continuous 4GiB parent reserve. Full imported
closure build, production controls and full H35 readiness remain pending.
Commands, exit/wall/RSS and decisive outputs: /workspace/vx1-evidence/checkpoint-07-publication/.

Separate read-only finder and skeptic found no preservation defect; neither used
Lean/server. Both confirmed no H38 approval/adapter or applicable cache receipt;
results retained in reviews-final.txt. No source fix was needed.

Queue remains X01 full freeze/all-30 rescope then X02 production source/admission/
lowering/compiler integration; completed census and toy controls are backfill,
not Source/EVM adequacy. Owner requests and relay remain until receipt. H41:
leave verified partial owned cache packet for coordinator pull, delivery pending;
never on-VM ship-cache. Upstream gate/cache notices do not establish local full
readiness/freshness. Prior packs and checksums retained. Manual blocked-goal
transition rejected for missing trusted CCA context; no goal create/reset/complete.

## Checkpoint 08: current published prerequisites and rebalance accounting

The original branch has adopted published 8bf8321873befa3f35ca31e97e5339a1baee93e6
and now 3ad22f66d8fc6431378c22e71823436c79dede7f, preserving the original assigned
base and all prior owned commits. Latest merge 2600ba7046d53a41c24046991ec04c59673a3074
has owned parent74d7e69c888f28f9f31c9128a964c8dbcd61d79d. Exact disjoint union;
all15 owned files, Source/Scoped and direct proof dependencies unchanged.

The separately authorized G35-ADDR-RAW-1105 rebalance is source/kernel checked,
reviewed and published byte-identically in 8bf83218; its root/map registration
is verified. Its standalone37-theorem audit is separate from guarded G07 pins
(no RawAddress guarded entries). See calldata-packets-1105-RawAddress.md and its
sealed handoffs. This does not complete X01 or X02.

The latest18 increments add bounded length-check, call-scope, memory-cost growth,
shift and other supporting results. No Source/EVM H38 owner review/approval,
RunIndexed adapter, environment-field integration or catalog-generator change
arrived. X01 full D1-D6/public freeze and all30 exclusion rescope remain open;
X02 source/admission/lowering/compiler and production controls remain blocked.
Completed census/schema backfill and RawAddress do not substitute for those goals.

Actual adoption-head runtime/KeySort and unchanged37-theorem RawAddress inventory
passed in3.844s (Lean4.24.0/Lake5.0.0-src+797c613). Separate read-only finder and
skeptic verified preservation and retained boundaries; neither used Lean/server.
No new implementation or cold foundation build was undertaken. Existing G07
failures and historical missing evidence are not waived or reconstructed.

Coordinator reports full/core/Bridge/TestSuite/corpus/automatic/axiom/review PASS
under host receipt sched-20261105T1608Z; that receipt was not read on this VM.
Integration leaf prospective review language is not itself a completion receipt.
Current own-branch full-library/cache admission is a separate gate; no freshness
or readiness is inferred from publication. H41 prior partial packs and all seals
remain preserved with their original checksums; no ship-cache on VM or new delivery
claim. No goal/VM creation/reset, push or PR. Exact saved-head gate results are in
tests/calldata-packets-1105/RawAddress/evidence/publication-3ad22f66 and its handoff.

## Checkpoint 09: authorized e6849d3b rebase

The coordinator explicitly requested rebase before the next commit. A clean
11-commit rebase onto e6849d3bdf516099d20c33d3581d523449764018 completed without
conflicts at2c6dd714ae5762186b62febb249d3867e526155d. Original branch/head/base
and all historical seals are preserved; the pre-rebase head2b8d7e70c03f436e06c151dfcf32352560905468
remains reachable at refs/vx1-preserved/pre-rebase-e6849d3b. Rebased tree equals
exactly the precomputed old-lane/upstream union, with the same eight local overlay
paths. All15 owned files and four direct dependencies retain their original bytes.

Original H38 proposal06f5ae081ca5e01a976b3ae3cb9b43a3d369d033 is preserved in
that history. Its rewritten equivalent is76efe1a37a459b77b2e330d98eaafbd5b999ae7c;
Contracts SHA2563e3833def0982b523de8be6a61a8c9b36b56abd9058b96b79a810582f3ced406
matches exactly. Relay this rewritten path/commit to all consumers and the
Source/EVM owners; it is a producer-review proposal, not frozen or dependency-ready.
No theorem, premise, exclusion, observation or proof budget changed.

The published four new Source/Agreement modules are adopted byte-identically,
not manually edited H16 implementations. They relate primitive values/locals
and state an unproved one-direction normal-result obligation; no full-state/
resource simulation, Source interpretation or RunIndexed adapter is supplied.
No H38 approval, environment-field adapter or catalog-generator change arrived.
All original X01/X02 obligations remain open; G35 RawAddress remains published.
The short COORD-MERGE notice supplies no new full-gate/cache receipt; no such
outcome is inferred. Pruned foreign evidence is not reconstructed.

Separate read-only finder/skeptic reviews pass preservation and scope. Finder
also verified all484 available checksum-manifest entries. Neither used Lean/server.
Actual bounded rebase-head runtime/KeySort and both owned inventories (37 RawAddress,
39 VX1 controls) passed4.418s, Lean4.24.0/Lake5.0.0-src+797c613. No owned Lean
source changed, no new implementation or cold prerequisite rebuild was performed.
Saved-head checkpoint and G07 outcomes are separately retained under
 tests/calldata-packets-1105/RawAddress/evidence/rebase-e6849d3b.
H41 packs/seals remain unchanged; no VM/goal replacement/reset, push or PR.

Saved checkpoint at29588eb314e0ebc16c5c895139543ead1ff50a73 failed43.355s:
full-library cache admission failed; trust/orphans/layers/roots/doc-paths passed.
Pin inventory reports8599 theorems, zero axiom-set errors and479 unrecorded changes.
Read-only published-base equivalence confirms all479 are inherited frome6849d3b,
not this lane:58 V08,7 V16,414 test pins. No shared pin file was edited.
G07 rerun failed30.196s:4812 modules,89 Source modules,24 violations. Four new
reported paths are Source.Agreement.{Locals,NormalStatement,Primitive,PrimitiveTypes}
to Semantics.Run;20 earlier violations remain. Resolution belongs to the Source/
G07 owners under existing policy, not an automatic whitelist expansion. Exact
logs and pin-origin.json are preserved. These findings do not change any proof.

## OOM hold response, 2026-11-06: isolate the proposal leaf

Human authorized an OOM repair and push of a head marked [oom-fix]. Start head
90f79509d5882cf521249f52e71b50046d1f5898, published input
38d38d87e74376d6b95daf9b792fa884333f20b3. The host pre-gate reported six8GiB
kills with no last module. That host failing module is still UNKNOWN; the
journal/command was requested. No local measurement reproduced an8GiB OOM.

The lane's only changed registered library module was Roadmap.Contracts,
invalidating3364 reverse dependents (3361 default touched targets). Its own
baseline check passed8.010s at324264KiB maximum child RSS, so it is not shown
to be an8GiB proof. A large inherited candidate, Yul.Checks.Arithmetic.Part01,
passed43.042s at803528KiB. A tiny two-module Lake probe was serial at one thread;
it supplies no process-overlap evidence. The3361-target cache/planning-only probe
used73416KiB and failed on missing artifacts, not OOM. These distinguish measured
facts from hypotheses and do not identify the host's failing module.

Restored Solidity/Roadmap/Contracts.lean byte-for-byte to published master. Moved
the entire FullScope/RunIndexed namespace into the explicitly imported leaf
Solidity/Language/EnvironmentFields/Contracts.lean, within VX1 ownership. Everything
from namespace through EOF is byte-identical: names, statements, premises,
observations, proofs and budgets unchanged. Only the owned control import changed.
Legacy G01 consumers retain their unchanged foundation. FullScope consumers must
now explicitly import Solidity.Language.EnvironmentFields.Contracts; no backward
import shim was added because it would recreate the dependency invalidation.
No other production consumer exists in this checkout. H38 owner review/freeze
remains pending and the new path must be relayed to all original consumers.

The changed registered-module closure is now one leaf. Actual touched gate
builds only that module, PASS2.011s,273208KiB maximum child RSS, zero OOM events.
Leaf standalone kernel check PASS1.543s,270476KiB; all39 existing controls
PASS1.440s,246472KiB. All checks used verified8GiB/no-swap, explicit Lean-j1,
LEAN_NUM_THREADS=1 and continuous4GiB parent reserve. No maxHeartbeats or other
proof-budget rescue. These are scoped local passes, not host pre-gate clearance.

A stale local foundation object still contained relocated declarations despite
Lake's up-to-date/cache receipt, causing duplicate-declaration errors on the first
standalone leaf check. Preserved the stale object/receipts; rebuilt the small
foundation with a private cache in3.481s using explicit-j1. The final standalone
kernel checks pass. MCP's initial zero-error report alone was not treated as proof.

Independent finder/skeptic found no semantic/G0 defect in the extraction. Both
verified exact body/foundation identity and require explicit import migration and
central registration. Temporary root profiling TOML was removed; its fixture and
all profiling commands/PID RSS/cgroup memory.events remain in owned evidence.
The targeted checkpoint passed touched/trust/layers/fragments/doc paths but failed
foreign library cache admission, the unregistered leaf's root/orphan checks and
existing shared pin drift (4133 unrecorded, zero axiom-set errors). No shared
registry/map/pin policy was edited. Registration/map proposal is retained for COORD.

Evidence: tests/calldata-packets-1105/RawAddress/evidence/oom-20261106.
This mitigates measured rebuild amplification and is to be pushed for host
re-gating; exact host OOM attribution/result remains pending. Original X01 full
freeze/all30 rescope, X02 production and other owner obligations remain open.

## Skeptic-held 707500a2 follow-up

The coordinator's follow-up explicitly authorizes normal root registration and
an area fragment for the isolated leaf. Both Contracts and ContractControls are
registered by register.sh; the roadmap.d/vx1-contracts-environment.md fragment is
regenerated by fragments.sh. Normal library imports therefore include both the
proposal and its new inhabited/negative controls, not only the external tests.

The registered ContractControls module supplies reachable dirty assembly exits
with actual recovery/byte preservation, rejects identity and erasing writebacks;
keeps an unsafe nonempty block opaque while changing a safe block and rejects
unsafe edits; constructs a total Exact pass with its Cert and a nonempty observed
success, rejects an always-reverting target; exercises optimizes_of_refines on
live guarded/admissible resources and rejects changed final outcomes; constructs
ArtifactSound using an actual artifact and resource-indexed reader with nonempty
code/gas/memory observations, rejects reverting artifacts; and uses an inhabited
query to validate OracleAgreement and reject changed gas readers. These are
interface non-vacuity models, not production Source/EVM proofs.

The historical Q-ORACLE-01 request is now explicitly labeled superseded. H38's
option2 decision remains resolved; pending producer review is not that question.
check-census.py now asserts the exact seven unique source paths and exact six
fork/capability boundaries before validating their pinned bytes and source text.
Printed counts are computed from the structures actually checked. Mutation tests
cover missing/duplicate/extra identities and missing/extra/wrong fork boundaries.

Final independent read-only finder and skeptic found no blocking defect in all
five follow-up fixes. Both verified live domains and negative controls, normal
root/map coverage, enforced census counts and corrected H38/scope accounting.
Neither used Lean/server or independently reproduced the supplied measurements.
Kernel check of the new controls passed1.038s at249096KiB maximum child RSS; all
19 inventories use only standard axioms. Census baseline plus eight mutations
passed. Full-root build/cache validation and host OOM attribution remain open.

### RawAddress scope authorization retained

Source tag: coordinator idle-lane rebalance H10/H12, 2026-11-05, assignment
G35-ADDR-RAW-1105, dispatched to this same VX1 thread/VM/branch. The authorization
was: "Exclusive write scope: Solidity/Backend/CalldataPackets/RawAddress/**;
tests/calldata-packets-1105/RawAddress/**; docs/feature-work/calldata-packets-1105-RawAddress.md."
It also stated "The integrator is V11"; that identifies the integrator, not a
transfer of the explicitly assigned writer reservation. Hence the retained
RawAddress audit, fixtures and sealed evidence are authorized VX1 backfill.
The coordinator's 1422Z publication message independently identifies snapshot
5d40125c420f7e453706d163e12a02729e3e573d as the contribution of both RawAddress
source modules; those modules remain published byte-identically. Nothing was
moved from another lane or used to claim X01/X02 completion. Original seals are
preserved rather than relocating historical evidence and invalidating receipts.


### H70 all-30 staged manifest and generator inventory

On input19acbfdd2aff80a0d9bf26127e67d676339a04d4, prepared
tests/fullscope-20261104/vx1/manifest-rescope/all30-proposal.json. Exactly30
former exclusions are proposed as model/missing open obligations, preserving all
localEvidence and upstream locations and retaining old decisions in before records.
Missing is a conservative catalog inspection status, not a claim that existing
fragments do not exist. Requirements now state full-language obligations rather
than withdrawn profile exclusions. Every affected upstream family/symbol reference
is recorded. Active generated outputs remain untouched until the generator owner
decouples unsupported diagnostics from scope. No H38 freeze or producer completion
is inferred.

ADAPTERS.md inventories render_lean/render_lean_info, decision validation, report
rendering and Source outsideDiagnostic/ScopeScan boundaries, plus BlockField
consumers. VY5 alone owns Source. Changing scope must not bypass unsupported
construct rejection or weaken existing admission certificates. H70 routes Source
review to VY5 and EVM/resource review to V14/V15; H67 pins stay coordinator-owned.

Checks: proposal check.py PASS30 exact transitions, original provenance/evidence
and all affected ledger references; solidity-feature-audit.py --check PASS212
features/783symbols, active baseline still30 exclusions. This is staged source
work, not regenerated-catalog readiness, kernel proof, compiler/EVM evidence or
whole-lane completion. No Lean code/import change or heavy build in this increment.

Independent read-only finder confirmed exact30 rows and provenance; found the
initial consumer census omitted Source.unmodelled?. Fixed by adding Source:306,
ScopeScan admission/diagnostic and compiler-artifact boundaries to ADAPTERS.md.
Independent skeptic found no blocking scope/provenance defect and recommended
explicit unchanged category/syntax assertions; added them to check.py. Neither
review used Lean/server/builds; skeptic ran the lightweight Python checker.

## VX1 G01 (cloud move5-20261106): OOM fix, frozen D1–D6, generator adapter

Lane moved from the Codex VM lane `solidity-fullscope-20261104/vx1-contracts-environment`
(H75); branch `cloud/move5-20261106/vx1-g01` from `cloud/move5-20261106/vx1-base`
(`d2a9a040`), which already contained `origin/master` (`5f7bb144`).

### OOM hold: the module over the bound

Measured on a cold full build (`LEAN_NUM_THREADS=1 ./run-lean.sh`, 4 cores,
15 GiB, no swap) with a `/proc/<pid>/status` VmHWM sampler (0.2 s) over every
`lean` process. `Solidity/Backend/Scalar/PowerBounds.lean` (from master's
v13-abi-world increment, `0bf90a41`) peaked at **7877 MiB, 203 s**: 32
`decide +kernel` row checks in one module, at the 8 GiB pre-gate bound once
Lake's own memory is counted. Every lane touching the library root rebuilds it.
The second module near the bound is `Solidity/Source/Horizon.lean` (same
increment): **7447 MiB, 201 s**. The full table of modules over 4 GiB is at
the end of this section.

Fix (`[oom-fix]` commit `cb07a2c3`): `scripts/backend-scalar-thresholds.py`
now emits `PowerBounds/Part01`–`Part08` (four widths each: rows
`naturalThresholdRow<w>` and `rowBounds<w>`, no longer `private`) and
`PowerBounds.lean` assembling `naturalThresholds`, `threshold_bounds`,
`thresholdWord(_nat)`, `exponentWord(_nat)` with unchanged statements and
proofs. Constants, statements and row proofs are unchanged up to placement
(multiset and order checked); the 64 row names lose `private`. Parts measured: Part04 2099 MiB / 26 s, Part08 2337 MiB / 26 s;
`--check` of the generator and `check-backend-scalar.mjs` pass.

Second fix (`[oom-fix]` commit `ce77a3f1`): `Source/Horizon.lean` is now the
linear chain `Horizon/Below` → `Horizon/Grow` → `Horizon/Const` → `Horizon`
(the Approx layer and its `#guard_msgs` axiom pins), cut at its own section
boundaries; every original line is present in order and only module
preambles and docstrings were added, so importers of `Solidity.Source.Horizon`
see the same declarations. Measured: Below 2182 MiB / 51 s, Grow 3871 MiB /
90 s, Const 1440 MiB / 26 s, Horizon 4091 MiB / 105 s (batch, one thread).
This touches a VY5-owned file under the assignment's OOM authorization only.

Third fix (`[oom-fix]` commit `75fea01c`): `Frontend/Checked/UnitExamples.lean`
peaked at **7972 MiB, 129 s**. Its corpora move to `UnitExamples/Corpus`, the
per-program `decide +kernel` certificates to `UnitExamples/Parsed`,
`ProfileParsed` and `ProfileExprParsed` (made public, otherwise unchanged);
`UnitExamples.lean` keeps the exactness lemmas, the pinned
`allCtors_covered`/`profileCtors_covered` (pins unchanged, `#guard_msgs`
passes) and the controls. Measured batch, one thread: Corpus 2008 MiB / 23 s,
Parsed 2355 MiB / 38 s, ProfileParsed and ProfileExprParsed under 3726 MiB /
34 s and 19 s, UnitExamples 2610 MiB / 20 s.

Fourth (partial) fix: `Examples/Tactics/OpenLoops.lean` measured **9108 MiB,
469 s** standalone (one thread). `binomialRowsNine` moves unchanged to
`Examples/Tactics/OpenLoops/RowsNine.lean`; `OpenLoops.lean` now builds in
10 s. `RowsNine` with its original `chunk := 128` peaked at 8992 MiB / 457 s;
with `chunk := 64` it peaks at **5876 MiB but takes 594 s**. The chunk size is
the only proof change (`sol_prove (chunk := n)` re-checks the same walk; each
chunk is still kernel-checked). The 8 GiB bound now holds; the 300 s bound does
not: the time is the walk itself, and meeting it needs the walk checkpointed
across modules, which `sol_prove (chunk := n)` (`Calculus/ProveChunked.lean`,
tactic owner) does not offer. Open, owner request below.

Cold-build table (`run-lean.sh`, `LEAN_NUM_THREADS=1`, Lake running four jobs,
VmHWM sampled every 0.2 s over 6415 modules; times are under parallel load and
exceed standalone times). Rows over 5 GiB after the splits above (the split
modules themselves are listed in their fixes):

| Module | Peak MiB | Seconds |
|---|---|---|
| `Solidity/SortCheck/Faithfulness.lean` | 6427 | 61 |
| `Solidity/Examples/Tactics/RevertData.lean` | 6163 | 118 |
| `Solidity/TestSuite/Derived21.lean` | 5990 | 66 |
| `Solidity/TestSuite/Derived7.lean` | 5428 | 86 |
| `Solidity/Yul/Views/MemberDynamicSequence.lean` | 5357 | 13 |
| `Solidity/Yul/Views/MemberDynamicBoundaryControls.lean` | 5326 | 9 |
| `Solidity/Examples/Tactics/CallSharingDefault.lean` | 5297 | 73 |
| `Solidity/Examples/DecisionHashThreeKinds.lean` | 5290 | 31 |

Next by time: `Examples/Tactics/Recursion.lean` 296 s (2741 MiB) under load,
at the time bound; not changed here.

### Frozen G01 relation contracts D1–D6 (`FullScope.V1`)

`Solidity/Language/EnvironmentFields/Frozen.lean`, namespace
`Solidity.Roadmap.FullScope.V1`, over the unchanged definitions of
`Solidity.Language.EnvironmentFields.Contracts`. A later change is a `V2`
namespace with an adapter (H57); V1 is never edited in place.

Consumer declaration names (vt1, vo1 and every X/O/T lane):

| Name | Kind | Meaning |
|---|---|---|
| `V1.Alignment source target` | `abbrev` (Type) | the producer's operational resource alignment |
| `V1.D1 source target domain machine compiler environment aligned` | `abbrev` (Type) | `RunIndexed.Certificate … .exact` |
| `V1.targetRunOf` | `def` | the target run a certificate assigns to an eligible source run |
| `V1.D1.forward_oracle`, `V1.D1.backward_oracle` | theorems | executed queries read the actual target reader |
| `V1.D2 attempt` | structure (Prop) | `failures : CreationSizeFailures attempt` (EIP-170/3860), `live`: some fitting creation succeeds |
| `V1.fieldRead`, `V1.fieldsDisjoint`, `V1.creationFitsDecidable` | defs, instance | low-order-first packed field content; byte disjointness; decidable limits |
| `V1.Layout`, `V1.Layout.Agrees`, `V1.MemoryAgrees`, `V1.Physical`, `V1.Physical.Representable` | defs/structures | D3 data |
| `V1.D3 physical` | structure (Prop) | `agrees` on related states, `total` on representable ones, `live`: some representable state |
| `V1.Assembly`, `V1.D4 assembly` | structure, structure (Prop) | `writeback : UnsafeWriteback …`, `opaqueBlocks : Opaque …`, `live`: some execution and some unsafe block |
| `V1.D5 source target environment`, `V1.d5_of_certificate` | def, theorem | environment correspondence; every certificate proves it |
| `V1.D6 …` | `abbrev` (Type) | `RunIndexed.Certificate … .optimizer` |
| `V1.Mode.observe_le`, `V1.Mode.observe_optimizer`, `V1.D1.toD6` | theorems/def | quotient monotone, idempotent; exact ⇒ optimizer |
| `V1.Contract source target domain machine compiler environment aligned mode attempt physical assembly` | structure | `run`, `admitsSome`, `creation`, `layout`, `assemblyBoundary` |
| `V1.Contract.compiles`, `V1.rejecting_refused`, `V1.forward_completes` | theorems | totality, rejecting compiler refused, adequacy on completion |

`Solidity/Language/EnvironmentFields/FrozenControls.lean`
(`V1.Controls`): `witness` and `optimizerWitness` inhabit the whole bundle
(joint satisfiability, H62/H69) with an admitted input, an executed gas query,
a successful completion matched by the target (`witness_live`,
`oracle_live`), creation success at the limits (`creation_at_limits`) and a
representable nonzero layout (`d3_live`). Negative controls:
`rejecting_refused`, `reverting_refused` (both modes), `empty_relation_refused`,
`shifted_relation_refused`, `overlap_refused`, `rewriting_optimizer_refused`,
`extra_event_refused` (an extra non-gas observation with equal gas reads and
outcome fails in both modes), `always_failing_refused` (D2),
`nothing_admitted_refused` (an empty domain with a compiler compiling nothing).
`tests/fullscope-20261104/vx1/FrozenAxioms.lean` inventories 24 declarations:
only `propext`/`Quot.sound`. MCP diagnostics: no errors or warnings on all three.

Binding for consumers: vt1's `fun_<name>_<id>` simulations state their
correspondence as a `V1.Alignment` plus `RunIndexed.SourceRuns`/`TargetRuns`
and conclude `V1.D1` (or `V1.Contract`); vo1 binds X01/D6 by `V1.D6` (from
`V1.D1.toD6` for passes that are exact) and D4's `opaqueBlocks`.

### Generator adapter

See `tests/fullscope-20261104/vx1/manifest-rescope/ADAPTERS.md`, "Generator
adapter": a patch for the generator owner, identity on the active catalog,
staged and kernel-checked 30-row transition, seven mutation controls.
Activation waits for VY5's `ScopeScan.certify` to test `unmodelled?` first; the
active catalog (`docs/solidity-features.json`, `FeatureInfo.lean`,
`Features.lean`) is unchanged.

Use the qualified names (`V1.D1.toD6 c`, `V1.forward_completes c …`): `V1.D1`
and `V1.D6` are abbreviations of `RunIndexed.Certificate`, so dot notation on
a certificate value does not find the `V1` lemmas.

Limits of the freeze, stated rather than hidden: D2–D4 are over the producer's
own `attempt`, `Physical` and `Assembly`; `V1.Contract` does not tie them to
the target's operational semantics (each producer's adapter does). The joint
witness is a toy whose source and target share one execution function with
trivial guards; its value is that every field is inhabited at once with live
domains, not that the fields constrain each other. A "gas-only difference
passes D6 but fails D1" control is not constructible in the run-indexed design:
the coupled transcripts force the source oracle to read the target's gas
values in both modes, so the quotient only matters for gas observations that
are not oracle reads.

### Reviews (finder, skeptic; read-only, no Lean server)

Skeptic: C1 partially holds (D3/D4 could be vacuous through the producer's
choice of state types, extent or an empty `executes`/`isUnsafe`); fixed by the
`live` fields of `D3` and `D4`. C2 partially holds (degenerate toy, missing
non-gas-change control); `extra_event_refused` added, degeneracy and the
gas-only control recorded above. C3–C5 hold; fixed the doc's "byte-identical"
wording, section numbering and the dot-notation caveat.

Finder: A1 (an empty `Admitted` with a compiler compiling nothing satisfied
the bundle) fixed by `Contract.admitsSome` and `nothing_admitted_refused`; A2
(always-failing `attempt`, empty D3/D4 models) fixed by `D2.live`, `D3.live`,
`D4.live` and `always_failing_refused`; A4 fixed by keeping the D3 helpers and
the instance named inside `V1`. Remaining by design, recorded as limitations:
`V1.D3` allows `Var := Empty` (a contract without state variables) and does
not state that steps preserve `Related` (the producer's simulation proof does);
`admitsSome` does not say *which* inputs are admitted (G07 ties `Admitted` to
the catalog); the toy's guards are `True` and `legality` is `Iff.rfl`
(exercised non-trivially by the earlier `specified_run_cannot_be_filtered` in
`tests/fullscope-20261104/vx1/ContractsControls.lean`); the H38 Source (VY5)
and EVM (V14/V15) reviews of `Legal`/`Aligned` are not recorded in this
repository, so the freeze stands on the coordinator's VX1 assignment. Adapter
E1 (generated `inProfile`/`outsideScope` still scope-only), E2 (anchor not
checked), E3 (`python -O`) and E4 (`Admission/Profile.lean` census) fixed in
the patch, `adapter.py` and ADAPTERS.md. PowerBounds and registration: no
defect.

### Gates (VX1 G01, final)

- MCP diagnostics: `EnvironmentFields/{Frozen,FrozenControls}.lean`, `Source/Horizon.lean`,
  `Frontend/Checked/UnitExamples.lean` and parts, `Backend/Scalar/PowerBounds.lean`:
  no errors; `tests/fullscope-20261104/vx1/FrozenAxioms.lean`: 24 declarations,
  only `propext`/`Quot.sound`.
- `gate.sh touched` (origin/master): PASS, 472 s.
- `gate.sh checkpoint`: build-touched, library, examples, trust, orphans, layers,
  roots, fragments PASS; doc-paths FAIL (pre-existing:
  `after-roadmap-va1.md` cites a missing Mathlib file, another lane's doc);
  axiom-pins FAIL (pre-existing: 0 errors, 4379 unrecorded changes; pins are
  coordinator-owned, H67).
- `./run-lean.sh`: Lean build of all default targets and `SolkeyTestSuite`
  without errors; `check-solkey.sh` against the unpinned `../solkey`
  (`5c448df`) FAIL with 167 mismatches (upstream drift); pinned rerun against
  the `473da8944c` snapshot (`SOLKEY_RULES=tests/migration/solkey/…/solidityProgramRules.key`)
  PASS: "annotations match", 131 read-bearing.
- `adapter.py --stage`: identity, 8 mutations rejected, staged hashes stable;
  `check.py`, `solidity-feature-audit.py --check`,
  `backend-scalar-thresholds.py --check`: PASS.


### H121 resumed ownership and G01 backward completion increment

H121 reverses H75: ownership/edit permission returns to VX1. Exact transferred
base90e39f89a80c7eeec08a65f1e5b91399e168bc5e was fetched and ancestry from
e70b959 verified. Original local headfaecbd6f3a61077bb11f61a8e62778b534303904
is preserved at refs/vx1-preserved/pre-h121. Adoption29bd60869c58887f78366b936ca44acc7dfb1ede
and master mergee4ae46e6ae5aa9b9d8684e2a26dd72085f5c85af retain all histories.
Master inputa8f684928fa085d8976ead33e3d0db30208e7a4f.

Merge repairs: retained transferred PowerBounds split generator rather than
restoring the old monolith; reused master's published HorizonFuel/HorizonGrow/
HorizonConst implementation, leaving transferred Horizon/Below,Grow,Const
as import-only compatibility modules. Separate read-only finder confirmed no
duplicate declarations in the shims. No Source semantics or frozen ExtCall edits.

Consequences.lean proves backward_completes and backward_exact from unchanged
V1/RunIndexed.Certificate fields. Existing compiled-artifact, eligibility, guard
and completion premises remain exact. Completed backward prefix refinement
becomes equality under mode.observe; exact mode retains all bytes and events.
CompletionControls.lean exercises gasquery5/nonempty success[5] and rejects
completed success[6] as a prefix of success[5]. Four actual axiom inventories
contain only propext. No production adequacy instance is claimed.

Separate finder/skeptic reviews found no semantic/premise defect in these
consequences or controls; both were read-only, without Lean/server/builds. An
initial control annotation failed OfNat target.lang.Res5; explicit Word fixed
it. Final bounded per-file PASS: KeySort1.689s, Frozen10.350s, Consequences0.942s,
CompletionControls0.469s. Actual Lean4.24.0/797c613 and Lake5.0.0-src+797c613.
Docker memory.max8589934592/swap.max0, LEAN_NUM_THREADS1, explicit-j1.
Cgroup peaks respectively128999424,296951808,115306496,92405760bytes; zeroOOM.
AggregateRSS sampling is retained for consequences/controls only; historical
missing RSS samples are not reconstructed. No checked module exceeded60s.

The cross-module frontier prototype is retained as the non-module fixture
tests/fullscope-20261104/vx1/checkpoint/Checkpoint.lean.txt, not kernel-checked.
Its per-file prerequisite attempt stopped180.002s at the approved extra
prerequisite bound, cgrouppeak836644864bytes, zeroOOM, before reaching the draft.
No retry/cold rebuild extends that allowance. Existing artifacts retained.
Static finder/skeptic confirm preservation of all ordered residuals, failed-cut
propagation and reconstruction via Proves.of_cutWithin; per-input step bounds
do not bound a whole frontier, and opaque receipt theorems are needed to avoid
replaying previous checks. Declaration export, progress checks, terminal closure
and original RowsNine reconstruction remain open. H121's reported memory split
measurements are coordinator evidence, not freshly reproduced here.

Current open contract boundaries: V1.D2 models creation limits but does not itself
state exact Osaka charging; D3 is a generic physical correspondence rather than
a full solc-reserved-memory/layout/word-machine refinement; D5 corresponds
environments without auditing all predicates as crypto/chain-only; admitsSome
does not establish a live eligible execution in an arbitrary instance. These
are open producer/relation obligations, not completed proofs or new exclusions.
Frozen V1 statements were not changed. H38 owner review receipts remain absent.

Shared registration/map proposal is h121-registration.json; COORD must register
Consequences. Native-browser owns H127 runner/registration repair: merged roots
still default-import RowsNine despite H109. Do not delete the obligation or
claim CI delivery. Remaining exact per-file/full gates need current source-bound
cache; central pins remain COORD. Original all30 active regeneration and X02
production queue remain open; transferred adapter.py/patch are staged work.

Post-merge generator consistency exposed master's Elab.async=false directive
retained in PowerBounds.lean but absent from the transferred split generator.
Updated only the generator header template to reproduce that existing directive;
no generated Lean declarations or proof budgets changed. Generator --check PASS.

Final narrow finder/skeptic reviews confirm generator scheduling-header repair
changes no numerical generation, declaration or proof, and no unbuilt checkpoint
Lean module remains in the library. Draft text is explicitly not validated.


### H121d independent premise and exact gas/layout accounting

At input9229b4c7db79640293d693e86e229888f828d10b fetched origin/master
65e69b6426a9a4fc3fb5541f41726a4bfefda5d0; it is already an ancestor.
No duplicated producer implementation, new language premise, theorem alteration
or frozen V1 edit. Coordinator confirms handoff/checksum retrieval, but no cache
pull, full gate or registration integration receipt.

Current Source owner is H125 solidity-inline-assembly5-20261031/vy1-words;
previous VY5 ownership requests above are historical. H121b aggregate lifecycle
remains V10. V14/V15 review requests are staged for coordinator forwarding, not
reported as delivered. Native-browser slow-library request was relayed.

The premise-audit inventory records30 distinct accounting items (not the30
feature rows), source-pinned to7 interface/implementation files. Every item
retains status open-production-linkage. approved-family labels identify only
permitted crypto/chain premise families; they do not approve arbitrary Fixed
functions, Allowed/Admissible/Forward/Guard predicates or producer instances.
The four entries cover per-run source hash non-collision, bounded hashed-region
non-overlap, specified crypto functions and quantified chain inputs. No global
hash injectivity, no arbitrary gas oracle and no additional language restriction
is authorized.

Exact gas accounting findings: V1 D2 states code-size failures and a live
attempt, not an operational Osaka schedule. allButOne64 exists but does not
prove actual CALL accounting. StipendRule.Fitted is an obligation to prove,
not an extra assumed public premise. Memory expansion, warm/cold access,
precompile costs, refunds and resource failures still need target operational
linkage; query agreement alone does not prove cost correctness. D6 preserves
the permitted gas quotient but proves no improvement. Legacy pinned disables
four Osaka limits; D2 explicitly supersedes the two code-size idealizations.
Transaction/block gas-limit differences need existing chain-premise/producer
accounting; this audit authorizes no waiver or changed decision.

Exact layout accounting: intrinsic ByteMemory and reserved-range constants
exist, but constants alone enforce no solc state initialization/update discipline.
Generic Layout disjointness is not solc packing/layout-at agreement; generic
D3 correspondence is not a word-machine/byte-memory refinement. Reachable-state
representability, actual storage/transient accesses and transaction lifetime
remain producer obligations. Unsafe writeback must cover all actual exits and
prove MemOK recovery rather than assume MemOK there; generic executes/isUnsafe
predicates and toy live witnesses are not operational adequacy.

Predicate accounting: legacy SourceSpec records allowed_iff, forward_iff and
guard_iff obligations. Concrete Source.sourceLang documents uninstantiated
failures/hash/stipend with trivial resource/Forward/Guard defaults. Neither
this source alone nor the abstract V1 bundle establishes production D1-D6.
Legality/coverage bind specified runs structurally, but actual independent
Specified/Aligned predicates still need owner review. admitsSome does not prove
a live eligible guarded Forward success for arbitrary instances.

Check.py verifies exact30unique IDs, reviewed dispositions, four permitted-family
entries, open status, source digests, exact anchor occurrences/lines and current
Source/lifecycle owners. It rejects9corruptions: missing/duplicate entry, gas-as-approved-
premise, unproved completion, source digest drift, line drift, invented anchor
stale Source owner and stale lifecycle owner. Both normal and Python-O checks pass; no assert-based
validation is stripped. This is reproducible interface accounting, not a semantic
proof of the prose, axiom-closure audit, compiler/EVM test or new admission claim.
No Lean source/import changed and no heavy build was run for this increment.
Frozen V1 and production gate obligations remain unchanged.

Separate finder/skeptic reviews independently confirmed7source hashes and30
anchors and found no substantive accounting or new-premise defect. Both were
read-only without Lean/server/builds; skeptic ran the lightweight checker.
Their checker findings are fixed: source-pin counts are computed, lifecycleV10
is validated, and a ninth stale-lifecycle-owner mutation is rejected. Prose
truth remains a reviewed conclusion, not something hashes alone prove.


### Consequences map registration and H121 route correction

Coordinator explicitly assigns the Consequences roadmap fragment row to VX1.
Added it to roadmap.d/vx1-contracts-environment.md and regenerated the combined
map with scripts/coord-tools/fragments.sh. The existing root import is retained.
The row describes conditional backward-completion/exact-observation lemmas,
not production adequacy. No Lean source/import or frozen V1 change.

Current H121 EVM/resource routes supersede the historical owner strings in the
sealed premise audit: V14 items go to Codex v17-validation-release; V15 items
go to Codex executable-bytecode. The router now delivers directly. Source
remains H125 vy1-words; aggregate lifecycle remains V10 under H121b. H127
slow-library work remains solidity-directruntime-20261104/native-browser.
The Consequences fragment-row dependency is resolved locally by this commit;
no producer review, cache delivery or full gate is inferred.

Separate read-only finder/skeptic reviews found no defect in the row, generated
map or routing correction; neither used Lean/server/builds. fragments.sh --check,
register.sh --check and git diff --check PASS. check-doc-paths.sh PASS: every
backticked Lean reference resolves (142 ambiguous references reported globally).
This documentation-only increment adds no Lean verification claim.


### H82 independent non-vacuity control and H71/H70 receipt

Fresh master65e69b6426a9a4fc3fb5541f41726a4bfefda5d0 is already an ancestor.
Added tests/fullscope-20261104/vx1/EmptyDomainControls.lean: a concrete V1.Contract
with the existing operational source/target meanings, oracle readers/resources
and existing live D2/D3/D4 witnesses, but Allowed=False on both sides. The input
is admitted and compiles; no source/target run is eligible and no eligible source
success exists. This kernel-checked limitation witness substantiates auditP10.
It is not production adequacy, approval of empty chain domains, a weakened public
theorem or a change to frozen V1. Concrete producer linkage must independently
establish actual chain environments/live eligible runs.

Per-file gate PASS0.486s, cgrouppeak91734016bytes, zeroOOM; all5new declarations
use only propext. Docker8GiB/no-swap, LEAN_NUM_THREADS1/explicit-j1, parent4GiB
reserve monitored. Initial unresolved phantom resolved indices caused elaboration
errors; explicit resolved/art indices fixed them. Initial diagnostic sorryAx
outputs were error recovery, not accepted evidence; final inventories have none.
Separate read-only finder/skeptic confirmed the countermodel and boundaries;
neither used Lean/server/builds. No production source module/import changed.

RowsNine classification is proposal-ready per H71 native-browser head567e3b81;
central15member registration and proof-cost acceptance remain pending. Exact-SHA
Git fetch failed authentication; no producer commit/file was adopted or falsely
reported independently verified. The forwarded module-times report at
/workspace/h62-coordinator-inputs/router-20261107T135033Z/module-times-605db6b63.md
is present and independently SHA256-verified459990b2682acdbef2f3c34e337360c64be9b69debf81a90aa6ae6be0b2bc739.
Its relevant H70/H116 sections were read. Receipt boundaries are recorded in
rowsnine-receipts.json. Historical594sSTOP remains; H116600sCI is only Derived17
cumulative replay, never a RowsNine budget increase.

H82 statement-preserving consumer repair: TrustAudit.lean explicitly imports
OpenLoops.RowsNine, whose binomialRowsNine it already audits. Parent does not
import child. The audited declaration list is unchanged; no root, runner, pin,
statement or budget is edited. Static import resolution only, not a full trust
audit pass: compiling the slow child remains blocked by its known budget and
missing exact-source ProveChunked cache. Native-browser retains classification/
runner ownership; central registration/planner/control work is not claimed done.

Separate narrow finder/skeptic reviews confirm the TrustAudit edit is exactly
one child import: audited declarations, trust policy and budgets unchanged.
Both independently confirmed the forwarded report hash and receipt boundaries;
neither ran Lean/server/builds or a slow audit. Static import-diff and receipt
hash checks PASS; full trust-audit execution remains pending.


### H70/H133 authenticated original proposal receipt

Coordinator delivered the original RowsNine registration proposal at
/workspace/h62-coordinator-inputs/router-20261107T141332Z/rowsnine-registration-original.json.
Read and independently SHA256-verified5594f73f12c8c07555e35f475d2dd3dd694b509926f67845210147ddb57fa0b3;
module identity is OpenLoops.RowsNine. The earlier failed Git retrieval remains
historical; this delivered file closes only that original-proposal receipt gap.
The newer helper-ticket hash mismatch remains unresolved and is not substituted.
No code adoption, central registration, proof acceptance, integration, new cache
or performance STOP release follows from delivery.

Coordinator confirms EmptyDomainControls was read/hash-verified and relayed
verbatim to H125 vy1-words. Current H133 EVM/resource owners are
solidity-v12-v17-20261031/v17-validation-release (V14) and
solidity-parallel-20261103/executable-bytecode (V15). Prior native-browser
request is retained without another ping; H127 runner/planner ownership stays.
No independent runnable item established: wait for actual eligible Source runs/
environments and admission linkage; EVM/resource operational linkage; exact-source
ProveChunked cache, generator adapter and central15member RowsNine integration.
H82/H90b/H112 statements, dependent definitions, interfaces, budgets, axioms and
exclusions are unchanged. This increment maintains receipts only.

Separate read-only finder/skeptic independently verified original-proposal hash
and module identity, found no receipt/routing defect, and confirmed no acceptance
or STOP-release claim. Neither used Lean/server/builds. JSON parsing, exact hash/
module checks and git diff --check PASS; no new Lean verification was run.
