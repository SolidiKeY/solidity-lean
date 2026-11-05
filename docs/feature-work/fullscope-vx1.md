# VX1: contracts and environment fields

Base: `e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`.
Branch: `codex/solidity-fullscope-20261104/vx1-contracts-environment`.
Repository: `/workspace/solidity-lean`.

Current status: H38 resolved Q-ORACLE-01 by authorizing option 2. The run-indexed proposal is source/kernel checked and submitted for producer review; full X01 freeze/readiness remains pending. Earlier blocking-question sections below are checkpoint history.

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

### Blocking API question and complete queue accounting

ESCALATE `Q-ORACLE-01` [X01/G01, D1/D6]: the complete oracle/resource alignment
API is missing. Artifact/environment-only readers are insufficient, as the
checked counterexample and both reviews showed. D1–D6 and both refinement
directions remain binding. Choose one implementation path:

1. Obtain a joint Source/EVM producer signature before freezing the full
interface; retain the independent proofs and fixtures completed here.
2. Authorize VX1 to propose a run-indexed contract binding artifact, oracle and
resources, subject to producer review before freeze.
3. Authorize VX1 to propose an explicit oracle/resource-alignment adapter around
existing G01 contracts, subject to producer review before freeze.

This is required by the assignment's human-only design/producer-API rule; no
option is treated as approved, and no option changes the settled D1–D6 decisions.

| Queue item | Accounting |
| --- | --- |
| X01 full committed interface/stubReady | Blocked on Q-ORACLE-01 and producer alignment; provisional definitions and independent proofs committed, no freeze/relay readiness claimed. |
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
