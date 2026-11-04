# VX1: contracts and environment fields

Base: `e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`.
Branch: `codex/solidity-fullscope-20261104/vx1-contracts-environment`.
Repository: `/workspace/solidity-lean`.

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
