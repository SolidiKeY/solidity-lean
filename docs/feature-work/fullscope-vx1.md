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
