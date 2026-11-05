# VT1 full-scope handoff — interface checkpoint in progress

Base and committed HEAD: `e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`.
Branch: `codex/solidity-fullscope-20261104/vt1-solc-validation`.
Repository: `/workspace/solidity-lean`. Original clean `work` branch preserved at
`9c44a2f9acbdddba82d56a693eb7dba6e8eb8028`. Fetch of origin/master succeeded;
base ancestry check exits 0. No push, reset, merge, or implementation edits.

## Runtime blocker

Lean reports 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b);
Lake reports 5.0.0-src+797c613 (Lean 4.24.0). KeySort is pending,
so RUNTIME_GATE_PASS is not claimed. No Lean server tool is available.
User systemd scope fails without session bus; system scope fails because
PID 1 is not systemd. Cgroup root is not writable. Existing memory.max is
17179869184, memory.swap.max is max. Host reports no swap, but this does not
establish the mandatory process-group hard cap. No heavy checks were run.
Repair requested: delegated 12 GiB / zero-swap cgroup or working systemd
scope on this SAME executor. Do not replace executor or relax the contract.

## Queue and evidence

T01 dialect/import interface and implementation remain open. T02 matcher
interface, per-function simulation and contract compositions remain open.
All owned backfill (real pinned solc fixtures, dialect/helper census, negative
controls, inhabited matches, provenance) remains open. Final VX4 memory and
X01/G01 integration checks remain open. No theorem or premise has changed.
No stubReady is claimed. Exact producer APIs must be obtained before freezing
consumer interfaces; do not substitute existing partial relations for D1–D6.
Finder/skeptic milestone reviews, axiom inventory, controls, final gates,
cache export and patch are pending. This is setup evidence, not a ready checkpoint.
Historical evidence not present in this checkout is UNVERIFIABLE.

Commands and exact exit/output: `tests/fullscope-20261104/vt1/evidence/setup/commands.json`.
The goal tool exposes stop_goal but no get_goal in this session.

## Coordinator Docker fallback follow-up

Coordinator authorized Docker 12g memory/12g memory-swap, one CPU, uid 1000.
Managed local Unix-socket daemon reports Docker 28.4.0. No active containers
were present before probing. `ubuntu:24.04` was absent. A run with the exact
coordinator flags began pulling library/ubuntu layer 7a48b8f0e5c7; inner cgroup
values have not yet been observed. Thus runtime envelope and KeySort remain
pending. No heavy Lean check has started.

Owner requests: X01 must provide committed D1–D6/G01 typed relations and
artifact/gas parameters (path, commit, signatures) for the T02 consumer;
VX4 must provide the committed physical byte-memory view/writeback interface
for T01 final checks. Existing Roadmap.Contracts and Yul.World.ByteMemory
are partial predecessors, not evidence of the newly required contract.
Producer-owned files remain untouched. No design change is proposed.

Docker bootstrap timed out: observed 325 seconds without completed image pull.
Only owned client PID 940 was terminated; daemon preserved. Exact probe status
is in `tests/fullscope-20261104/vt1/evidence/setup/docker-probe.json`.
Repair/retry the same executor image pull; no replacement is authorized.

## 2026-11-05 runtime recovery and dialect syntax interface

Coordinator instructed infrastructure retry after 600 seconds; more than that
interval elapsed before retry. Docker ubuntu:24.04 pull succeeded (digest
sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852).
Inside the authorized container memory.max=12884901888, memory.swap.max=0.
Lean 4.24.0 and Lake 5.0.0-src+797c613 reported; KeySort check exits 0.
RUNTIME_GATE_PASS applies to this verified runtime check only. Heavy checks
remain serial, explicit -j1 / LEAN_NUM_THREADS=1, with writer lock and 4 GiB
admission reserve. No full build or final readiness is claimed.

`Solidity/SolcValidation/Dialect.lean` defines `ObjectOp : Nat → Nat → Type`,
`Op : Nat → Nat → Type`, `IrMode`, `Object Code`, and `IrArtifact Code`.
The dynamic arities of object operations are datasize/dataoffset/loadimmutable/
linkersymbol 0→1, datacopy 3→0, setimmutable 2→0, memoryguard 0→1; labels and
memoryguard's literal size are metadata. EVM operations embed Yul.Builtin
without copying the owner table. IrArtifact enforces a code-bearing root.
Intended consumers: VT2/VT3/VT4 dialect/import preparation. This is syntax only.
T02 relation interface still awaits frozen G01 relations; unfrozen 06f5ae081
is not consumed. No parsing, object validity, execution or simulation claim.

Exact theorem signatures, no premises beyond indicated arguments:
- `evm_name {a r : Nat} (op : Solidity.Yul.Builtin a r) : (Op.evm op).name = op.name`
- `mode_distinct : IrMode.optimized ≠ IrMode.unoptimized`
Both #print axioms reports say no axioms. Tests inhabit operation names and
an object-root artifact; these are syntax witnesses, not simulation witnesses.

Missing Builtins.olean was compiled as one serial prerequisite, then interface
checks used the warm artifact. First interface check found an incorrect recursor
motive; it was corrected. No proof budget or theorem was weakened.

Separate finder and skeptic reviews (read-only, neither using Lean/server) both
found memoryguard's literal-only requirement and a data-root artifact hole.
Finder additionally tested solc's literal diagnostic in memory. Both were fixed
in the intrinsic interface; mode comments were narrowed as skeptic requested.
Both reviewers rechecked and found no further concrete syntax-interface defect.
Remaining: object name resolution/validity, parser provenance, interpretation,
layout/gas adequacy, all T02 simulations and final integration dependencies.

Check command: `bash tests/fullscope-20261104/vt1/check-dialect.sh`.
Exit 0, KEYSORT_PASS, DIALECT_INTERFACE_PASS; cgroup peak 111190016 bytes.
This is not full H35 readiness: full builds, negative/combination controls,
module-registration proposal, trust inventory/cache shipment remain open.
