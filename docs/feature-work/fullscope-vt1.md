# VT1 full-scope handoff — interface checkpoint in progress

Base and committed HEAD: `e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`.
Branch: `codex/solidity-fullscope-20261104/vt1-solc-validation`.
Repository: `/workspace/solidity-lean`. Original clean `work` branch preserved at
`9c44a2f9acbdddba82d56a693eb7dba6e8eb8028`. Fetch of origin/master succeeded;
base ancestry check exits 0. No push, reset, merge, or implementation edits.

## Historical bootstrap blocker (recovered below)

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

## C02: exact IR channel extraction and owned fixture backfill

Status: locally kernel-checked extraction component; T01 and T02 remain partial.
This section supersedes historical bootstrap statuses. Original base remains
`e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3`; C01 dialect interface is committed at
`78d97c92956c1ef50f974f09a24bdbbe1b078570`. Same assigned branch/VM, no push.

`Frontend/SolcJson/IrImport.lean` selects a contract by its exact source/name and
retains the requested `ir` or `irOptimized` String with equality certificates.
The raw JSON source is parsed by Lean's existing JSON parser. This is not a
parser for Yul bodies or a proof of compiler authenticity. `irOptimized` here
is the requested output channel with optimizer.enabled=false, not a separate
optimizer-enabled build. Neither mode tags nor hashes authenticate execution.

Exact theorem statements and premises (all parameters universally quantified):
- `Selection.sound {contract : Lean.Json} {mode : IrMode} (selection : Selection contract mode) : contract.getObjValAs? String (field mode) = .ok selection.text`
- `Selection.complete {contract : Lean.Json} {mode : IrMode} (selection : Selection contract mode) : select contract mode = .ok selection`
- `ContractSelection.sound {output : Lean.Json} {source name : String} {mode : IrMode} (selection : ContractSelection output source name mode) : lookup output source name mode = .ok selection.selection.text`
The first two use no axioms; the third reports only propext. Selection records
carry exact lookup derivations; no producer semantics/proofs are assumed.

Pinned compiler SHA-256 matches the repository's 0.8.38 pin. Census.sol combines
constructor immutables, linked library call, checked arithmetic/exponentiation,
signed division, ABI dynamic bytes, storage push/pop, and Osaka CLZ. Saved
standard input/output and four raw IR strings cover two contracts/two channels.
Lexical census finds 296 function declarations (including duplicate names in
different object scopes); no semantic scope resolution is claimed. Source IDs
for the eight unoptimized fun_* declarations are cross-referenced to the saved
compiler AST (13, 55, 69, 90, 99, 109, 124, 133); this is external name/ID
association, not intrinsic Stmt matching. Helpers remain semantically unmatched.

Six compiler-rejection controls assert exact diagnostic types/messages, with a
positive literal-memoryguard control. Nine mutation controls reject altered bytes,
wrong compiler/source metadata, mode swaps (including rehashed), and rehashed
census/diagnostic/source-ID/control-input alterations. The verifier establishes
bundle consistency against the saved output/source/specification; coordinated
forgery of all artifacts is not excluded by checksums. Kernel controls separately
exercise exact mode, wrong field type, missing mode, wrong source and wrong
contract without falling back to a valid alternative. Four actual saved IR strings
pass through Lean's JSON parser and exact-channel extraction unchanged.

Reviews: separate read-only finder/skeptic, no Lean server. Fixed source-comment
function names inflating census (312 to 296); exact diagnostic assertions;
verification-only path and rehashed mode controls; recomputed census and AST ID
crosswalk; exact negative-control requests; and wording preserving String rather
than raw serialized JSON bytes. Both final reviews confirm all reported findings
resolved within this component's stated boundary. No semantic adequacy is claimed.

Validation: `bash tests/fullscope-20261104/vt1/check-import.sh`, exit 0.
Per-command logs/exit/wall/sampled aggregate RSS are under evidence/import/.
Maximum recorded aggregate RSS 303394816 bytes; cgroup peak 188370944 bytes in
that run (RSS sums may double-count shared pages). All commands serial, one CPU,
LEAN_NUM_THREADS=1, explicit -j1, each <=180s, group capped at 300s, no swap,
12 GiB hard cap, 4 GiB admission/ongoing reserve guard. Per-file MCP diagnostics
on Dialect, IrImport and IrImportChecks all report zero errors; bounded MCP stopped
before other checks. No full cold build has run. No maxHeartbeats/axiom/exclusion
changes. Lean errors during implementation were corrected without weakening proofs.

Static gate logs in evidence/gates/: layers, trust (3837 sources, 285 sites,
zero findings), axiom pins (7385 existing pins, no errors), and doc paths pass.
Existing-pin gate does not register the new theorems: their explicit inventories
above accompany the central proposal. Roots/orphans/module-map gates fail on the
two new modules because COORD owns registration. Proposal is registration-proposal.md.
Full run-lean and integrated final closure remain pending; no H35 readiness.

Cache-helper probe with SHIP_ALLOW_HEAD=1 and the configured cache fails because
`/home/agent/.local/state/cloudvm-coord/poll-state.json` is absent. Export a
source/toolchain/checksum-bound kernel artifact packet and request host helper
transfer. Shipment is not delivered without a coordinator receipt.

Open queue remains: full object/Yul parsing and provenance; dialect operation
semantics and lowering (all seven compiler-only operations plus complete core
EVM interpretation), object/static validity, immutable/link layout, physical
memory writeback and Osaka resources; T02 typed matcher and every helper/function
simulation, dispatcher/constructor composition; frozen X01/G01 and VX4 integration;
semantic/combination controls; final builds/inventories/reviews/cache receipts.
No new exclusion, weakened observation, assumed producer proof, or closure claim.

Raw fixture whitespace: git diff --cached --check reports trailing blank lines
in two compiler-emitted unoptimized IR files. Preserve exact compiler Strings;
source/script whitespace checks exclude only raw *.yul fixtures and pass.

## C03: adopted integration and checked object-data reference adapter

Original base remains e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3. Published
master 8495f1deb0a95dd6b9301822d8649ab76b217681 was fetched, its ancestry in
origin/master verified, and merged without conflict. Merge head before C03 was
904ba9fbf1a1f9d52f07d2e0fd53ac66d7da18b5. Both earlier owned commits remain
ancestors; no reset, replacement VM, push or protected producer edit occurred.
Read integration-20261105-checkpoints.md. Newly integrated Yul physical/world
components do not freeze VX1 H38, establish final VX4 adequacy or close T01/T02.
No local cache shipment receipt for sched-20261105T0200Z was found; the notice
is not cache freshness evidence. The owned checks below use observed warm artifacts.

DataLayout.lean adds static `DataRef artifact` (word offset, word size and an
actual in-bounds interval), `DataTable artifact` (intrinsically unique names),
and membership-carrying `DataSelection`. DATASIZE returns the actual selected
bytes' length without truncation; DATAOFFSET retains the assembled position.
Each selected byte is proved equal to the actual artifact byte. Present labels
are never discarded. Static references do not restrict dynamic DATACOPY/CODECOPY
bounds; no dynamic copy semantics, object-label association or layout authenticity
is claimed. No owner proof/producer is assumed. Canonical nested names, parsing,
object assembly and memory/gas/resource composition remain required work.

Exact theorem signatures/premises, namespace Solidity.SolcValidation:
- `DataRef.bytes_length {artifact : List DataByte} (ref : DataRef artifact) : ref.bytes.length = ref.size.val`
- `DataRef.datasize_exact {artifact : List DataByte} (ref : DataRef artifact) : ref.datasize.val = ref.bytes.length`
- `DataRef.dataoffset_exact {artifact : List DataByte} (ref : DataRef artifact) : ref.dataoffset = ref.offset`
- `DataRef.byte_exact {artifact : List DataByte} (ref : DataRef artifact) (i : Nat) (inside : i < ref.bytes.length) : ref.bytes[i] = artifact[ref.offset.val + i]` (the RHS bound proof is derived from ref.within and inside)
- `DataSelection.sound {artifact : List DataByte} {entries : List (String × DataRef artifact)} {label : String} (selected : DataSelection entries label) : (label, selected.ref) ∈ entries`
- `selectData_complete {artifact : List DataByte} {label : String} {entries : List (String × DataRef artifact)} (selected : DataSelection entries label) : (selectData label entries).isSome = true`
Axiom sets are inventoried in registration-proposal.md and measured-4.log:
only the standard propext/Quot.sound where listed; no new axiom/sorry/native_decide.
DataRef.within and table uniqueness are intrinsic static validity, not new
premises in a final compiler-correctness theorem or language exclusions.

Pinned ObjectData.yul assembles to 14 bytes, SHA-256
625580c50946ed8ad35484c59775596a7844fa335282e78adc84834bc10b5883.
The final three bytes 11 22 33 at offset11 inhabit a checked DataRef/table.
Kernel controls cover actual bytes, size, offset, present/missing labels,
zero-length endpoint, impossible out-of-range reference and duplicate table.
The compiler rejects unknown/duplicate labels with exact pinned diagnostics.
`generate-object-data.mjs --check` recompiles and compares saved JSON and Lean
witness without writes; three mutation tests reject altered source, artifact
bytes and generated witness. This establishes fixture coherence, not compiler
correctness, source-label association or target EVM execution.

Finder and skeptic reviews were separate/read-only, with no Lean/server. They
confirmed interval/static-vs-dynamic boundaries and found a fixture-coherence
gap. Fixed via read-only recompilation/comparison and mutation tests. Added
unknown/duplicate-label compiler and intrinsic negative controls. Finder's final
minor constant-generation concern was fixed by deriving interval constants from
assembled length and the witness mutation from the actual offset. Both reviews
found no other concrete defect within this component's scope.

Revalidation on adopted integration: check-dialect.sh passed Lean/Lake/KeySort
and syntax witnesses. `VT1_EVIDENCE_STAMP=integrated-8495 bash tests/fullscope-20261104/vt1/check-data.sh`
and the corresponding check-import.sh both exit0. New logs are separate under
evidence/data-integrated-8495 and evidence/import-integrated-8495; historical
C02 logs remain unchanged. New data group max sampled aggregate RSS304947200
bytes; cgroup peak171831296 bytes. Import group max RSS305623040 bytes;
cgroup peak186585088 bytes. Every check serial, one CPU, LEAN_NUM_THREADS=1,
-j1, <=180s/command and 300s/group, MemoryMax12GiB/swap0, 4GiB reserve guarded.
Per-file bounded MCP on DataLayout and ObjectDataChecks: zero errors; server
stopped before other checks. Full builds and final H35 readiness remain open.

Registration proposal now includes the third module. Central roots/maps/trust
pins were not edited. Existing C02 stub relay and cache transfer receipts remain
pending. T02 relations still wait for frozen X01/G01; no unfrozen stub is proved
against. All remaining T01 object/parser/operation semantics, physical memory,
immutable/linker layout and T02 helper/function/contract simulations remain open.

C03 static gates on adopted master: layers pass (628 enumerated core modules),
trust passes (3926 sources, 287 sites, zero findings), existing axiom pins pass
(7546 pins, no unrecorded changes), documentation paths pass. Root/orphan/map
gates fail only on the three owned modules awaiting central registration.
These failures remain open; no full-build or H35 checkpoint readiness claim.

## C04: follow-on adoption and exact unique-reference resolution

Fetched and verified f77cf60d3cea8f7f1db8db29cc027532b0cd3fce as an ancestor of
origin/master, then merged cleanly on the same owned branch. Merge head before
C04 was c6c98f031131609683646c0a94db2e69c54841e4. All prior VT1 commits are
preserved; original base remains e70b959bf6dd81d09bfaf6eda8025b1cc98bc4c3.
Read integration-20261105-deferred.md: no final expression-uniqueness proof,
ExtCall adequacy or frozen VX1 H38 relation is supplied by these increments.
No protected Source, Core ExtCall, owner modules, roots/maps or trust pins edited.

DataResolution.lean consumes the committed C03 interface without changing it.
Uniqueness of names now proves equality of references, and the actual resolver
reproduces the exact supplied membership witness. Missing names cannot fall back
to another entry. This does not certify source-object/path association, object
assembly, runtime memory or simulation; those remain required.

Exact public signatures/premises in namespace Solidity.SolcValidation:
- `DataTable.selection_unique {artifact : List DataByte} (table : DataTable artifact) {label : String} (left right : DataSelection table.entries label) : left.ref = right.ref`
- `DataSelection.ext {artifact : List DataByte} {entries : List (String × DataRef artifact)} {label : String} (left right : DataSelection entries label) (same : left.ref = right.ref) : left = right`
- `DataTable.select_complete {artifact : List DataByte} (table : DataTable artifact) {label : String} (selected : DataSelection table.entries label) : table.select label = some selected`
- `DataTable.select_iff {artifact : List DataByte} (table : DataTable artifact) (label : String) : (table.select label).isSome = true ↔ ∃ ref, (label, ref) ∈ table.entries`
Table uniqueness and membership are intrinsic, explicit static validity; no
compiler/producer proof or final-run equality is a premise. Inventoried axiom
sets are respectively [propext, Quot.sound], [], [propext, Quot.sound], [propext].
No new axiom/sorry/native_decide, exclusion, observation or budget change.

Pinned assembled-object witness now has two unique labels at different references:
a zero-length endpoint and the nonempty payload. Controls exercise exact tail
lookup, arbitrary competing selection uniqueness, empty head lookup and absent
name failure. Existing interval/duplicate controls, compiler diagnostics and
three source/artifact/witness mutation controls still pass. No intrinsic Stmt
match or source-level simulation is inferred from these data-reference witnesses.

Separate read-only finder and skeptic reviews found no concrete defect; neither
used Lean/server. Both confirmed explicit uniqueness, proof irrelevance, exact
resolver completeness and the stated separation from compiler label association.
Bounded per-file MCP diagnostics for DataResolution and ObjectDataChecks report
zero errors, with server stopped before subsequent checks.

Revalidation commands:
- check-dialect.sh: exit0, actual Lean/Lake and KEYSORT_PASS after adoption.
- `VT1_EVIDENCE_STAMP=integrated-f77 bash tests/fullscope-20261104/vt1/check-resolution.sh`: exit0; source/axiom/witness/control logs under evidence/resolution-integrated-f77. Max sampled aggregate RSS296464384 bytes, cgroup peak171814912 bytes.
- Corresponding check-import.sh: revalidates earlier IR extraction and fixtures on f77; separate logs under evidence/import-integrated-f77.
Serial explicit -j1 / LEAN_NUM_THREADS=1, one CPU, <=180s each and 300s group,
hard12GiB/swap0, 4GiB admission/ongoing reserve, no simultaneous Lean server/build.

Cache prerequisite request: source-hashed missing .olean closure for
Solidity.Backend.Environment.ByteConstants is in evidence/cache-request-f77/.
Initial local scan found14 missing oleans. A bounded cache-only attempt
`lake --no-build build +Solidity.Backend.Environment.ByteConstants:olean`
fetched Opcode, Jumpdest, Assembler and Secp256k1, then exited3 because AST and
Eqns are out of date. --no-build prevented recompilation; there was no cold
foundation rebuild or proof-budget extension. Request the exact compatible
cache closure through H21, including current AST/Eqns sources whose hashes are
recorded. Some cache hits do not establish global H21 freshness/delivery.
This holds the next physical-byte consumer while frozen VX4/G01 interfaces and
memory adequacy also remain open. Do not invent their stubs or assume proofs.

The registration proposal includes all four owned modules. No full-build or H35
checkpoint readiness is claimed before central registration, integrated gates
and cache delivery receipts. Existing relay requests for C01/C02/C03 remain
pending. Full T01 parsing/operation execution and T02 helper/function/contract
simulations, plus all previously enumerated final controls and obligations,
remain open; this component is not whole-lane completion.

C04 static gates: layers pass (636 enumerated core modules), trust passes
(3942 sources, 287 sites, zero findings), existing axiom pins pass (7590 pins,
zero errors/unrecorded changes), documentation paths pass. Root/orphan/map
gates fail on four owned modules pending central serialized registration.
Existing-pin success does not register the new theorems. New theorem inventories
and registration rows are supplied in the proposal; final build/cache readiness
remains open. Import revalidation max sampled RSS318464000 bytes, cgroup
peak188448768 bytes.
