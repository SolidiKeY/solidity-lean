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


## C05 — full-path IR lookup completeness and controls

Coordinator follow-up on published master8bf8321873befa3f35ca31e97e5339a1baee93e6.
Adopted in merge d666751e260c6fdcc9d2446751009a010b329ff6, preserving the
original branch and RawBool checkpoint. No source producer or shared registry
edit. This additive proof/controls checkpoint leaves original full T01/T02 and
all recorded physical-memory/G01/interface/compiler obligations open.

`Ir.select_lookup` erases the channel certificate to the exact ordinary lookup
on both success and error. `Ir.selectContract_lookup` does the same for the full
contracts/source/name/channel path, with arbitrary JSON and no success premise.
`Ir.ContractSelection.complete` assumes only
`lookup output source name mode = Except.ok text` and constructs an actual
selection with `selectContract ... = Except.ok selection` and exact text. Old
statements and extraction implementation are unchanged. Complete quantified
signatures are in ImportFollowup/Signatures.lean and its measured output.

`Solidity.Frontend.SolcJson.IrImportControls` supplies22 kernel controls: decoy
source/contract, both channels, exact newline/quoted text, empty-string success,
missing contracts/source/name/channel, null path components, wrong field spelling,
number/bool/null/object channel types, inhabited completeness and no fallback.
The partial Lean JSON parser is tested externally (escaped text and malformed
JSON) in ParserChecks.lean; it is not a kernel parsing theorem. The unchanged
saved real-solc output test reports IR_CHANNEL_FIXTURES_PASS4. Neither JSON
selection nor these controls authenticate solc, parse Yul or establish T02
simulation. No new premise, exclusion, axiom, sorry, native_decide or budget lift.

Separate read-only finder and skeptic reviews used no Lean/server or writes.
Both found no concrete defect: completeness only assumes ordinary lookup success,
error strings are preserved, decoy controls discriminate exact paths, and the
parser/compiler boundary is explicit. Initial dependent-case proof elaboration
failures were fixed with match splitting and channel erasure, retaining the
statement. Constructor inference in the executable parser check was fixed with
explicit Json.str. Initial attempted parser reduction controls were moved to
executable checks because Json.parse is partial; no kernel parsing claim is made.
All failed diagnostics/build logs are retained alongside successful evidence.

Final per-file MCP diagnostics:0 errors each, stopped before builds. Individual
import check0.490s/RSS332505088 bytes; controls2.196s/RSS332779520 bytes. External
parser0.345s and real-fixture0.469s pass. Axiom inventory covers all28 theorems
(six importer plus22 controls), only existing propext/Classical.choice/Quot.sound.
Fresh runtime: Lean4.24.0 (797c613), Lake5.0.0-src+797c613. KeySort exit0,0.936s:
RUNTIME_GATE_PASS. No module above60s in these focused checks.

Reproduction tools are scoped in tests/fullscope-20261104/vt1/ImportFollowup/.
They use the previously verified Docker12GiB/no-swap/CPU1 envelope, explicit
Lean-j1/LEAN_NUM_THREADS1, writer lock, observed aggregate RSS, max one Lean
frontend,4GiB admission/ongoing reserve and unchanged180s file/300s group guards.
Lake CLI lacks-j; scope-local TOML adds-j1 to frontend weakLeanArgs. The copied
configuration changes no tracked root configuration or generated registry.

After committing, required gate.sh touched/checkpoint run at that committed HEAD;
exact commands, outcomes, wall/RSS, gate HEAD and all failures are sealed in the
scoped seal/HANDOFF.md. Per-file success is not checkpoint readiness. Coordinator
owns generated roots/maps/pins: register the new IrImportControls module and
new theorem inventory; original IrImport is now centrally registered. RawBool
registration requests and its separately sealed handoff remain unchanged.
H41: export a verified source/toolchain/checksum-bound cache packet for pull;
never run ship-cache.sh on this VM or claim delivery without a receipt.

## Moved lane on a Claude VM (2026-11-05)

The lane moved from the Codex VM to a Claude cloud session. Branch
`cloud/moved4-20261105/vt1-solc-validation`, started at origin/master
`aec9adf1` (which already contains the Codex head 70845978). Codex-only seals
and evidence directories (H44) are not reachable and are not cited below.

Compiler access on this VM: `binaries.soliditylang.org` is refused by the
network policy (HTTP 403); the npm `solc@0.8.38` package's `soljson.js` hashes
to `0b15fcb2…2fa6c`, not the pinned `6c74ffba…2d390`, and running downloaded
compiler code was refused by the session's permission policy. So no compiler
was run here: every real-solc check below uses the committed outputs in
`tests/fullscope-20261104/vt1/fixtures/` (produced on the Codex VM by the
pinned binary, recorded in `manifest.json`). A fresh re-run with the pinned
binary remains open work.

## C06: certifying parser for solc IR text

`SolcValidation/IrSyntax.lean` is the intrinsic syntax of solc's object-dialect
Yul: expressions indexed by their exact number of returned words, contexts as
lists of names (locals) and signatures (functions), calls as memberships,
`Args` of exact length, the dialect's `Op` (core `Yul.Builtin` plus
`ObjectOp`), `Ctl` making misplaced `leave`/`break`/`continue`
unrepresentable, function groups hoisted over their block (`Block.mk`), bodies
typed over their parameters and returns only, `for` initializers scoping over
condition, post and body (`Loop`). Literals carry their decoded word with a
proof (`Lit.decoded`): numbers below 2^256, strings of at most 32 bytes
left-aligned.

`SolcValidation/IrParse.lean`: `lex`, an untrusted recursive-descent parser,
and `parse : (text : String) → Except String (Parsed text)`. A `Parsed text`
carries `lexed : lex text = some tokens`, `printed : objectToks root = tokens`
and `wellFormed : objectWf root = true`, both checked on the result.
`objectWf` is the scoping/static check (canonical first-binder resolution of
every variable and call, no shadowing of visible variables, functions or
reserved names, each function body printed exactly once in order, nonempty
distinct `let`/assignment names, switch with a case or default and distinct
case values, no function in a for initializer, no `pc`, distinct object member
names). `Mem.eq_of_index` shows a checked position determines the membership.

Theorems (namespace `Solidity.SolcValidation.IrSyntax`):
- `Parsed.sound {text : String} (p : Parsed text) : lex text = some (objectToks p.parts.root) ∧ objectWf p.parts.root = true` — axioms [propext].
- `Mem.eq_of_index {α : Type} {L : List α} {x : α} (m₁ m₂ : Mem L x) : m₁.index = m₂.index → m₁ = m₂`.
- `Parsed.artifact_root` (the artifact root is the parsed object).

Trusted boundary: `lex`, the printer `objectToks`, `objectWf`. Numbers are
compared by value (`0x80` and `128` are the same token); comments are not
provenance. Refused although solc accepts them (open): single-quoted strings,
unescaped non-ASCII in strings, hex literals as expressions, `_` in numbers,
plain-string `data`. Object names and operation labels are raw text (escapes
not decoded). Gate G0's kernel-speed conditions are not applied: this tree is
evaluated by compiled code; kernel controls use inputs of a few dozen tokens.

`SolcValidation/IrCensus.lean` lists, per object path, the function
definitions and operation uses read off the tree.

Checks (`tests/fullscope-20261104/vt1/IrParseChecks.lean`, MCP diagnostics,
0 errors): 47 kernel `rfl`/`decide` controls (positive: hoisting, multi-return,
for-init scope, switch/default, nested data, object ops, comments; negative:
unknown function, builtin/user arity, discarded value, shadowing, undeclared
target, misplaced leave/break, local capture, literal ranges, string data,
data root, trailing brace, malformed number, plus the review-driven rules
below; a census shape control). All four saved real IR texts parse
(Census unoptimized 4679 tokens / 130 functions, optimized 4552 / 124,
LinkedMath 633 / 22 and 605 / 20) and their function census equals
`fixtures/census.json` per artifact (296 in total), as does `ObjectData.yul`.
Seven mutations of the real Census IR (renamed builtin, dropped argument,
non-literal memoryguard, unbalanced brace, top-level leave, shadowed local,
undeclared target) are refused.

Reviews (read-only, no Lean server). Skeptic: certificate sound, but binding,
function-name freshness and the census rested on the untrusted parser
(unprinted `Mem`, phantom bodies without markers); G0 tension; controls only
checked success. Finder: duplicate/builtin-named/shadowing functions accepted;
switch without cases; duplicate cases (including different spellings of one
word); function in a nested for-init block; duplicate assignment targets;
leading-zero decimals; `\b \f \v \u` escapes refused; raw labels; `pc`.
Fixed in 494266f1: `objectWf` added to `Parsed` and checked (covers all rule
findings), lexer refuses leading zeros, escapes `\b \f \v \uNNNN` (UTF-8)
decoded, census structural (kernel-evaluable), 17 new controls including tree
shape. Documented instead of changed: raw labels, single quotes, hex
expression literals, G0 (rationale above), census comparison is per artifact
because `census.json` has no per-object rows.

## C07: execution of the object dialect

`SolcValidation/IrEval.lean`: a fuelled interpreter over the C06 tree.
Intrinsic values `Vals L` (one word per name in scope), function environment
`FunEnv` mirroring the lexical stack of groups (recursion through the group's
own environment), right-to-left argument evaluation, `Flow` for
leave/break/continue, faults `halt state reason` / `stuck reason` / `fuel`.
Pure builtins use `Solidity.Yul.Pure.eval`; every other EVM builtin is
delegated to `Machine σ`, supplied by the consumer (the VY4 world or the VX4
byte memory). `ObjectCtx` holds the assembled artifact with a checked
`DataTable`, immutable positions and values, and link addresses. No owner
module is edited.

Theorems (namespace `Solidity.SolcValidation.IrSyntax.IrEvalLaws`, all
parameters universally quantified, axioms [propext, Quot.sound]):
- `datasize_exact (k) (env) (vs) (s) (l) (sel : DataSelection ctx.table.entries l) : evalExpr M ctx (k + 2) env (.op (.object (.datasize l)) .nil) vs s = .ok (s, fun _ => sel.ref.datasize)`
- `dataoffset_exact` (same, `sel.ref.offset`), `datasize_missing` (absent label ⇒ `.error (.stuck …)`)
- `memoryguard_value`, `loadimmutable_value`, `linkersymbol_value`
- `datacopy_codecopy (n) … : evalExpr … (.op (.object .datacopy) args) … = evalExpr … (.op (.evm .codecopy) args) …`
- `pure_value`: a pure builtin returns `Pure.eval p xs` on the evaluated arguments, state unchanged beyond them
- `setimmutable_stores`: exactly one `mstore` of the value per recorded position, offset-relative, in order.

`SolcValidation/IrEvalFuel.lean`: `eval_succ (k)` — for all eight mutually
recursive evaluators, a result other than `Fault.fuel` at fuel `k` is the
result at `k + 1`; `evalBlock_stable`, `runCode_stable (n m) (le : n ≤ m) …
(conclusive : runCode M ctx n code s ≠ .error .fuel) : runCode M ctx m code s
= runCode M ctx n code s`. Axioms [propext, Quot.sound].

Executable witnesses (`tests/fullscope-20261104/vt1/IrEvalChecks.lean`, a
bounded test machine with byte memory, storage and the repository's
`Solidity.Keccak`, no gas or calls): for both contracts and both IR channels,
the parsed constructor code, run with the saved creation bytecode as code,
returns the saved `deployedBytecode` with the constructor argument at the
immutable positions; constructor storage holds `values = [5]`. The copied
bytes equal the saved runtime by construction of the data table, so this
checks the IR's plumbing (which label it copies and returns, constructor
argument decoding through `datasize(<object>)`/`codesize`/`codecopy`,
`setimmutable` offsets relative to the copy buffer, storage), not the copied
content; link bytes are placed by the test and `linkersymbol` is never
executed. The saved bytecode was assembled from `irOptimized`, so for the
`unoptimized` channel the byte comparison is plumbing only. Runtime: `arithmetic(3,4) = (7, 81)`, add and exponent
overflow Panic(0x11), `signed(-7,2) = -3`, division by zero Panic(0x12),
`signed(min,-1)` Panic(0x11), `assemblyWord(1) = 255` (clz), `seed() = 5`
through `loadimmutable`, `push(9)` with storage `[5, 9]`, `echo` ABI
round-trip (runtime code and the seed read back from the constructor's
output), value sent to a non-payable function, unknown selector and short
calldata revert, `LinkedMath.twice(21) = 42` and its overflow panic; a
missing label is `stuck`. Artifact facts are derived without a compiler by
`generate-artifacts.py` (`--check` verifies) from `fixtures/output.json`:
deployed offset, link offsets, immutable positions as zero `PUSH32` operands,
each cross-checked against a `PUSH2 <pos>` in the creation code.
This is test evidence for the dialect semantics, not a proof about the EVM.

Open in T01: the physical byte-memory machine (VX4/X06) and world (VY4) as
`Machine` instances and their composition; gas (D1/D2) — `gas`, `msize` and
memory expansion are the machine's; calls/creates; fresh compiler runs.

Reviews (read-only, no Lean server). Finder: interpreter clean in every
semantic area (right-to-left arguments with positional results, multi-value
assignment, return variables, leave at the call boundary, loops, switch,
scoping, recursion through `FunEnv.lookup`, object operations incl. offset
arithmetic mod 2^256 and `datasize` of the enclosing object); one low finding
(a machine could report `Fault.fuel`); five test findings (circular byte
comparison, heuristic immutable positions, unoptimized compared with
`irOptimized` bytecode, runtime seed not read from the constructor output,
`linkersymbol` never executed). Skeptic: fuel theorem holds; laws other than
`datasize_exact`/`dataoffset_exact`/`datasize_missing` restate definitions
(kept as the interface); "adapter over the core semantics" overstated (a
separate interpreter); `memoryguard` vs StackLimitEvader undocumented;
stringly halt reasons; `wordOfNat` duplicated `Yul.word`; witnesses not wired
to a script.

Fixed: `Machine.exec` now returns `MachineFault` (halt with a typed
`HaltKind`, or unsupported), so `Fault.fuel` is only the interpreter's horizon;
`Fault.halt` carries `HaltKind`; `Yul.word` reused; runtime calls read the
immutable from the constructor's returned code and run that code; immutable
positions cross-checked against creation-code `PUSH2`; wording in the module
docstrings, the test header and this section corrected (separate interpreter,
no relation to `ClosedRun` yet; memoryguard as emitted; what the byte
comparison tests). Still open: `immutableReferences`/`linkReferences` from a
fresh compiler run (needs the pinned binary), executing `linkersymbol` through
a call-capable machine, and a relation between this interpreter and the owner's
`Yul/ClosedRun.lean` semantics.

## C08: helper-level simulation (T02 first slice)

T02's relations to the source program wait for X01's frozen G01 relations, so
this checkpoint takes the part that does not: solc's checked-arithmetic
helpers matched to the source's runtime operators.

`SolcValidation/IrHelpers.lean` holds eight helper functions cut verbatim from
the saved IR (`extract-helpers.py`, `--check`; `fixtures/helpers.yul`):
`cleanup_t_uint256`, `cleanup_t_int256`, `panic_error_0x11`,
`panic_error_0x12`, `checked_add_t_uint256`, `checked_sub_t_uint256`,
`checked_div_t_int256` (Census) and `checked_mul_t_uint256` (LinkedMath). Their
tree was generated from the parser's output by `IrLeanGen.lean`, and
`helpers_certified : lex helpersText = some (objectToks helpersRoot) ∧
objectWf helpersRoot = true` is checked by kernel evaluation (`decide +kernel`;
axioms [propext]) — the same certificate a parse of that text carries.

`SolcValidation/IrHelperSim.lean` (any `Machine σ`, any state, any words):
- `checked_add_sim (k) (x y : Word) (s : σ) : evalExpr M ctx (k + 20) helperEnv addCall (argVals x y) s = if x.val + y.val < 2 ^ 256 then .ok (s, fun _ => word (x.val + y.val)) else (fun s => (s, fun _ => word (x.val + y.val))) <$> panicRun M 0x11 s` — through the call site, closure lookup and both cleanups.
- `checked_mul_body (k) (x y) (s) : evalBlock M ctx (k + 30) helperEnv bodyMul (.cons x (.cons y (.cons 0 .nil))) s = if x.val * y.val < 2 ^ 256 then .ok (s, …word (x.val * y.val)…, .normal) else … <$> panicRun M 0x11 s`.
- Arithmetic facts: `add_wraps`, `sub_wraps`, `mul_fits` (solc's `x = 0 ∨ y = (x·y mod 2^256)/x` check is exactly "fits"), `pure_sub_of_le`.
`panicRun` is solc's sequence `mstore(0, 0x4e487b71…)`, `mstore(4, code)`,
`revert(0, 0x24)` on the machine.

`SolcValidation/IrHelperSource.lean` (imports `Semantics/Ops.lean`):
`sourceAdd_eq`, `sourceMul_eq` compute `BinOp.evalNum .uint … .add/.mul`, and
- `checked_add_matches_source (k) (x y) (s) : match sourceAdd x y with | some v => evalExpr … = .ok (s, fun _ => word v.toNat) | none => evalExpr … = … <$> panicRun M 0x11 s`
- `checked_mul_matches_source` (same shape for the body of `checked_mul_t_uint256`).
Axioms [propext, Classical.choice, Quot.sound]. The relation between the
source's revert and the panic's return data is G01's and is not asserted.
What "simulation" means here, exactly: on success the helper returns the
source's value as a word with the machine state unchanged; on a source revert
the helper runs solc's panic sequence on the machine (it reverts only on a
machine whose `revert` halts). `checked_mul_matches_source` is about the
body entered with `product = 0`; the call-site form (lookup, argument binding)
is proved for add only. All proofs are about the helper group `helperEnv` of
the extracted `"Helpers"` object, not the contracts' own function groups:
transferring them needs a lemma that lookup in the parsed Census/LinkedMath
environment yields these bodies (open). The generated term carries the
parser's certificate, but uniqueness of a well-formed tree for a token stream
is not proved, so "these terms are the parse" rests on that certificate.

Tests (`IrHelperChecks.lean`, run by `check-ir.sh`): 576 helper/source
agreements on 12×12 edge words for add, sub, mul and signed div with the exact
effect log (for div the source gives only "reverts"; the panic codes 0x12 for
a zero divisor and 0x11 for `min / -1` are solc's, stated in the test);
`helpersText` equals the fixture and each of its 8 whole functions is a
verbatim substring of the saved IR.

Open (kernel): `checked_sub_t_uint256` and `checked_div_t_int256`. A proof
of the same shape as `checked_mul_body` elaborated for sub, but the kernel
reported deep recursion (the attempt is not committed): the owner's `Pure.sub`
(`word (x + 2^256 - y)`) and `sdiv` (`signed`, `x - 2^256`) put a symbolic sum
with the literal `2^256` where a defeq check unfolds it in unary — the same
family as Gate G0's `ofInt?` pitfall, which `IrHelperSource.lean` avoids with
`rw`-stated lemmas. Fix: carry the `Pure` values folded through a `rw`-proved
characterization (as `pure_sub_of_le`), or ask VY1 for `rw`-friendly `Pure.eval`
lemmas. Also open: `checked_exp_*` (the loop; would generalize `Evm/Exp.lean`),
ABI and storage helpers, `fun_<name>_<id>` bodies and dispatcher/constructor
composition (need G01), and the remaining helpers of the census.

Reviews (read-only, no Lean server). Finder: no defect in the proved
theorems (fuel cannot make them vacuous, the panic sequence and selector match
solc's `panic_error_0x11`, the certificate does tie `helperBodies` to the
text, the source side is `BinOp.evalNum` as `BinOp.evalT` uses it, the test
oracle is independent); findings on the provenance test (split on blank lines
skipped `cleanup_t_uint256` and every overflow check), a tautological Python
assert, `IrLeanGen` and `IrHelperSim` docstrings claiming more than is
proved, the hard-coded 0x12 expectation, and no runner. Skeptic: the same
provenance and runner findings; "simulation" must be read as "runs the panic
sequence", mul is body-level only, everything is about the extracted
`helperEnv` rather than the contracts' function groups, tree uniqueness is not
proved, full `simp` in finished proofs and untyped `have`s (AGENTS.md),
global `@[simp]` attributes.

Fixed: whole-function provenance check (8 functions, object closers
stripped), Python assert replaced by a whole-definition check, `check-ir.sh`
runs both fixture derivations and the three Lean check files, docstrings and
this section state exactly what is proved (body-level mul, synthetic
environment, no uniqueness, panic-sequence reading, solc's panic codes in the
div test). Then fixed with the Lean server: every finished proof in `IrHelperSim.lean`
uses `simp only` (from `simp?`), and the `have`s carry explicit types. The
global `@[simp]` attributes stay: all are `rfl`/`rw` facts about this lane's
own definitions (`Vals`, `Run`, `word2`) plus `rfl` restatements of `Pure.eval`
cases; they are recorded here for importers.

## Gates for C06–C08 (Claude VM)

Evidence: `tests/fullscope-20261104/vt1/evidence/claude-c06-c08/README.md`.
Per-file Lean diagnostics clean on all eight modules and four check files;
`check-ir.sh` (fixture derivations) passes; axioms standard only. The full
`./run-lean.sh` passed its static stages but its cold `lake build` (3808
modules, no Lake cache on this VM) was stopped at 143 modules: the full build
gate is not passed here and is open for the integrator's cached build.

## Continuation after the coordinator's follow-up (2026-11-06)

Merged origin/master `771a5fed` (merge `20078929`, no conflicts); after it
`register.sh --check`, `fragments.sh --check` and `check-layers.mjs` ("857 core
modules, 0 reach the elaborator") pass, and master changed nothing in this
lane's import closure (`AST`, `Yul/Builtins`, `Yul/Words`, `Semantics/**`,
`Roadmap/**`, `Syntax.lean`, `Hash/**`).

Full build: this VM's Lake cache holds only the 294 MB this lane built; no
master artifacts were delivered, so `./run-lean.sh` would again be a cold
~3800-module build (the earlier run reached 143 modules in ten minutes with
2 GB free). It was not rerun; the full-build gate stays open for a cached
environment.

`checked_sub_t_uint256` kernel proof, second attempt (not committed): the
body proof was restructured as the coordinator suggested — `Pure.eval .sub`
generalized to an opaque `f` (with its value lemma `pure_sub_val` as a
hypothesis) before any `if` is reduced, no `consFn_two`, `if_true`/`reduceIte`
replaced by `ite_normal`/`ite_self`. The kernel still reports deep recursion,
and bisection pins it to the first `ite_self`+`run_ok_bind` step that collapses
the `cleanup_t_uint256` call — the identical step succeeds in
`checked_mul_body`. So the cause is not `Pure.sub`'s `2^256` as first
diagnosed above; it is still unidentified. Next step: replace the one-shot
`simp` by per-statement lemmas (cleanup call, panic call, assignment) proved
once and composed with `rw`, so each kernel check is small. `checked_div_t_int256`,
`checked_exp_*`, ABI and storage helpers were not started in this
continuation.

## C09: the remaining helper proofs (follow-up session, 2026-11-06)

Base: branch head `9717636c` merged with origin/master `e5d25cb3` (no
conflicts). All proofs below are kernel-checked (per-file Lean diagnostics, no
`sorry`, no new axiom, no `maxHeartbeats` change); `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound` (or a subset).

**The earlier kernel deep recursion.** Bisection found a trigger, not a proven
cause: after unfolding the whole `checked_sub` body, `simp only [run_ok_bind]`
(rewriting under the large nested `do` continuation) already made the kernel
recurse too deeply, while the same step done by a statement-level lemma did
not. Other contributing causes are not excluded. The fix is the coordinator's
suggestion in its general form: `SolcValidation/IrHelperSteps.lean` proves one
lemma per statement shape over an abstract environment and abstract values
(`assign_cleanupU`, `assign_pure2`, `if_panic11`, `items_stmt_normal`,
`items_stmt_map`, `items_last`, `op1_gen`/`op2_gen` for call-free expressions at
any fuel above a bound, …) and composes them mostly with `rw` (some finished steps still use a bounded
`simp only` over one statement or one call), so each kernel check is small.
`sub` is kept folded and characterized by `pure_sub_val`/`sub_gt`; the
remaining `rfl`s on literals (`lit_min`, `max_lit_val`, `lit_val`) only compute
`literal % 2^256` on numerals.

### Checked arithmetic (namespace `Solidity.SolcValidation.IrSyntax`)
- `checked_sub_body (k) (x y : Word) (s : σ) : evalBlock M ctx (k + 30) helperEnv bodySub (.cons x (.cons y (.cons 0 .nil))) s = if y.val ≤ x.val then .ok (s, …word (x.val - y.val)…, .normal) else (fun s => (s, …Pure.eval .sub (word2 x y)…, .normal)) <$> panicRun M 0x11 s`
- `checked_sub_sim (k) (x y) (s) : evalExpr M ctx (k + 34) helperEnv subCall (argVals x y) s = if y.val ≤ x.val then .ok (s, fun _ => word (x.val - y.val)) else … <$> panicRun M 0x11 s` (call site).
- `checked_mul_sim` (the call-site form of `checked_mul_body`, closing C08's
  "body-level only" gap) via the generic `call2`.
- `checked_div_body (k) (x y) (s) : evalBlock M ctx (k + 60) helperEnv bodyDiv (…x, y, 0…) s = panicIf M (y.val == 0) 0x12 s >>= fun s => panicIf M (x.val == 2^255 && y.val == 2^256 - 1) 0x11 s >>= fun s => .ok (s, …Pure.eval .sdiv (word2 x y)…, .normal)`.
  `panicIf M b code s` is `panicRun M code s` when `b`, else `.ok s`: the first
  panic is not the last statement, so on a machine whose `revert` returns the body
  continues, and the theorem says exactly that.
- Source matches (`IrHelperSource.lean`, `BinOp.evalNum`):
  `sourceSub_eq`, `checked_sub_matches_source` (`uint -`, call site),
  `checked_mul_call_matches_source` (`uint *`, call site),
  `sourceDiv_eq`, `tdiv_inRange` (the `int256` range fact: `Int.tdiv` of two
  in-range values is in range unless `min / -1`), `checked_div_matches_source`
  (`int /`, words read by `Yul.signed`; a source value `v` is returned as
  `iword v`; a source revert is `panicRun M (if y.val = 0 then 0x12 else 0x11) s >>= …`).

### `checked_exp_t_uint256_t_uint256`
`IrExpHelpers.lean`: the six functions of the group (`checked_exp_t_uint256_t_uint256`,
`checked_exp_unsigned`, `checked_exp_helper`, `shift_right_1_unsigned`,
`cleanup_t_uint256`, `panic_error_0x11`), cut verbatim from the saved Census IR
(`extract-helpers.py`), printed from the parser's output (`IrLeanGen.lean`),
split by `gen-helper-modules.py` (`--check` in `check-ir.sh`), and certified by
`expHelpers_certified` (`decide +kernel`, the `Parsed.sound` statement).
`IrExpModel.lean`: `expLoop`/`expUnsigned`, a natural-number model of solc's
algorithm (special cases, the `(b < 11 ∧ e < 78) ∨ (b < 307 ∧ e < 32)` shortcut,
the square-and-multiply loop with its `base > max / base` test), and
- `expLoop_spec`: below an overflow the loop is exact with `1 ≤ p ≤ b` and
  `p * b ^ e` preserved; it panics only if `p * b ^ e ≥ 2^256`;
- `expUnsigned_correct (b e) (bW : b < 2^256) : expUnsigned b e = if b ^ e < 2^256 then some (b ^ e) else none`
  (including `306^31 < 2^256` and `10^77 < 2^256`, the shortcut's bounds).
`IrExpSim.lean`: the interpreter runs as the model, on any machine:
`loop_run` (strong induction on the exponent; fuel `j + steps e + 45`, with
`steps e ≤ 255` by `steps_le`), `helper_run`, `u1_*`…`u7_run` (the seven
statements of `checked_exp_unsigned`), `unsigned_run`, and
- `checked_exp_body (j) (x y : Word) (s : σ) : (x.val ^ y.val < 2^256 → evalBlock M ctx (j + 420) expEnv expExpU256 (…x, y, 0…) s = .ok (s, …word (x.val ^ y.val)…, .normal)) ∧ (¬ x.val ^ y.val < 2^256 → ∃ cont, evalBlock … = panicRun M 0x11 s >>= cont)`:
  no machine effect when the power fits. In the overflow case the `∃ cont` form
  is informative only when the panic sequence faults: in `Except` it is
  equivalent to "if `panicRun M 0x11 s = .error e` then the result is `.error e`",
  and it says nothing on a machine whose `revert` returns. Hence
- `RevertHalts M` (`IrHelperSteps.lean`: `revert` always halts with
  `HaltKind.revert`, a property the consumer's EVM machine proves; nothing
  assumes it unless it says so), `panic_factor_halts`, and
  `checked_exp_overflow_halts (j x y s) (h : RevertHalts M) (over) : ∃ e, panicRun M 0x11 s = .error e ∧ evalBlock … = .error e`:
  on such a machine the overflowing body ends exactly with the panic sequence's
  fault, from the entry state.
- `checked_exp_matches_source` (`IrHelperSource.lean`): the same against
  `sourceExp` = `BinOp.evalNum .uint … .pow`.
This is an analogue of `Evm/Exp.lean`'s square-and-multiply proofs for the
imported IR; no lemma relates the two yet (`Evm/Exp.lean` is not edited), so
"generalizes `Evm/Exp.lean`" (T02's wording) is not claimed.

### ABI and storage helpers (machine level)
- `IrAbiHelpers.lean`/`IrAbiSim.lean` (the five functions of
  `abi_decode_tuple_t_uint256`): `validator_body` (no effect: the `uint256`
  cleanup is the identity), `decodeU256_body`, and
  `decodeTuple_body (k) (h d) (s)`: with `short := decide (signed (sub(d, h)) < 32)`,
  `short = true → ∃ cont, evalBlock … = M.run .revert (word2 0 0) s >>= cont` (the
  same caveat as above; `decodeTuple_short_halts` gives the exact result under
  `RevertHalts M`) and
  `short = false → evalBlock … = (fun r => (r.1, …r.2 0…, .normal)) <$> M.run .calldataload (fun _ => h) s`.
- `IrPushHelpers.lean`/`IrPushSim.lean` (the thirteen functions of
  `array_push_from_t_uint256_to_t_array$_t_uint256_$dyn_storage_ptr`):
  `slice_zero` (`update_byte_slice_dynamic32(old, 0, v) = v`), `updateStorage_body`,
  `index_body`, and `push_body (k) (a v) (s)`: the body equals the explicit effect
  script `sload(a)`; `Panic(0x41)` if the length `l ≥ 2^64`; `sstore(a, l + 1)`;
  `sload(a)` again and `Panic(0x32)` unless `l <` that; `mstore(0, a)`;
  `keccak256(0, 32)` giving `h`; `sload(h + l)`; `sstore(h + l, v)` — each on
  the state the previous step returned, for any machine.
Provenance: `extract-helpers.py` cuts each function at its first occurrence in
`Census.unoptimized.yul`, so the push group comes from the creation object
`Census_134` (the constructor's `values.push`), and the exp and ABI groups take
`cleanup_t_uint256`, `validator_revert_t_uint256` and the `revert_error_…` helper
from the creation object and the rest from `Census_134_deployed`. The texts are
identical up to indentation in both objects, so the theorems are unaffected, but
no group is literally either object's function environment.
What a calldata word or a storage slot means for the source (ABI decoding and
solc's storage layout, D3) is G01's relation; these theorems state the exact
machine behaviour and assume nothing about the machine.

### Tests (`IrHelperChecks.lean`, Lean server)
`IR_HELPER_PASS 576` (unchanged), `IR_EXP_HELPER_PASS 144 checked_exp/source
agreements on edge words` (bases around 0/1/2/10/11/306/307/2^128/2^255/2^256-1,
exponents up to 300 so the oracle can compute `x ^ y`; larger exponents are
covered by the theorem), provenance passes for all four fixtures
(`IR_HELPER_PROVENANCE_PASS 8`, `IR_EXP_PROVENANCE_PASS 6`,
`IR_ABI_PROVENANCE_PASS 5`, `IR_PUSH_PROVENANCE_PASS 13`; each count is now
also checked against the definition lines of the text, and each name must be
defined exactly once). The exp test also checks that a fitting power leaves the
effect log empty. These provenance passes are secondary evidence: the
`*_certified` theorems are what tie each tree to its text. The Lean tests run
through the Lean server here, not through `check-ir.sh` (`lake env lean` is
denied in this session), and their machine halts on `revert`, so they do not
exercise a returning `revert`.
`VT1_SKIP_LEAN=1 check-ir.sh`: ARTIFACTS_CHECK_PASS, HELPERS_CHECK_PASS,
HELPER_MODULES_CHECK_PASS, VT1_IR_CHECKS_PASS.

### Still open
- `fun_<name>_<id>` simulations and dispatcher/constructor composition (T02's
  per-function and per-contract layer): they need X01's frozen G01 relations
  (source argument/return ↔ ABI words, revert ↔ return data, storage layout).
  Master has none frozen (only VX1's unfrozen stub), so they wait on G01; no
  stub is proved against.
- The helper theorems are about the extracted helper groups' own environments
  (`helperEnv`, `expEnv`, `abiEnv`, `pushEnv`), not the contracts' parsed
  function groups: transferring them needs a lookup lemma for the parsed Census
  tree (open, as in C08). Tree uniqueness for a token stream is still not proved.
- A fresh solc run is blocked: `binaries.soliditylang.org` returns 403 here and
  running an unpinned compiler is not allowed; the fixtures remain the Codex
  VM's pinned-binary outputs.
- The physical byte-memory machine (VX4/X06) and world (VY4) as `Machine`
  instances, gas (D1/D2), calls/creates: unchanged from C07.

### C09 reviews (read-only, no Lean server)
Finder: no high-severity defect. The Nat model matches the Yul text; the
statements, fuel and effect order (right-to-left arguments) match solc;
the oracle is independent. Findings: (1) the "generalizes `Evm/Exp.lean`" claim
was unsupported, so it was reworded as an analogue; (2) the provenance counts
were tautological, so they are now checked against definition lines, with
exactly-once names; (3) mixed creation/runtime provenance is now documented;
(4) about 30 untyped `have`s; (5) the exp test ignored the effect log, and now
requires it empty when the power fits; (6) `.term` regeneration is not in
`check-ir.sh`, so soundness rests on the certificates (known open:
tree uniqueness).
Skeptic: (1, must-fix) the `∃ cont, … = panicRun … >>= cont` form is vacuous on
a machine whose `revert` returns, so "first machine effect" overclaimed. Fixed:
`RevertHalts`, `panicRun_bind_halts`, `panicRun_error_of_halts`,
`panic_factor_halts`, `checked_exp_overflow_halts`, `decodeTuple_short_halts`,
plus reworded docstrings (`IrExpSim`, `IrHelperSource`, `IrAbiSim`) and this
section. (2) Provenance: documented. (3) Provenance checks: strengthened.
(4) Lean tests are run by the server: stated. (5) The deep-recursion wording
was too firm, so it is now stated as a bisected trigger; the `rw`/literal
wording was corrected. (6) The word-reading of source values is now stated in
`sourceDiv`'s docstring as this lane's choice, with the relation left to G01.
Not changed: the `have`s that instantiate a lemma (`body`, `hr`, `hu`, `hc`,
`t`, `t4`, `t5`, `spec`, `ih'`, `h`) stay untyped, because their type is the
cited lemma's statement and spelling it out would repeat large `match` terms.
The short ones are now typed, and the `have := …; rw … at this` patterns were
replaced by `rw`; exact.

### C09 gates
- Per-file Lean diagnostics (MCP), 0 errors: IrHelperSteps, IrExpHelpers,
  IrExpModel, IrExpSim, IrAbiHelpers, IrAbiSim, IrPushHelpers, IrPushSim,
  IrHelperSource, IrHelperSim, tests IrHelperChecks/IrLeanGen.
- `./run-lean.sh` (warm rerun after a cold run that hit the 2 h session limit;
  the cold run's two OOM kills, exit 137 in other lanes' `Yul/Views/MemberDynamicSequence`
  and `Examples/Tactics/OpenLoops`, came from running it next to the Lean server):
  static stages pass; `lake build` "Build completed successfully (6163 jobs)", 0
  errors; then `check-solkey.sh` against the unpinned sibling `../solkey`
  (b8d5f883) fails: "167 mismatch(es)" (taclets newer than the pinned table).
  Rerun with the pinned rules,
  `SOLKEY_RULES=tests/migration/solkey/…/solidityProgramRules.key scripts/check-solkey.sh`:
  "OK — annotations match" (377 taclets, 131 read-bearing, table covers 131), exit 0.
- `VT1_SKIP_LEAN=1 check-ir.sh`: VT1_IR_CHECKS_PASS. `check-doc-paths.sh`: 1
  failure, in another lane's `tests/calldata-packets-1105/RawUintN/README.md`.

## C10: Census-tree transfer, unique tables and the `Evm/Exp` link (follow-up 2, 2026-11-06)

Scope approved by the user (H66). Base: branch head `a1ba2cf2` merged with
origin/master (no conflicts). All proofs are kernel-checked; no `sorry`, no new
axiom, no `maxHeartbeats` change. `#print axioms` of the headline theorems gives
a subset of `propext`, `Classical.choice`, `Quot.sound`.

### 1. Lookup transfer onto the certified Census tree
- **The parsed trees as terms.** `IrCensusGen.lean` (test, Lean server) prints the
  parser's output for `fixtures/{Census,LinkedMath}.unoptimized.yul` as
  `fixtures/census-tree.txt`; `gen-census-modules.py` (`--check` in `check-ir.sh`)
  writes `IrCensusCreation.lean` (`Census_134`, 27 functions), `IrCensusDeployed.lean`
  (`Census_134_deployed`, 103), `IrLinkedCode.lean` (`LinkedMath_14` and its deployed
  object, 3 and 19) and `IrCensusTree.lean`, which quotes both fixture texts verbatim
  and proves `census_certified`/`linked_certified` (`lex text = some (objectToks root) ∧
  objectWf root = true`) by kernel evaluation (about a minute for Census).
- **The parser's own result.** `IrCensusParse.lean`: `linked_is_the_parse : ∃ p,
  parse linkedText = .ok p ∧ p.parts.root = linkedRoot`, by running the parser in the
  kernel and comparing through `IrErase.lean`'s erasure, which keeps every name,
  position, signature, operation and literal and is proved injective
  (`objectErase_inj`). The Census version is not proved: deciding the erasure of
  `parse censusText` exhausted the Lean worker (the kernel re-runs the unshared
  parse for every projection; deciding only its success takes about two minutes),
  so `censusRoot` rests on `census_certified`.
- **Renaming simulation.** `IrRename.lean`: `Ren F G` maps call positions partially;
  `Expr.ren … Bodies.ren` rename every call; `Sim k ρ E E'` relates environments up to
  fuel `k`; `evalExpr_ren`/`evalBlock_ren`: renamed code evaluates in `E'` exactly as
  the original in `E` (same effects, result and fault) at every fuel; `Sim.flat`
  discharges `Sim` for one top-level group from one body equation per function.
- **Lookup lemmas.** `IrCensusMaps.lean` (generated) maps each function of the four
  extracted groups to the function with the same signature in `cdSigs`, `ccSigs` or
  `ldSigs` (a wrong position does not elaborate). `IrCensusTransfer.lean`:
  `<group>_lookup_<obj>`: for every function of the group that the object defines, the
  object's body is exactly the extracted body with calls renamed — Helpers→`Census_134_deployed`
  (all but `checked_mul_t_uint256`), Helpers→`LinkedMath_14_deployed` (`cleanup_t_uint256`,
  `panic_error_0x11`, `checked_mul_t_uint256`), exp→Census deployed (all 6), ABI→Census
  deployed and LinkedMath deployed (all 5), push→Census deployed and Census creation
  (all 13); "the object's body" is `Block.ren … = some …`, i.e. the same text up to
  call positions. Every function a map sends to `none` is absent from the object's
  group (`<group>_unmapped_<obj>`, `IrCensusUnique.lean`, kernel), so each listed
  pair covers every helper the object defines. Pairs not stated: Helpers/ABI→`Census_134`
  and exp→`LinkedMath_14_deployed`, whose objects define only a cleanup, a validator or
  a panic of those groups. `sim_<group>_<obj>` follow by `Sim.flat`.
- **Headline theorems on the fixtures' trees** (each environment is the one evaluating
  that object's code installs: `cdEnv_installed`, `ccEnv_installed`, `ldEnv_installed`): `census_checked_add_sim`, `census_checked_sub_sim`,
  `linked_checked_mul_sim`, `census_checked_div_body`, the five `*_matches_source`
  forms, `census_checked_exp_body`, `census_checked_exp_overflow_halts`,
  `census_decodeTuple_body`, `linked_decodeTuple_body`, `census_decodeTuple_short_halts`,
  `census_push_body` (`push(uint256)`), `census_constructor_push_body` (the
  constructor's `values.push`). Call-site forms use `cdAddCall` etc., whose printed
  tokens are checked (`cdAddCall_toks`: `checked_add_t_uint256(a, b)`); body forms use
  the bodies `cdF72`, `cdF67`, `cdF8`, `cdF87`, `ccF25`, `ldF7`, whose names are
  checked by `cd_bodies_named` and which are the group's bodies at the helpers'
  positions (`cd_div_at`, `cd_exp_at`, `cd_decode_at`, `ld_decode_at`, `cd_push_at`,
  `cc_push_at`). Not every C08/C09 lemma is restated (e.g. only `decodeTuple` of the
  ABI group); any other one transfers the same way through `cd_*_eq`/`evalBlock_ren`. The C09 provenance caveat (groups mixing creation
  and runtime copies) no longer matters: each theorem is now about one object's own group.

### 2. Unique function tables (the option the T02 references need)
T02 and G01 refer to functions by name in an object's scope, so the stated
property is one definition per name per scope. `IrCensusUnique.lean`:
`TablesUnique o` (every function group at every depth of `o` has distinct names),
`census_tables_unique`, `linked_tables_unique` (kernel; `objectWf`, which both trees
pass, is stronger: it also forbids a nested group from reusing a visible function
name and fixes each call to the innermost binder of its name); `Mem.name_unique` (in such a
group the name fixes the signature and the position); `helpers_named_<obj>`: name
lookup with the parser's resolver `findFn` lands exactly on the positions the
transfer theorems use. Negative controls: `parse_rejects_duplicate` and
`parse_rejects_nested_duplicate` (a scope defining `f` twice, at top level or in a
nested block of a child object, is refused with "tree violates scoping or static
rules") and `duplicate_counterexample` (the two trees resolving `f()` to the first or
the second definition print exactly the text's tokens yet differ, and both fail
`TablesUnique` and `objectWf`: the tokens alone do not determine the tree). Not proved: printer injectivity under
`objectWf` (that every certified tree for a text equals the parser's), so "the unique
parse" of the Census text is not claimed; the parser's own result is pinned for
LinkedMath only (`linked_is_the_parse`).

### 3. `checked_exp` against `Evm/Exp.lean` and the EVM `EXP`
`IrExpEvm.lean` (imports `Evm/Exp.lean`, which is not edited):
`expUnsigned_evm`: the model returns `v` exactly when this compiler's checked `**`
code (`uTail .pow`, `exp_tail`) returns `v`, and fails exactly when it reverts;
`expUnsigned_opcode`: a model value is the value of the Yul `exp` builtin / EVM
`EXP` (`Pure.eval .exp`, `powWord`; solc's helper does not call it), and the model
fails exactly when `EXP` wraps;
`checked_exp_vs_evm`, `census_checked_exp_vs_evm`: on equal operands the imported IR
body (extracted, and the parsed Census body) returns the compiled code's value with no
machine effect, and runs `Panic(0x11)` first when the compiled code reverts;
`checked_exp_vs_evm_halts`: under `RevertHalts M` the helper then ends with exactly the
panic's fault. The two machines are different models and `uTail .pow` is this
compiler's code, not solc's: what is related is the outcome on equal operands;
revert payloads are not compared.
This removes C09's "no lemma relates this to `Evm/Exp`".

### 4. ABI and storage meaning: waits on X01/G01
Master has no frozen G01 relation (D3 layout, ABI argument ↔ calldata words, revert ↔
return data): `docs/feature-work/full-scope.md` still lists G01's contracts as
"proposed"; `docs/coverage-plan.md` says G01 counts as frozen only after revisions;
VX1's stub is on owner-review hold. What exists are partial, unfrozen pieces: the
source semantics' decoder (`Source/Eval.lean`: `wordAt`, `decodeArg`, `decodeArgs`),
layout slot terms (`Evm/Layout.lean` `Occ`, `Storage/HashedLayout.lean` `Loc.word`)
`Yul/Views/DynamicElements.lean`'s `uint256[]` element path, the calldata views
`Yul/Views/{AbiCalldataAgreement,AbiWordInput,AbiDecodeSequence,AbiUintArray*}.lean`,
and the first, unfrozen G01 statements in `Roadmap/Contracts.lean`. The handoff forbids
substituting partial relations for D1–D6, so the ABI and storage helpers keep their
exact machine-effect statements (C09) and their meaning waits on X01/G01, as do the
`fun_<name>_<id>` simulations.

### C10 reviews (read-only, no Lean server)
Finder: no high-severity defect (indices of `cd_bodies_named`, the `none` entries and
pair completeness checked against the generated signature lists). Findings: (1) "unmapped
= not defined" was not stated in Lean; (2) the Census tree's tie to the parser is the
generator's, and `check-ir.sh` did not compare the regenerated `census-tree.txt`;
(3) `TablesUnique` is weaker than `objectWf`; (4) the duplicate control did not pin the
rejection reason or cover a nested duplicate; (5) nothing tied `cdF72` etc. to the
group's positions; (6) "every group the object defines" overclaimed the pairs;
(7) stale names in docstrings (`eval_ren`, `sim_flat`, `eraseObject_inj`,
`IrCensus{Text,…}`); (8) the vs-EVM revert branch had no `RevertHalts` form.
Skeptic: no must-fix. Should-fix: "parsed" wording for Census (only LinkedMath's parse is
proved); (2) as the finder's (1); `cdEnv_installed` named `runCode` and had no `cc`/`ld`
versions; the negative control shows only that tokens without `objectWf` do not fix the
tree; "EVM `EXP`" is the Yul builtin's value and payloads are not compared; §4's
inventory missed the `Yul/Views/Abi*` modules and `Roadmap/Contracts.lean`; untyped
`have`s; the kernel cost of `census_certified` is not discussed.
Fixed: `<group>_unmapped_<obj>` (kernel); `check-ir.sh` runs `IrCensusGen.lean` first and
fails on a changed `census-tree.txt` (regenerated here through the Lean server: unchanged);
"certified Census tree" wording in the docstrings and this section; `ccEnv_installed`,
`ldEnv_installed`; `*_at` position lemmas; pairs stated exactly; `objectWf` vs
`TablesUnique` documented; pinned rejection reason and a nested/child-object duplicate
control; `checked_exp_vs_evm_halts`; docstring names; `exp` wording and payload caveat;
§4 inventory; typed `hs'`, `ih`, `ht`. Not changed: `have`s that instantiate a cited
lemma (`h`, `body`, `hw`, `h₁`, `h₂`) stay untyped, as in C09. Kernel cost (warning,
per AGENTS.md): `census_certified` takes about a minute and the generated Census
modules elaborate in about a minute more; they are leaf modules of this lane.

### C10 gates
- Per-file Lean diagnostics (MCP), 0 errors: IrRename, IrCensusCreation, IrCensusDeployed,
  IrLinkedCode, IrCensusTree, IrCensusMaps, IrCensusTransfer, IrCensusUnique, IrExpEvm,
  IrErase, IrCensusParse; test IrCensusGen (`CENSUS_TREE 172 lines`, file unchanged).
- `#print axioms`: `census_certified`, `sim_push_cd`, `census_tables_unique`,
  `duplicate_counterexample`, `parse_rejects_duplicate` [propext]; `evalBlock_ren`
  [propext, Quot.sound]; `helpers_named_cd` none; `census_checked_add_matches_source`,
  `census_checked_exp_overflow_halts`, `census_constructor_push_body`, `expUnsigned_evm`,
  `expUnsigned_opcode`, `census_checked_exp_vs_evm` [propext, Classical.choice, Quot.sound].
- `VT1_SKIP_LEAN=1 check-ir.sh`: CENSUS_MODULES_CHECK_PASS, VT1_IR_CHECKS_PASS.
  `check-layers.mjs`: "857 core modules, 0 reach the elaborator".
- `./run-lean.sh` at `52ed5830`: master's `docs/README.md` carries a row no fragment
  produces (master's, not this lane's), so `fragments.sh --check` fails before the build;
  for the gate only, the file was regenerated with `fragments.sh --force` and restored
  after the check stage (never committed). The cold build (no shipped artifacts) hit the
  2 h session limit at 5987/6257; three incremental reruns followed, in which other lanes'
  `Source/Horizon` and `Backend/Scalar/PowerBounds` were OOM-killed (exit 137) while the Lean
  server held ~4 GB, until both built. Final run: "Build completed successfully (6428 jobs)",
  then `check-solkey.sh` against the unpinned sibling `../solkey`: "167 mismatch(es)" (as in
  C09). Rerun with the pinned rules,
  `SOLKEY_RULES=tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key scripts/check-solkey.sh`:
  "OK — annotations match" (377 taclets, 131 read-bearing), exit 0.
- Fresh solc fixture rerun: still blocked (`binaries.soliditylang.org` unreachable; no
  unpinned compiler is run); the fixtures remain the pinned-binary outputs.
