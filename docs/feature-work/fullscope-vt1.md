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

Tests (`IrHelperChecks.lean`): 576 helper/source agreements on 12×12 edge
words for add, sub, mul and signed div (division by zero `Panic(0x12)`,
`min / -1` and every unsigned overflow `Panic(0x11)`, exact effect log);
`helpersText` equals the fixture and its blocks are verbatim substrings.

Open (kernel): `checked_sub_t_uint256` and `checked_div_t_int256`. Their proofs
elaborate, but the kernel reports deep recursion: the owner's `Pure.sub`
(`word (x + 2^256 - y)`) and `sdiv` (`signed`, `x - 2^256`) put a symbolic sum
with the literal `2^256` where a defeq check unfolds it in unary — the same
family as Gate G0's `ofInt?` pitfall, which `IrHelperSource.lean` avoids with
`rw`-stated lemmas. Fix: carry the `Pure` values folded through a `rw`-proved
characterization (as `pure_sub_of_le`), or ask VY1 for `rw`-friendly `Pure.eval`
lemmas. Also open: `checked_exp_*` (the loop; would generalize `Evm/Exp.lean`),
ABI and storage helpers, `fun_<name>_<id>` bodies and dispatcher/constructor
composition (need G01), and the remaining helpers of the census.
