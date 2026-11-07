# Shared executable AST translator

Status: preparatory raw-reader extraction, not completion of the first checkpoint
or the assignment. Base: `b419c3cf4f642ae519b66bebc26cdf2f7cf93574`.
Branch: `codex/solidity-directruntime-20261104/shared-translator`.
Repository: `/workspace/solidity-lean`.

## Concrete executable boundary

`Frontend/ExecutableAst/Shared/Boundary.lean` defines `Reader` with these exact
fields (namespace `Solidity.Frontend.ExecutableAst.Shared`):

```lean
structure Reader where
  typeName : Json → Except String (Ty × RawTy)
  expression : Json → Except String RawExpr
  statements : Json → Except String (List RawStmt)
  params : Json → Bool → String → Except String (List (String × Ty))
  specification : Json → Except String FunSpec
```

`Translate.lean` provides the actual default `reader`, plus concrete recursive
extension steps:

```lean
typeNameStep : (Json → Except String (Ty × RawTy)) → Json → Except String (Ty × RawTy)
expressionStep : (Json → Except String RawExpr) → Json → Except String RawExpr
statementsStep : (Json → Except String RawExpr) →
  (Json → Except String (List RawStmt)) →
  (Json → Except String (Ty × RawTy)) → Json → Except String (List RawStmt)
function : Reader → Json → String → Except String (String × FunDecl)
contract : Reader → Json → Except String Contract
```

B/C modules must capture their declaration-resolution tables in callbacks,
dispatch only their owned forms, and connect all recursive callbacks through
these steps. An isolated update of `reader.expression` does not reconnect the
already-bound default `reader.statements`. `ReaderControls.lean` pins this caveat,
connected nested extensions, both conditional bodies, left-child error priority,
type recursion and retained refusals. An `Except.error` is final: never catch it
to retry another executable translator. Only the existing Raw surface syntax is
returned, as input to existing intrinsic elaboration. No new verification IR,
axiom, admitted proof or placeholder implementation is introduced.

DirectRuntime now imports Shared.Translate and calls `contract reader` and
`function reader`; the old local reader was removed. Its proof-search/export code is unchanged. The assertion builder now lives in
Shared.Intrinsic with explicit producer callbacks and a new reference guard that
preserves the already-refused default AST fragment. The extracted helpers retain all 252 original string literals
in order. Default admission remains limited: uint256/int256/bool parameters,
primitive locals, arrays/mappings as storage roots, selected expression forms,
assignment/assert/require/push/pop, while/for and compact specification parsing.
References, tuples, richer contracts/calls and do-while remain refused by this
default. The existing name-only identifier reader and String diagnostics retain
known parity gaps. The metadata increment below rejects malformed booleans and unhandled operator
annotations after whole-root decoding. Existing unknown constant-kind failures
remain unchanged; these controls do not establish complete producer parity.

## Import closure and CR migration packet

The local source import closure of Shared.Translate has 17 modules and reaches
neither Frontend.Import nor Frontend.Testing. It uses the producer's existing
constant arithmetic/documentation helpers from SolcJson.Contract/Body. This is a
source import-cycle check, not a generated-C closure or no-kernel runtime proof.
Registration rows are proposed in the owned `registration-proposal.json`; shared
roots, maps and trust pins were not edited.

CR still owns the existing general printer/import route. CR must migrate its
producer-owned wrapper to this executable boundary while preserving every
previously supported form and diagnostic, and provide its exact reviewed commit.
No producer API was changed here. `lowerBodyLoops` currently lives in
Frontend.Import (lines 221 onward at the base); copying it into Shared would
create duplicate executable semantics. The shared intrinsic builder now reuses it through an explicit callback, alongside
the producer-owned Problem.callPre from Frontend.Problems. Producer adoption and
full source parity remain open; neither helper is copied. Importing Testing into Shared would
create a cycle and is prohibited. A new optional wrapper or this raw-reader
extraction alone does not satisfy the shared-translator requirement.

## Census and controls

Run `python3 tests/directruntime-20261104/shared-translator/inventory.py`.
The owned `coverage-inventory.json` compares all 58 emitted Solidity node kinds
against the pinned compiler ASTJsonExporter (commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`, Git blob
`b855c19efcb9061c7b19b696cf7045f25e78dc74`). It inventories 16 Yul kinds,
17 RawExpr and 42 RawStmt constructors and all 212 feature catalog entries.
Every row separates source admission, Raw/elaboration input, proof closure,
semantic catalog observations, backend gaps, ownership and candidate fixtures.
It explicitly marks full per-construct positive/negative controls as pending; H30 supplies the integration-owner map below. The compiler exporter is preserved with its
GPL header as source-provenance evidence. Catalog/schema inspection is not an
AST-to-solc semantic-equivalence theorem.

ReaderFixtures.sol/ast.json are freshly generated by the pinned solc 0.8.34
compiler (compiler SHA and source SHA are in the fixture header). FixtureControls
checks supported scalar/array/loop/spec bodies beside refused memory/tuple/
do-while siblings, two distinct overloaded declaration IDs, and retained
contract-member refusal in UnsupportedContract.sol. These are raw-admission
controls; sourceId selection/reporting, formula closure and producer parity still
need their own tests.

## Validation and reviews

All heavy checks use the owned bounded.sh wrapper: Docker memory.max=12884901888,
memory.swap.max=0, one CPU; LEAN_NUM_THREADS=1 and explicit Lean -j1. The outer
cgroup/host available-memory guard monitors H1's 4 GiB reserve. Writer locking
covers commands. Actual Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613 were read.
The alternate config has focused Shared defaults for MCP lean_build; tracked
run-lean.sh still requests its tracked full default targets. Native/WASM build
scripts use absolute prefix/bin/lake and need explicit bounded-config handling;
the PATH shim alone does not cover those future commands.

Evidence under `tests/directruntime-20261104/shared-translator/evidence/`:

- shared-mcp.log: focused 18-job build succeeded; both per-file diagnostics zero.
- reader-controls.log: callback/refusal controls passed (3 seconds).
- fixture-generation.log: both pinned compiler fixtures regenerated successfully.
- fixture-controls.log: all nine function rows plus unsupported contract sibling passed.
- api-signatures/1.log: exact Lean-checked callback/function/contract signatures.
- compiled-source-manifest.json: exact source/generated-C/olean hashes for Shared;
  not a runtime-closure or final exact-head gate.
- baseline-per-file/1.log: exact-base check failed due missing AnonLocalCapture.olean.
- baseline-build/1.log: fresh broad dependency build was deliberately interrupted
  before DirectRuntime; exit 137. It is pending, never counted as passing.
- reviews.md: independent read-only finder and skeptic, neither using Lean server.
  Confirmed resource/import/callback issues were fixed or explicitly retained as
  outstanding integration obligations. Counts were corrected by schema comparison.

Fresh KeySort passed after the first source commit: 377 taclets, 131 read-bearing,
table covers 131, exit 0. No RUNTIME_GATE_PASS: exact-base/head before/after timing/runtime,
compiled closure, native/WASM provenance and final full gates are still pending.
New module central registration is a proposal; no shared generated edits are
silently made to pass roots checks.

## Queue and handoff

1. Census: initial schema-complete index saved; per-form semantic/backend closure,
   all matching controls and per-form semantic/backend closure remain pending. H30 owner assignments are recorded.
2. First shared boundary: raw-reader callbacks and primitive intrinsic builder compiled/reviewed;
   full producer parity/adoption/migration and native/WASM closure remain pending.
3. Integration: no exact reviewed B memory/C control or CR migration commits have
   been received/consumed. A remains the only Shared/DirectRuntime writer.
4. Final ledger/proofs/performance/handoff: partial source packet only. Required
   full tests, proofs, reviews and serial runtime evidence remain open.

No push, merge, PR or publication. The persistent goal remains active for the
whole assignment; this preparatory packet is not final acceptance.

## Intrinsic executable API increment

Shared.Intrinsic imports Calculus.Spec; its static local closure has 104 modules
and reaches no other Frontend module. Its additional exact signatures are:

```lean
BodyLoopLowerer := List String → Nat → List RawStmt → ElabM (List RawStmt)
PlainEntryPre := (C : Contract) → (Γ : NCtx) → Fml C Γ.ctx
assertionObligation : BodyLoopLowerer → PlainEntryPre →
  (C : Contract) → String → Bool → Except String (Fml C [])
obligation : BodyLoopLowerer → PlainEntryPre →
  (C : Contract) → String → Bool → Bool → Except String (Fml C [])
```

ElabM here is Solidity's existing pure lowering computation, not Lean's environment
elaboration monad. DirectRuntime.buildObligation pins lowerBodyLoops and
`fun C Γ => Problem.callPre C Γ false [] false [] true`. No producer API changed.
The specified branch calls existing specObligation. The primitive assertion
algorithm, lowering order, source=true elaboration, entry/well-formedness premises,
scalar binders and modality are preserved.

Reference parameters remain refused. The new intrinsic guard prevents using
closeN's box reference binders for a source diamond. The producer's general wrapper
uses modality-specific binders plus refInputs; integration must preserve those
before admitting references. No arbitrary-callback source theorem is claimed.

intrinsic-mcp.log records a successful focused 114-job build and zero diagnostics.
IntrinsicControls checks the real existing lowerBodyLoops helper, both modalities,
entry-premise transport, callback failure, scalar binding, reference/return refusals
and specified/plain dispatch. These are development controls, not source or backend
correctness proofs. intrinsic-source-manifest.json binds source, generated C and
olean bytes. The broader closure warm-up was interrupted with exit 137 for this
increment and remains pending; it is not a passing before/after/runtime gate.

CR migration touchpoints remain Import.readImportedContract (base lines 565–589),
the printed-body/parser/macro-to-Raw block (793–822), loop/return lowering and source
scope checks (846–875), Problems.obligation (140–192) and the specified testing
wrappers. Changing only formula construction leaves a second AST translation path
and does not satisfy this assignment.

## H30 ownership and recovered API packet

The original executor was reattached with the branch, b2c27cb7 source commit and
uncommitted Intrinsic intact. A recovery diff/untracked archive was saved before
writes. A alone owns Shared, DirectRuntime and this lane's documentation/tests.
Shared generated roots, module maps, trust pins, Scoped and Source/ExtCall remain
untouched. B owns registered Memory modules, C ControlTuple modules and D the
registered native/browser scripts. Integration owners: CR Admission/P8 migration;
V11 MemoryOps; V09 Passes; VY5 H16 Source; V08 Lowering/V08; V16 Aggregates/Roadmap.
These ownership answers resolve DRA-OWNER-1; they grant no extra A write scope.

The API packet is API-HANDOFF.md in the owned test directory. Its exact committed
SHA/path receipt is saved in artifacts/API-RECEIPT.json after committing. Reader
signatures remain unchanged from b2c27cb7. Intrinsic is implemented and checked,
not a placeholder proof or declaration stub. First-checkpoint completion still
requires full producer parity/adoption and native/WASM closure evidence.

## Whole-root metadata refusal increment

The original decoder algorithms and recursive callbacks are unchanged. Metadata
validation runs after successful complete decoding, using existing J.nodes to
inspect folded descendants. Public function validates one complete function;
contract validates admitted storage members and skips sibling function bodies.
Legacy whole-root errors retain priority. Malformed booleans, malformed/nonpositive
operator identities and unhandled positive aliases cannot become admitted roots.

Raw Reader callbacks are elaboration-input decoders, not admission certificates.
Use public function/contract for their roots, or checkedExpression/checkedStatements
for standalone roots. Do not insert checked child wrappers into a root decoder if
you require its legacy later-sibling error priority. No Reader signature changed.
The default validator refuses all operator aliases; CR's full migration must wire
reviewed declaration-aware support before claiming prior producer alias parity.

38 ParityControls guards passed, including folded metadata, later-sibling errors,
whole-function priority, and malformed-function sibling isolation. Existing reader
and real-solc fixture controls passed. Per-file MCP diagnostics for Translate and
ParityControls were zero. The original per-node prototype was rejected in review
and is not the committed implementation. The audit reconstructs the published
fcdddfcc decoder prefix exactly and separately identifies added admission checks.

MetadataBench used 73 expression nodes from the source-SHA-pinned ReaderFixtures,
three serial raw/checked pairs of 20000 calls each, varying input index each call.
Raw samples:2.418s,2.269s,0.889s. Checked samples:2.695s,2.424s,2.310s.
Every call succeeded. These are variable Lean development-evaluator measurements,
not standalone runtime timings, a stable overhead factor or RUNTIME_GATE_PASS.
The benchmark and source/C/olean hashes are saved in evidence/metadata-* files.
Full native/WASM closure and before/after verification evidence remain pending.

## Coverage and refusal checkpoint handoff

The census now records source-hash anchors, fixture/compiler identities, JSON
pointers, source ranges/lines and enclosing declarations for all 57 modern
Solidity kinds. Throw is legacy-only and the pinned 0.8.34 compiler rejects it
at its original source span. The 77 existing fixtures contain 70 with matching
source hashes; eight selected fixtures witness the modern kinds. These existing
AST files may include intentional mutations: matching source/header hashes are
not authenticated compiler regeneration. 806 observed subtype combinations are
indexed separately. The owned freshly compiled Yul fixture contains all 16 Yul
kinds; direct JSON controls check decoding and grammar shape only.

raw-elaboration-ledger.json indexes all 17 RawExpr and 42 RawStmt constructors
against existing source arms and records exact declaration starts for typed
calculus/operation theorems. It does not certify Raw lowering preservation,
source equivalence, or the axioms of those declarations.

Public roots now check their expected nodeType after successful legacy decode.
Whole-root metadata checks require compiler expression types, Boolean unary
prefix flags and binary common types, including folded descendants. Existing
decode errors retain priority. DirectRuntime rejects malformed present selector
and listing fields; function declarations globally require positive, unique
integer IDs before selection. This validates headers without reading unselected
function bodies. Conjunctive name/ID selection remains unchanged. Signed int
complement remains unsupported at intrinsic elaboration; its raw success is
explicitly not counted as semantic support. No Reader signature changed.

Validation: the dc271809 touched gate passed 340 jobs in 4289.227s, child maximum
RSS 3211968 KiB, cgroup peak 4651905024 bytes, minimum outer headroom 7339847680
bytes. The subsequent changed-source/Yul rebuild passed 357 jobs; after the final
header/ID corrections, DirectRuntime rebuilt successfully again. All eight
per-file MCP diagnostics and nine repository per-file regression gates passed.
The scope remained 12 GiB, swap disabled, one CPU/Lean thread, with monitored
4 GiB outer headroom. Lean 4.24.0 and Lake 5.0.0-src+797c613 remain the actual
toolchain. Earlier KeySort passed 377 taclets, 131 read-bearing/table-covered.
These are touched/per-file gates, not the assignment's final full gate.

Evidence and initial corrected failures are saved under
tests/directruntime-20261104/shared-translator/evidence/refusal-checkpoint/.
Independent finder/skeptic findings and fixes are recorded in evidence/reviews.md.
Published origin/master89373e34 contains only the earlier Shared Boundary and
Translate snapshot from fcdddfcc, not this lane's Intrinsic/wiring/refusal changes.
The immutable starter API receipt is retained in artifacts/API-RECEIPT.json.

Queue accounting: complete per-form admission/proof/semantic/backend controls
remain partial; FIRST adoption/parity remains partial; exact reviewed B/C/CR
integration remains pending; native C/WASM closure, exact-base/head runtime,
exact theorem/axiom comparisons and final full gates remain pending. The existing
general SolcJson translation has not migrated, so no single-boundary completion
or RUNTIME_GATE_PASS is claimed. Registration remains a central proposal; H30
excludes generated roots/maps/trust pins from this lane. No push/PR/publication.

## H35 VM validation and cache delivery blocker

H35 requires owned-module build, axiom inventory and controls on this VM, then
cache shipment before reporting a checkpoint done. The four owned modules built
successfully at implementation713a0612 (340jobs); the new AxiomInventory file had
zero per-file MCP errors. Eleven repository per-file gates passed, including all
nine existing controls and current/exact-base axiom inspections. Lean4.24.0 and
Lake5.0.0-src+797c613 were measured again. All heavy work used the existing
12GiB/no-swap/1CPU/Lean-j1 scope with monitored4GiB outer reserve. An initial
Lake-version invocation through the build shim failed before any build; the
corrected pinned version command/build passed and both logs are retained.

No named theorem was added or changed by the owned implementation. The inventory
covers all32 explicitly declared public Shared structures/abbrevs/definitions and
both runtime entrypoints. Current and pinned-base check/checkString each report
exactly propext,Classical.choice,Quot.sound; no additional observed axiom name or
sorryAx. The base validation source prefix is byte-identical to git-show b419,
with only four inspection commands appended. Partial definitions are opaque to
logical axiom traversal: this does not establish executable closure or source
equivalence. Machine comparison and raw inspection output are in evidence/h35.

The requested ship-cache.sh invocation used its documented SHIP_ALLOW_HEAD=1
option and actual LAKE_CACHE_DIR. It prepared1737artifacts/583mappings, then exited1
because coordinator poll-state.json was absent. vmexec.py is also unavailable
on this worker. No remote transfer occurred and no successful script delivery
receipt exists. A separately labelled local-verification receipt checks every
archive artifact's size/SHA256 and exact member set; it is not shipment success.
The pack is600359272bytes, SHA256
cac02c95edef9190666bd7e11333438c348039e09251ed9415645fc14ddeb6f2.
Its absolute path and manifests are in evidence/h35/cache-receipt.json.

H35-CACHE asks whether the coordinator retrieves/relays this verified pack or
provides a worker-side invocation/routing configuration. The self-contained
question/options are saved in evidence/h35/scope-question.json. H35 checkpoint
acceptance remains blocked until real delivery evidence; previously implemented
checkpoints are not represented as H35-complete. Full assignment B/C/CR integration,
complete construct/source/proof parity and native/WASM/final full gates remain open.
No production file changed after implementation713a0612; this increment adds
validation tooling/evidence only. No goal creation/reset, push, merge or publication.

The final cache verifier also checks all583 mapping schemas/output-prefix
references, duplicate-key consistency and the4owned mappings against actual
build-trace outputs; receipt versions/exit/failure are derived from gate logs.
This strengthened check passed in24.991s with19812KiB child maximum RSS. Source
trace freshness relies on the preceding build gates. Independent finder/skeptic
final reviews found no further defect; no delivery/installability claim follows.

## H41 custody and 57-kind source-reader backfill

H41 amends H35: retain verified packs on this VM with their path/SHA; the
coordinator pulls them; never run ship-cache.sh on this VM; future delivery is
coordinator-pending. The coordinator reports receipt at
/home/guilherme/.local/state/cloudvm-coord/receipts/shared-translator-cache-received-20261105T025521Z.json
and verification of SHA cac02c95edef9190666bd7e11333438c348039e09251ed9415645fc14ddeb6f2.
The600359272-byte pack remains in its original artifacts/h35/cache-ship path;
its SHA was rechecked locally. The host receipt itself was not read here.
Installation/runtime closure does not follow. H35-CACHE is resolved, not a
remaining permission request; historical failed-shipment logs remain unchanged.

This backfill freezes observations for57modern Solidity kinds in each of two
suites.37kinds have standalone Shared reader entrypoints and20have none. The
existing-fixture suite records11decoded/26refused; fresh exact-pinned compiler
ASTs record14decoded/23refused; both have20no-entry outcomes and37unknown-root
refusals. Each records14producer expression-printing attempts (existing11printed/
3refused; fresh9printed/5refused). Different selected source nodes explain suite
differences; these counts are neither same-input regression nor performance data.

Eight selected sources were actually recompiled on this VM with exact0.8.34/
0.8.38 compiler binaries, through the existing compiler helper. Full raw ASTs are
saved unchanged under tests/directruntime-20261104/shared-translator/fresh/.
Receipts record compiler/source/output hashes; all57modern kinds are present,
with no unexpected non-Yul kind. Source ranges, declaration IDs and JSON pointers
are stored in cases; independent preflight checks114witness identities,8fresh
output hashes and2compiler pins. Legacy Throw remains separately compiler-refused.

All4owned modules built (340jobs); frozen noncapture per-file MCP had0errors;
all12repository per-file gates passed, including exact-base/current axiom checks.
The340-job build/MCP/preflight run took14.554s, cgrouppeak714182656bytes, minimum
outer reserve7425843200bytes. Twelve per-file gates took50.277s, child maximum
RSS1263572KiB. Actual Lean4.24.0/Lake5.0.0-src+797c613 and12GiB/no-swap/-j1 bounds
remain recorded. Source-reader matrices/receipts are linked from the inventory.
No implementation theorem or production source changed in this increment. Four
owned source/trace mappings match the coordinator-received cache packet; no new
owned-module cache outputs were produced. Future packs remain coordinator-pending.

Both independent reviews are recorded in evidence/reviews.md. These observations
exercise whole witness subtrees; child refusals may dominate. Decoding and
printing do not establish identity resolution, intrinsic closure, source
equivalence, or backend support. Full producer adoption/proofs/native-WASM gates
remain open. The next step is user-authorized adoption of published8495f1de and
its exact reviewed Memory/ControlTuple packets, preserving this committed work.


## Reviewed packet composition and lexical preparation

Adopted published8495f1de in merge d6894545, preserving owned metadata controls.
Compose wires the published Memory.Reader and ControlTuple.Adapter through one
recursive executableReader; DirectRuntime uses it for contract/function reads.
There is no failure-catching fallback. Reference parameters/returns and unsupported
siblings retain their existing guards. At this checkpoint Scope/Compose registration was proposed
locally, without modifying shared roots; published9584 later registers Scope.

Plain obligation preparation now reuses the existing renameStmts before the loop
callback. The callback therefore receives freshly renamed syntax. Scope guards
check original same-scope duplicates; nested shadowing remains valid. Fresh names
reserve root, parameter, local and invariant binders. Three checked theorems prove
index bounds only, not semantic preservation of renaming. This supersedes earlier
claims that the assertion builder changed only by callback extraction.

The exact344-job build, two MCP checks and14per-file gates passed in57.357s,
maximum child RSS1245272KiB, scope peak1091465216bytes and minimum outer available
5293535232bytes. Logs: artifacts/composed-gates.log and composed-gates/*.log.
The new/changed axiom inventory contains only existing propext/Classical.choice/
Quot.sound dependencies, without admissions. Finite intrinsic execution controls
exercise four normal, two panic and two revert results; these samples and ready
listings do not establish source correctness or universal proof closure.

The composed fixture retains existing builtin-ID normalization/loop annotations
and restores required typeIdentifier/tryCall from matching raw compiler nodes.
This is a test-only adapter, not authorization to alter producer interfaces.
DR-A-META remains open: producer owners must select metadata retention or an
explicit checked compatibility adapter. CR's existing Lean import migration,
native/WASM closure, full parity/proof inventory and final gates remain pending.
The prior received cache predates Scope/Compose and must not be claimed fresh.


Published f77cf60d was adopted in15a78eb6 after byte-comparing its Intrinsic to
c3bc7282; the newer scoped builder was retained. Post-adoption344-job build,
axiom inventory and two focused controls passed in178.973s, childRSS1254608KiB,
minimum outer reserve5934964736bytes. Actual Lean4.24.0/Lake5.0.0-src+797c613
versions are in evidence/adoption-f77/gates.log. Source ownership audit passes
against the explicitly authorized adopted master; original decoder/proof-search
comparisons remain pinned to original source. No unowned producer path was edited.

H41 local delta contains six owned modules/18artifacts/6mappings, verified against
trace outputs, cache mappings and archive bytes. Path:
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/cache-f77/15a78eb6ba12/owned-delta.tar.zst
SHA256047cfd99894d0943e9cdd728122ac48db0b2103652a97444944efbcc2325f167,
965584bytes. It is coordinator-pending, requires matching dependency caches and
is not standalone installation or native closure evidence. ship-cache.sh was not
run. The earlier received600MB pack remains preserved separately.


Fresh bounded per-file Solidity/KeySort.lean gate passed. Refreshed solkeycheck
built12jobs and reported: parsed377taclets,131read-bearing,table covers131;
OK annotations match the pinned local solidityProgramRules.key. The check took
6.633s within the scope (startup-inclusive49.215s),RSS252428KiB; minimum outer
available6264778752bytes. Evidence/adoption-f77/keysort.log preserves commands and
outputs. RUNTIME_GATE_PASS remains pending: actual versions/KeySort are necessary,
but producer migration, full/native/WASM gates and source parity are not complete.
Fresh six-module source/C/olean/trace fingerprints are saved beside these logs.


## Published9584 adoption and canonical coverage backfill

Explicitly authorized master9584f9e7 was fetched,remote-ancestry verified and merged
without conflicts in44da2669. All owned production bytes are unchanged from
abe3fb8c. Master delivers identical Scope plus C's separate intrinsic model controls;
it does not deliver CR's existing-import migration. Scope is centrally registered
on master; Compose remains a local proposal. No shared root/map edit was made.

Local bounded build344jobs,MCP0 and all8focused per-file gates passed,including
new C controls; wall87.938s,RSS1244524KiB,scopepeak1498406912bytes,minimum outer
available4865368064bytes. Actual Lean4.24.0/Lake5.0.0-src+797c613 are recorded.

The single observation driver now uses default and composed Reader configurations.
Default matrices are frozen even in capture mode. Independent source preflight,
frozen MCP and per-file checks passed in25.562s,RSS579044KiB,minimum available
5455556608bytes. Each reader exercises57modern kinds in each suite,with37unknown
root refusals and20no-standalone inputs. Existing suite counts stay11decoded/
26refused; four refusal reasons change as composed decoding reaches deeper shapes.
Fresh counts change14decoded/23refused to16decoded/21refused,only selected do-while
and tuple witnesses. Reader-comparison.json preserves every exact difference and
source identity; inventory links all four matrices. These are decoding observations,
not exhaustive subtype support,identity adequacy,source semantics or backend proofs.

Migration-packet.json pins current source/API hashes and CR/D obligations. Both
independent read-only finder/skeptic reviews found no driver/comparison/ledger defect;
neither used Lean/server. CR migration,DR-A-META,full per-form parity,compiled
native/WASM closure,before/after runtime and final gates remain pending. No goal
completion or RUNTIME_GATE_PASS is claimed.


Fresh post9584 KeySort per-file gate and refreshed SolKey checker passed:
377taclets,131read-bearing,table131,annotations OK. KeySort/cache command exit0,
wall6.013s,RSS252608KiB,minimum outer available6093467648bytes. The six-module
cache delta was regenerated and fully verified against current successful build
traces and mappings; bytes are identical to the earlier local delta:
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/cache-packs/1a3bce261301/owned-delta.tar.zst
SHA256047cfd99894d0943e9cdd728122ac48db0b2103652a97444944efbcc2325f167,
965584bytes,18artifacts/6mappings. Delivery remains coordinator-pending; dependency
caches/toolchain must match. H41 was obeyed: no ship-cache.sh invocation. Fresh
source/C/olean/trace fingerprints and cache/gate receipts are in adoption-9584.


## Publishedb86 adoption and direct-result coverage

Fetched remote-verified b86ae456 and merged in34afa7f0. One Compose add/add conflict
was resolved to the published reviewed docstring correction; executable code is
unchanged. All five Shared modules are now centrally registered on master. Later
owned Translate/Intrinsic/DirectRuntime changes remain preserved. CR migration was
not delivered; no producer paths were directly edited. Adoption.json records exact
source hashes and receipt attribution.

Local bounded344-job build,Compose MCP0,axiom inventory and four focused controls
passed in43.917s,RSS1242408KiB,minimum outer available5394448384bytes. Compiler
witness preflight still checks114identities,8fresh outputs and2binary pins.

New DirectResultControls invokes the actual public checker without listing for
12existing source-identified fixtures,checking function/sourceId,provenance and
diamond tags. Four positive samples return proved;four failing diamond samples
return pending;four unsupported shapes remain unsupported. Frozen MCP0 and per-file
gate passed in48.385s,RSS1249260KiB,minimum available5325553664bytes. These are
trusted executable-model outcomes,not exported Lean proof terms or source/native
correctness proofs. Pending is not refutation. This complements,not replaces,the
finite intrinsic execution and ready-listing controls. No checker implementation,
proof budget,trust policy,premise or theorem was changed to obtain these results.

Coordinator reports byte delivery of the prior965584-byte cache delta with SHA
047cfd99894d0943e9cdd728122ac48db0b2103652a97444944efbcc2325f167 and host receipt
/home/guilherme/.local/state/cloudvm-coord/receipts/sched-20261105T1200Z/shared-cache-received.json.
Host receipt is unread locally; installation/entrypoint migration/parity/native
closure do not follow. H41 remains in force for refreshed packs. CR migration,
DR-A-META,exhaustive form parity,source preservation,native/WASM closure,before/after
runtime and full final gates remain open. Original queue checkpoints stay partial;
no RUNTIME_GATE_PASS or goal completion is asserted.


Fresh KeySort and SolKey377/131/131 annotations checks passed under actual cgroup
memory.max12884901888,swap.max0,cpu.max=100000 100000. Actual toolchain remains
Lean4.24.0/Lake5.0.0-src+797c613. KeySort/cache run6.353s,RSS251580KiB,minimum outer
available6049267712bytes. New refreshed pack differs from the received prior pack:
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/cache-packs/14d0d88411fa/owned-delta.tar.zst
SHA256eb91e1e42a61cbd72744bb8290fea7cdb10c139cbfeaa47a08a52a2e52646519,
964484bytes,18artifacts/6mappings,fully verified locally. It remains coordinator-
pending and requires matching dependencies/toolchain. The earlier047cfd99 pack
is byte-delivered per coordinator receipt; that receipt does not cover this new
pack. H41 obeyed; no ship-cache.sh invocation. Evidence and fresh source bindings
are in adoption-b86. RUNTIME_GATE_PASS remains pending.


## Published8bf and paired box/diamond backfill

Remote-verified8bf83218 adopted cleanly inb4990c26;owned production files remain
byte-identical to459c19a8. New SolcJson.IrImport selects an IR JSON channel,not the
existing AST import migration. All five Shared modules remain centrally registered.
Local344-job build,axiom inventory and Composed/DirectResult controls passed in
31.133s,RSS1250004KiB,minimum outer available6072496128bytes. Actual toolchain
remains Lean4.24.0/Lake5.0.0-src+797c613;no source proof/budget/trust policy changed.

New ModalityControls source explicitly marks box functions and leaves diamonds
unmarked. Three function-body byte pairs are identical. Canonical reader/obligation
and public checker verify source identity,provenance and modal tags;separate finite
initial-state runs check normal/revert/panic halts. Results:normal proved both;
revert proved box/refuted diamond;panic refuted both. Three proved/three refuted
are trusted executable-model outcomes,not exported Lean proof terms or source/
native correctness. Counterexample objects are present for refuted results but are
not independently replayed/validated by preflight. Older four complex failing
diamond fixtures remain pending;the new simple cases do not discharge those gaps.

Exact0.8.34binary/source/raw AST/normalized AST identities and6source IDs are saved;
raw AST is unchanged compiler output. Fixture generator reuses the existing helper,
with no metadata-restoration adapter/new translation. Frozen MCP0/per-file/preflight
passed in42.053s,RSS1249292KiB,minimum available5282668544bytes. Raw-provenance
regeneration preserved the gated normalized fixture byte-for-byte and passed in
2.150s,RSS169496KiB. Inventory/migration packet link the complete6-case ledger.
Both independent read-only finder/skeptic reviews found no confirmed defect and
used no Lean/server. No full original queue item or RUNTIME_GATE_PASS is claimed.
CR migration,DR-A-META,complete form/source parity,native/WASM closure,before/after
runtime and final full gates remain open. H41 remains in force.


Fresh8bf KeySort and SolKey377/131/131 annotations checks passed;actual cgroup
memory.max12884901888,swap.max0,cpu.max=100000 100000. KeySort/cache8.535s,
RSS252580KiB,minimum outer available6055948288bytes. Six-module cache regenerated
and verified against fresh successful build traces/mappings;18artifacts/6mappings,
964484bytes,SHA256eb91e1e42a61cbd72744bb8290fea7cdb10c139cbfeaa47a08a52a2e52646519,
byte-identical to the prior pendingeb91pack. Current path:
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/cache-packs/defe3f023c1b/owned-delta.tar.zst
Delivery remains coordinator-pending;dependency caches/toolchain must match. Old
047pack byte delivery remains separately user-reported. No ship-cache.sh invoked;
source/compiled provenance and gate/cache receipts are in adoption-8bf. No final
RUNTIME_GATE_PASS or full original queue completion follows.


## Published3ad and native executable checkpoint

Verified master3ad22f66 adopted cleanly in8de74453. Owned production bytes are
unchanged;no new frontend/runtime producer API or CR AST migration was delivered.
Local344-job build,axiom inventory,modal and prior direct-result controls passed
before native compilation. No Lean implementation,theorem,budget or trust change.

Ran existing scripts/build-direct-native.py unchanged with exact clean Lean source
797c613 and toolchain4.24. The owned prefix only redirects Lake to existing bounded
policy;all other files symlink actual toolchain. Native code compiles serially at
producer default-O2. First attempt outer guard stopped at307.511s,minimum available
4290482176bytes,outer137/guard125;this is a resource failure,not a passing gate.
Read-only POSIX_FADV_DONTNEED hints on OWNED regular artifact/source files reclaimed
clean pages without data mutation,symlink traversal,global cache drop or limit/
reserve changes. Retry compiled all206retained modules but failed at bridge cc
lookup;486.234s,RSS1229488KiB,min4789747712bytes. Existing supported CC override
selected/usr/bin/x86_64-linux-gnu-gcc-14(Debian14.2.0-19);cached retry linked in
50.519s,RSS1229536KiB,min5243146240bytes. Both failures and completed objects remain
preserved. Exact source checkout stayed clean;producer scripts/source unchanged.

Native binary20962960bytes,SHA2561d327a56e1501d4bf02fe66bd04c4a4c1d85d328d7a550846a20ab76f05caa5d.
18exact saved model outcomes and2malformed/unknown-root fail-closed controls passed.
Runtime executes in empty cwd with Lean search vars removed;file/process/network
trace observes no serialized Lean environment access,external frontend executable
or network;dynamic dependencies are system-only. Native execution with strace took
0.097s(contains instrumentation overhead;not a before/after benchmark);complete
control/audit command0.632s,RSS21308KiB,min6463283200bytes. Exact inputs/source IDs,
source/C/binary/trace hashes and stdout are saved. Native references the canonical
Shared executable reader;no general producer expr/body translator root was found
by the named-symbol inspection. This remains a bounded external regression check.

Fourteen frontend-origin symbols survive link GC. Independent read-only finder/
skeptic reviewed all exact linked disassemblies/pinned helper bodies:6initializers
only allocate IO-unit success with heartbeat/OOM handling;8helpers implement List
String equality,List Nat membership,Option String/Nat equality,UTF8 membership,
JSON field/string access,JSON array construction and identity traversal. No actual
frontend functionality among THESE candidates;origin names do not justify either
a violation or a blanket closure claim. The review does NOT prove exhaustive
forbidden-functionality absence over all9953retained functions/206modules. No
exclusion/trust relaxation was requested or assumed. Broader native closure,WASM,
source preservation,CR migration,DR-A-META,complete form parity,before/after runtime
and final gates remain pending. No RUNTIME_GATE_PASS or original queue completion.


During checkpoint preparation coordinator explicitly required rebase onto published
e6849d3b before the next commit. Preserved original committed history at
refs/codex-recovery/shared-translator/pre-e684-8de74453b38b and WIP tracked.patch/
untracked.tar under artifacts/rebase-e684. Replayed17owned commits;only Compose
comment conflicted,resolved to exact reviewed prior source;autostash restored WIP.
Three merge-only historical evidence files were restored byte-exact from the old
Git blobs. Production source,desired dirty patch and all46untracked files were
verified preserved before metadata updates;no code/premise weakening or data loss.

Initial post-rebase bundle passed build/threeLean gates/native controls but failed
the static ownership audit because its old3ad baseline had not been updated after
preservation check exposed those historical evidence omissions. Log retained as
setup failure. Corrected authorized baseline to e684 and restored exact old evidence;
final bounded344-job build,axiom inventory,modal/direct controls,native18+2 and
ownership audit all pass:22.089s,RSS1251604KiB,min6271008768bytes. Current native
source/C/binary bindings still match after the rebase;no recompilation assumption.
Last instrumented native18+2 execution0.129s,not a before/after benchmark. Broader
closure,WASM,CR migration,DR-A-META and original final gates remain pending.


Verified native replay packet:38payload members(binary,build/source manifest,
licenses,replay requests/oracles,trace,linked symbols and14review bodies/disasm).
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/native-packet/native-parity.tar.zst
7901648bytes,SHA256dc2e7041beab617cb5f57ef4d5c3e299cbaa92e7691f5a67869faa03c17ced60.
Every member size/hash/name was checked against embedded CONTENTS.json;no serialized
Lean environments included. Packet delivery is coordinator-pending,not publication.
Final read-only finder/skeptic independently confirmed e684 ancestry and exact
restored historical blobs,successful final gates and honest packet limits. Source/
exhaustive closure/WASM/migration obligations remain pending. An initial attempt to
pipe a packager via noninteractive Docker stdin did no packaging;it is not counted
as validation. The file-backed packager above performed the actual verified work.


After required rebase/native checkpoint commit,fresh KeySort and SolKey377/131/131
annotations checks passed. Actual Lean4.24.0/Lake5.0.0-src+797c613,scope memory.max
12884901888/swap.max0/cpu.max=100000 100000 remain verified. KeySort/cache4.669s,
RSS252528KiB,min6243352576bytes. Fresh6module18artifact/6mapping cache verified:
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/cache-packs/28b285ccf48a/owned-delta.tar.zst
964484bytes,SHA256eb91e1e42a61cbd72744bb8290fea7cdb10c139cbfeaa47a08a52a2e52646519.
Byte-identical to prior pendingeb91pack;delivery still coordinator-pending. No
ship-cache.sh invocation. Fresh source/compiled fingerprint receipt and gate/cache
logs are in adoption-3ad. RUNTIME_GATE_PASS and whole-lane completion remain pending.


## Published708 adoption

Coordinator published the complete prior owned head1d8e6c30 as an ancestor of
70845978. Required rebase completed cleanly to708;all owned files are byte-identical
across those heads and original history is preserved. Recovery ref:
refs/codex-recovery/shared-translator/pre-70845978. This is adoption of integrated
work,not completion or delivery of the pending CR AST importer migration.

Fresh bounded344-job owned build,axiom inventory,modal/direct controls,native18+2
and ownership audit passed32.846s,RSS1250056KiB,min5558743040bytes. Exact source/C/
binary manifest bindings still match the original native binary1d327a56;no changed
source modules were found in its manifest. Latest instrumented native replay0.205s,
not a before/after benchmark. Lean4.24.0/Lake5.0.0-src+797c613 remain actual versions.
Read-only finder/skeptic,no Lean/server,confirmed ancestry,owned preservation,gate
exit0 and appropriate limits. Native replay archive remains dc2e7041 and current
Lean cache eb91e1e4,local/coordinator-pending absent further byte-delivery receipt.
CR migration/DR-A-META,exhaustive binary/source/form parity,WASM,before-after runtime
and full final gates remain open. Existing goal is not reset or completed.


Fresh708 KeySort and SolKey377/131/131 checks passed with actual scope memory.max
12884901888,swap.max0,cpu.max100000 100000. KeySort/cache25.906s,RSS251196KiB,
minimum outer available5536673792bytes. Current verified6module18artifact/6mapping
cache964484bytes,SHA256eb91e1e42a61cbd72744bb8290fea7cdb10c139cbfeaa47a08a52a2e52646519:
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/cache-packs/8f03f21288f3/owned-delta.tar.zst
Local/coordinator-pending,not shipment/installation. H41 no ship-cache.sh invocation.
Current source/compiled fingerprints and cache/gate receipt are under adoption-708.
No get_goal capability is exposed;the existing goal is not reset or completed.


## Published1ae rebase and durable ownership audit

Coordinator integrated19f8973d through source-equivalent cherry-picks1dcfab2e/
79dca631,not original commit ancestry. All owned files matched the published tree.
Required rebase onto1aeaf276 completed cleanly,skipping already-applied8f03f212/
19f8973d;old identities remain in recovery ref
refs/codex-recovery/shared-translator/pre-1aeaf276. No runtime source changed.

The optional static ownership audit now uses the unique merge base of HEAD and
fetched refs/remotes/origin/master,requiring pinnedb419 ancestry. This prevents a
new hard-coded SHA edit for each publication and continues checking unpublished
tracked/untracked tree deviations. Ambiguous ancestry fails closed. Caller MUST
still establish authorized fetch/rebase;the audit grants no authorization and is
not an audit of every historical edit. Original decoder/proof-search/builder/
wrapper comparisons remain pinned to their original bases and are unchanged.
No runtime API,semantic exclusion,premise,proof budget or trust boundary changed.

Fresh344-job owned build,axiom inventory,modal/direct controls,native18+2 and new
ownership audit passed38.161s,RSS1250152KiB,min5537415168bytes. Native binary source/
C bindings remain exact;no Source AST importer migration was delivered. Independent
read-only finder/skeptic(no Lean/server/writes) found no scope-guard defect and
confirmed source-equivalence versus ancestry distinction. Remaining CR/DR-A-META,
complete form/source parity,exhaustive binary closure,WASM,before-after and final
full gates remain open. No RUNTIME_GATE_PASS or whole-goal completion is claimed.


Post-commit audit with local HEAD1b55edee ahead of publication still selected1ae,
so unpublished local work was not hidden. Output/source proof checks passed.
Fresh KeySort/SolKey377/131/131 and6module18artifact cache verification passed:
17.005s,RSS251532KiB,min5508968448bytes;actual scope12GiB/swap0/CPU1. Lean4.24.0/
Lake5.0.0-src+797c613 remain actual. Current964484-byte cache SHA256
 eb91e1e42a61cbd72744bb8290fea7cdb10c139cbfeaa47a08a52a2e52646519 is locally verified:
/workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/cache-packs/1b55edee9249/owned-delta.tar.zst
H41 delivery remains coordinator-pending;no ship-cache.sh invoked. Native archive
dc2e7041 remains immutable. Full goal/CR metadata decision/WASM/closure are unchanged.


## H68: fixed audit publication and metadata policy

H68 supersedes the moving-reference ownership audit described above: ownership-baseline.json records publication 4095d848297d87e374b4f069692511cfe4a36cf7. The audit verifies both ancestry edges and never reads origin/master to select its baseline. Original b419/fcdd decoder, builder, proof-search and wrapper comparisons remain unchanged.

Human H68 selected DR-A-META option 1: retain required typeIdentifier/tryCall metadata in producer output and migrate compatibility fixtures, preserving existing normalization and loop annotations. migration-packet.json and API-HANDOFF.md relay the concrete decision to CR/D; producer changes and exact reviewed migration commits remain owner dependencies. Prior pending-choice statements are superseded.

H68 audit checkpoint gates passed on this VM: owned serial build344 jobs; axiom inventory; modality/direct-result controls; KeySort; SolKey377/131/131; fixed audit and isolated Git regression. Combined37.386s,RSS1250672KiB; memory.max12884901888/swap.max0, outer minimum15216594944bytes. Exact commands/output and independent read-only finder/skeptic(no findings, no Lean/server) are in evidence/h68. No Lean declarations changed. Cache bytes remain source-identical; current-head packaging follows the commit under H41. Full runtime gate remains pending.


## H68 compatibility fixture checkpoint

Five fresh pinned0.8.34 compiler executions migrated all five owned .ast.json source fixtures to required metadata retention.424 typeIdentifier values and27 tryCall flags are bound to raw compiler nodes by kind/source span and retained declaration IDs. ComposedReaders was already retained and remains byte-identical; four other fixtures change. All other normalized JSON values match recorded4095, including builtin IDs and loop annotations. Fresh raw compiler output and exact source/compiler/fixture hashes are saved under evidence/h68. No producer-owned code changed.

The shared retention helper only copies authenticated compiler metadata onto existing normalization output; it performs no executable AST translation. Helper and independent preflight fail closed on missing/conflicting identity, type information or required metadata. Dedicated composed/modality/Yul generators retain the policy. Finder identified a stale dedicated modality receipt consumer; both generation routes now emit the dedicated receipt and its preflight consumes it. Skeptic requested missing-typeDescriptions coverage, now enforced in both paths. Both independent read-only re-reviews pass, no Lean/server/writes.

Owned build344 jobs,axiom inventory and eight affected per-file controls passed. Controls preserve exact admission/refusal diagnostics, declaration/overload selection, unsupported siblings,Yul refusal,eight finite intrinsic samples,public direct/modality outcomes.114 existing source witness identities and two compiler pins still pass. Native18exact comparisons+2failclosed passed against binary1d327a56; instrumented runtime0.126s is not a before/after benchmark. Combined33.774s,RSS1256288KiB;scope12GiB/swap0/CPU1;outer reserve minimum15028285440bytes. Review repair aggregate+dedicated regeneration/preflight passed3.457s,RSS172672KiB. No Lean declaration,axiom,premise,refusal or budget changed.

This completes the H68-owned fixture backfill, not the full lane. CR still owns actual existing importer migration and must deliver its exact reviewed commit; DR-D owns WASM delivery. No emcc/wasm-opt was on the current VM PATH. Existing import still uses printer/parser/macro construction. Exhaustive per-form/source preservation,full binary closure,WASM,before/after benchmark and final full gates remain open;RUNTIME_GATE_PASS pending.


## H44 source-only split and retained data

H44 supersedes the H68 data locations above. Held a073878cf3dd1bd8fb82cfc067ca4cedcb711bb1 is preserved by refs/codex-recovery/shared-translator/pre-h44-a073878c. Generated fixtures,raw compiler ASTs,logs,receipts,variant cases/matrices and current ledgers live only under ignored /workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/h68-bulk. Tracked fixture/ledger/inventory files are restored exactly to4095. Historical coverage-inventory.json/inventory.py and earlier evidence references retain baseline provenance; they do not claim migrated hashes. Current receipt paths are in migration-packet.json.

The source-only increment carries scripts,Lean control changes,docs,small policy configuration and bulk-manifest.json. Its recorded archive has absolute VM path,size,SHA-256 and an internally pinned per-file inventory. Copy the archive into archiveRelative,extract with tar --zstd -xf ARCHIVE -C tests/directruntime-20261104/shared-translator/artifacts/h68-bulk,and run verify-bulk.py before tests. There is no data download or fallback to legacy fixtures. H41 cache transfer remains separate;no ship-cache.sh.

Owned backfill now observes all806 inventoried selected-field variants from49 existing corpus fixtures through the same test driver: default165decoded/388refused/253noStandalone;composed172/381/253.553 unknown-root refusals per reader;25 natural differences are18 refusal reasons and7 newly decoded witnesses. Case hashes,source pointers/IDs/spans and field labels are independently checked. This corpus includes intentional mutations and unauthenticated compiler-header claims;it does not establish exhaustive grammar coverage,intrinsic proof closure,source preservation or backend support. No new translator is introduced.

Checking cost was warned and measured: original57-kind driver3.198s;uncached806 capture39.646s;invocation-local parsed-fixture caching reduces frozen extended per-file replay to5s(rounded toolkit duration),with identical old/new matrices. Whole ownedbuild+axiom+frozen/preflight/audit11.002s,RSS1192416KiB,min13983961088B. Those are different test workloads and timing boundaries,not a production runtime benchmark. Final cached-driver MCP0errors27.290s;post-relocation checks are recorded in retained evidence. No budgets,theorems,refusals or producer paths change.

H44 final VM gates PASS: all10affected-file MCP diagnostics0errors(280.760s,scopepeak2277277696B,minreserve11911069696B);server stopped. Owned344-job build,axiom inventory,11per-file controls including original57-kind plus806variant suites,metadata/modality/114witness preflights,native18+2,audit defect regression and SolKey377/131/131 all pass39.992s,RSS1254016KiB,minreserve12709044224B. Actual Lean4.24.0/Lake5.0.0-src+797c613;12GiB/no-swap,-j1,threads1. Exact commands/outputs are in retained evidence/h44.

Frozen archive: /workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/h44/bulk-0de09096a654c43c.tar.zst
207427bytes;SHA256 0de09096a654c43ce6ecf6bf2ae958bffca8dbc2732273b4db881ffba28978a5;50datafiles/3229786bytes. verify-bulk.py and independent actual extraction roundtrip passed. Independent final finder/skeptic read-only reviews found no hidden bulk,scope or completion defect. Manifest is committed;archive stays on this VM for coordinator pull. No publication or shipment is claimed. Full lane and RUNTIME_GATE_PASS remain pending CR migration,D WASM,full parity/closure and final gates.


## Adopt published5f7 checkpoint

Coordinator2026-11-06 published5f7bb1441566aaad64a34436904afc61de762fd2,including e778 through fb30388ff. Fetch and both original-base/e778 ancestry checks passed. Startup checkout da74bc6b contained two automatic publication merges and matched5f7 byte-for-byte;refs/codex-recovery/shared-translator/pre-5f7bb1441 preserves it. Requested rebase completed cleanly to5f7 without source/data loss. No runtime Shared/DirectRuntime source differs from4095.

H68 ownership-baseline.json is explicitly updated to that exact recorded5f7 commit;no moving reference determines the pin. The disposable regression now reads this recorded pin for its checkout and receipt. Its old moving-audit control still uses the original4095 code,so the reported defect remains independently reproduced after future authorized recorded-pin updates. H44 archive/data inventory remain immutable. Existing Import.lean still uses printer/parser/macro;no CR migration was delivered by this publication. Full-lane limits remain unchanged.

Fresh post-adoption gates PASS45.133s,RSS1257256KiB,minouter12611284992B. Owned344-job build,exact axiom inventory,old57-kind/806variant suites,modal/direct controls,KeySort,native18+2,pinned-audit regression and SolKey377/131/131 annotations OK. Actual Lean4.24.0/Lake5.0.0-src+797c613;12GiB/swap0,CPU1,threads1/-j1. No Lean source changed;no new theorem or axiom. Independent finder/skeptic read-only,no Lean/server,verified ancestry,pin behavior and unchanged runtime/data;no findings.

H44 external evidence manifest: tests/directruntime-20261104/shared-translator/adoption-5f7-manifest.json. Archive /workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/adoption-5f7/evidence-7ea5df486b5f1f3a.tar.zst;9179bytes;SHA256 7ea5df486b5f1f3a06475e14e0464623a7ddfd4952b9f0da8f1a9a91a15ca9f7. Commands/exits/wall/RSS,axiom signatures,rebase and review receipts are retained there. H41 exact-head cache preparation follows this commit;delivery remains coordinator-pending. Original CR migration/WASM/full-closure obligations remain open.


## H70 exhaustive observed-corpus census

New corpus-inventory.py accounts for every occurrence in a pinned finite input set:77existing corpus fixtures,5H68 normalized and5raw packets,8retained H41raw packets.95documents,55218nodes,73kinds,1926immediate-field structural forms and12899explicit identity-reference slots. All57modern Solidity and16Yul kinds occur;legacyThrow remains modern-compiler-negative/unobserved. Source/header bytes match88documents;7lack matching binding. Neither status proves compiler authenticity or AST/source equivalence.

Node rows preserve exact fixture/node hashes,JSON pointer,parent/source-unit links,ID/scope presence and raw values. Fourteen declared reference fields have explicit policies;operator function aliases apply only to Unary/BinaryOperation. The five actual function fields are UsingFor child containers with nested IdentifierPath references. Opaque internalFunctionIDs/typeIdentifier and externalReferences semantics remain gaps;candidate-key heuristics include false positives.10374slots uniquely match an input node ID;2451negative and57unsigned-negative candidates plus17null slots remain classified separately. Structural ID match does not prove lexical scope,shadowing,overload selection or intrinsic/source correctness.

Existing selected reader observations are joined only by exact fixture SHA/pointer and verified case/kind/route identity:330of1926forms have an observed occurrence;1596have none. No whole-form semantic verdict is inherited. Independent verification reconstructs every input occurrence and reference slot,checks all field schemas,complete pinned Git/H44 input set,receipt hashes,source-anchor claims and binding counts. Eleven identity controls cover missing/ambiguous/cross-root/bool/null/unsigned cases;three altered observation identities fail closed. All bulk remains outsideGit.

Finder/skeptic confirmed and fixed join/source-completeness/source-binding verification gaps,then re-reviewed with no remaining findings;no Lean/server/writes. VM owned344-job build,axiom inventory,existing57+806/modal/direct controls,KeySort,native18+2,census and SolKey377/131/131 pass31.984s,RSS1256536KiB,minreserve12451889152B. Final strengthened verifier/controls pass5.644s,RSS111616KiB. Lean4.24.0/Lake5.0.0-src+797c613;12GiB/no swap,CPU1,threads1/-j1. No Lean declaration,theorem,axiom,producer API or proof budget changes.

Manifest: tests/directruntime-20261104/shared-translator/corpus-inventory-manifest.json. Archive /workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/corpus-5528aeccfdfe4ba5.tar.zst;2749030bytes;SHA2565528aeccfdfe4ba5703a6e16b39b79dee1e690613bd41d2f40a071cadfee1645. Extract under artifacts/corpus-inventory before verifier;inputs require the recordedbc997source tree plus immutableH44 packet. This closes finite occurrence accounting,not exhaustive semantic language coverage. CR existing importer migration and DR-D entrypoint/WASM closure remain waits;no relay constitutes owner agreement. RUNTIME_GATE_PASS and original full queue stay open.


## H70 all observed structural-form reader controls

The existing ConstructReaderControls observer now also runs one exact witness for each1926frozen structural forms/73kinds;no translator code is copied. Source fixtures and IDs are checked against the immutable census. Default reader408decoded/1224refused/294noStandalone;canonical composed469/1163/294.1632unknown-root mutations per reader refuse.213differences comprise61refused-to-decoded witnesses and152changed refusal reasons;no decoded witness became refused. General-producer expression printing751printed/112refused is recorded separately;this is not the actual importer migration. Original57-kind and806selected-field matrices remain byte-identical.

Five retained H68 compiler executions provide738unique raw/normalized kind/span/retained-ID pairs. ID field presence92both/565raw-only/81neither;missing IDs are not called preserved. ReferencedDeclaration presence98both/640neither:80exact numeric identities,18existingu32-signed normalizations. Retained name/member/operator/kind/prefix/tryCall/type metadata compare to raw source fields. Unique matching does not establish lexical scope,shadowing,overload/type adequacy or source semantics. Arbitrary literal values and contexts remain outside a one-witness structural-form claim.

Independent finder/skeptic requested mandatory verifier integrity chaining and separate presence counts;both fixed and re-reviewed without remaining findings. New corpus_packet.py verifies portable archive/index/perfile/exactmembership/count/bytes for both generator and verifier;H44inputs separately reverified. No integrity fallback. Census manifest gains only archiveRelative;its archive bytes remain unchanged. All generated reader cases/matrices,identity ledgers/logs stay outsideGit.

Checking slowdown warned/measured:previous driverabout4s;extended frozen replay8s rounded while old matrices remain unchanged. Actual capture8.296s,RSS634636KiB;per-fileMCP0errors18.414s,scopepeak978710528B;server stopped. Owned344-job build,axiom inventory,frozen all suites and independent checks PASS12.340s,RSS1192420KiB,minreserve12408795136B. Final integrity checksPASS0.533s,RSS65836KiB.12GiB/no swap,CPU1,threads1/-j1;no proof/heartbeat changes,new axioms or runtime API changes. These are different test workloads,not before/after production runtime evidence.

Manifest: tests/directruntime-20261104/shared-translator/corpus-readers-manifest.json. Archive /workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/corpus-readers-68b78f8ac2ad9719.tar.zst;159929bytes;SHA25668b78f8ac2ad97199eaa54b83a0f19870acb56bf3ca965f29bcf17a908abe0be. Restore census+H44 archives and this packet,run verification,then the frozen per-file test. H41exact-head cache stays on VM for coordinator pull. Original CR migration/native-browser WASM/native closure waits remain;no relay establishes agreement or validation. RUNTIME_GATE_PASS and whole queue remain pending.


## Published002f manifest-verification follow-up

Remote002f4f1786a5378f7e06dced5548d714f3e73a38 contains f04;originalb419/f04 ancestry verified. Startup ec924 automatic-merge head preserved at refs/codex-recovery/shared-translator/pre-002f4f178;locked fetch/rebase passed. Ephemeral writer-lock directory was initially absent(exit66),recreated before successful fetch. Ownership audit explicitly pins recorded002f;no moving-ref selection.

verify-corpus-readers.py now authenticates its own archive/index/extracted files through the same packet helper and compares all published case/outcome/refusal/transition/pair/field-presence counts to corpus-readers-manifest.json. verify-corpus-inventory.py compares manifest counts/sourceBindingCounts and independently reconstructed full totals,including document/kind counts. adoption-5f7-manifest.json gains archiveRelative. Existing archive/data bytes remain unchanged.

manifest-controls.py executes both healthy verifiers,then12read-only in-memory manifest mutations:archive hash,index hash,census counts/source bindings and every reader count group. Every mutation refuses;both frozen packets reauthenticate afterward. No fixture/manifest bytes are changed by controls. Finder/skeptic read-only,no Lean/server,confirmed no remaining defect.

VM owned344-job build,axiom inventory,57/806/1926frozen suites,modal/direct controls,KeySort,native18+2,audit regression and SolKey377/131/131 annotations OK pass43.694s,RSS1251300KiB,minreserve14984622080B. Final controls pass10.247s,RSS330724KiB,min14682075136B. Actual Lean4.24.0/Lake5.0.0-src+797c613;12GiB/swap0/CPU1,threads1/-j1. No Lean source or proof/signature changes;per-fileMCP not needed for Python/JSON-only edits.

H44 external evidence manifest:tests/directruntime-20261104/shared-translator/manifest-followup-manifest.json. Archive /workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/manifest-followup/evidence-8e6e9df3e718dd9e.tar.zst;10092bytes;SHA2568e6e9df3e718dd9e50e0b01c7b4d0706124703d4c9e5646cb554bc5f9bdd5c07. Exact commands/exits/axioms/reviews/setup receipts retained there;no new bulk data inGit. H41 exact-head cache prepared locally after commit,no ship-cache.sh. H77 producer packet remains unchanged. Original CR importer migration,native-browser parity/WASM/native closure,full source/semantic preservation and final gates remain open;RUNTIME_GATE_PASS pending.


## Published e62 read-only controls and derived totals

Fetch/rebase onto e62f0230bcb683240be287b543443a38f317887c passed after verifying originalb419/92f ancestry. Prior92f preserved at refs/codex-recovery/shared-translator/pre-e62f0230b. H68 audit pin explicitly records e62;no moving-ref selection.

Both corpus verifiers now offer --read-only. Inventory emits checks without rewriting verification.json;reader verification compares recomputed normalization/summary JSON with retained outputs instead of rewriting them. Default output-refresh behavior remains available for existing generation workflows. manifest-controls invokes --read-only with Path.write_text trapped,then verifies unchanged packet membership,inode,size,mtime andctime across census/readers/H44 packet directories. Packet hashes are also reauthenticated. This checks those frozen artifacts,not every filesystemwrite.

Every negative control now requires an exact specific assertion message;the generic manifest/traceback fallback is gone. Cases and unknown-root refusal totals derive from len(cases) and computed callableCounts. Fixed1926/1632snapshot expectations remain regression guards,not report literals. No counts changed,no data archives or runtime translator altered.

Owned344job build,axiom inventory,57+806+1926/modal/direct suites,KeySort,native18+2,audit regression and SolKey377/131/131 annotations OKPASS54.821s,RSS1254768KiB,minreserve13906223104B. Two healthy verifiers and12altered manifests pass exact-label rejection;frozenMetadataUnchanged=true. ActualLean4.24.0/Lake5.0.0-src+797c613;12GiB/no swap,CPU1,threads1/-j1. No Lean source,theorem,axiom,premise,exclusion,proofbudget or trustboundary change;no newMCP needed for Python-only edits. Independent read-only finder/skeptic(noLean/server) confirmed no remaining checkpoint defect.

External evidence manifest:tests/directruntime-20261104/shared-translator/e62-followup-manifest.json. Archive /workspace/solidity-lean/tests/directruntime-20261104/shared-translator/artifacts/e62-followup/evidence-1aa73c9bc42f5844.tar.zst;9689bytes;SHA2561aa73c9bc42f5844dcdb9fbbfb0153fbc3411132f2aea284394b5702f735a76f. Exactcommands/output/signatures/resources/reviews retained outsideGit. H41cache prepared locally after commit,no ship-cache.sh. H77producer artifacts retained unchanged. CRactualimportermigration,native-browserWASM/nativeparity+closure,fullsource/semantic preservation,before-afterruntime and finalfullgates remainopen;RUNTIME_GATE_PASS pending.

### All-occurrence integrity backfill (2026-11-06)

The opt-in occurrence generator accounts for all 55,218 nodes in the fixed 95-document census. `verify-occurrence-readers.py --cases-only` authenticates each input, pointer, node hash, route and identity. `occurrence-integrity-controls.py` accepts the healthy packet and rejects five in-memory corruptions with exact failure markers, traps writes, then reauthenticates the census. These are external Python checks, not Lean proofs or reader execution. Generated cases and logs remain outside Git; `occurrence-integrity-manifest.json` records their paths, sizes, hashes and command.

Independent read-only finder and skeptic used no Lean/server. The skeptic requested exact failure markers and stronger read-only controls; both were fixed and re-reviewed with no remaining confirmed blocker. The earlier 467.071-second reader capture stopped with exit137 and produced no complete matrix. Optimized Lean validation, reader capture/replay, semantic obligations and producer migration/closure remain pending; no runtime gate pass is claimed.

### H90 first reader increment: narrow locals

`Shared.localTypeName` retains every canonical narrow primitive spelling for existing `elabTyW`; the general `localTypeName_of_narrow` theorem proves that decoder fact with the standard axioms `propext`, `Classical.choice` and `Quot.sound`. `localPrim` broadens only tuple scalar shape admission. Parameters, returns, storage and reference-local readers retain their earlier refusals. No Reader signature, producer implementation, Core/Source definition, proof-search block or exported wrapper changed. The extraction audit still compares the original implementation exactly after a hash-pinned normalization of this reviewed increment; its immutable ownership pin is `ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6`, with the authenticated H82 scope.

Q-H90-CENSUS option2 designates all78 AST files at CR `e0a5ac26ed521bde70e3ce4da5120d05a991d9ca`. On identical inputs and dependency trees, base `3a1e70479092b11d4d0f12e48690b82d316ad5ff` admits236 functions and the increment245, among1655 functions/1486 printed bodies: nine gains,12 refined refusals,zero losses. The1599/1446/226 figures remain historical; the original68-file selection is not asserted reproduced. These are printer/name-matched and decoder observations, not elaboration, overload, whole-contract or source adequacy.

Nine runtime controls cover assignment, checked unsigned/signed aborts, unchecked wrapping, simultaneous tuple capture/right-to-left repeated writes, a deliberately wrong repeated-target assertion, and narrow shadowing without leaking its width to an outer wide local. Six positive model controls prove and three abort controls refute. The existing standalone narrow range guard reverts, whereas solc carries Panic(0x11); this inherited model/source gap remains explicit. Parameter/storage refusal controls pass.

All5692 frozen structural reader observations were recaptured into a separate H90 profile:13 decode gains and14 refusal refinements, all individually retained; historical archives remain untouched. The scope check establishes that changed subtrees contain narrow locals/tuple leaves, not a causal or semantic proof. Both unknown-root profiles still refuse every callable witness. Independent verifiers pin the exact CR commit/path set, derive summary counts from unique compiler identities, authenticate inputs and archives, and support relative archive replay.

The original all-occurrence capture is now complete:55218 nodes across95 documents/73 kinds/1926 forms; default28648 decoded/17063 refused/9507 non-standalone, composed28862/16849/9507, and45711 unknown-root refusals per reader. This default-versus-composed delta is not attributed to H90 alone. The quadratic uniqueness run stopped137after467.071s without a matrix; the HashSet version captured in32s and replayed frozen data in25s. External integrity controls pass, with healthy verification read-only. Data/logs remain offGit with paths, sizes and hashes in the H90 manifests.

Per-file MCP checks, owned builds, actual Lean4.24.0/Lake5.0.0-src+797c613, exact12GiB/no-swap/threads1 limits and KeySort pass were measured on this VM. All25 affected per-file gates passed after building the missing IntrinsicControls dependency and rerunning ProofAudit; the initial missing-olean failure is retained. New theorem axioms are[propext, Classical.choice, Quot.sound], within the unchanged standard set. Finder/skeptic used no Lean/server; raw-string/EOF/quoted-name findings from inherited backfill and current verifier completeness/relative-path findings were fixed and re-reviewed. This is a local reader increment, not RUNTIME_GATE_PASS or full-assignment completion.

Next remain H90's other type forms, CR's exact34-fixture/20-pin migration, full importer parity/migration, and the newly requested primitive-return/stack/native-cost repairs. D's84-case/206-C reports require actual artifact delivery here and do not validate this new source head; known timing STOPs are not rerun unchanged.

The final Boolean-dispatch proof checks in13.9s versus13.4s for the base in single warm MCP samples; these are checking observations, not native/browser performance acceptance. Earlier slow proof attempts and their diagnostics remain in the offGit evidence.

### Exact H68 CR intake verification

Fetched apply `c0c53877f279964b86d55f56ea0bba4ec440a788`, hash-only correction `e13535d56684c196ba011ad1f07f373314ee1105` and current CR `19a7a1a9f764b19e75b16a9f941618a33a1678cf`. The owned verifier checks34unique exact changed fixtures, identical headers/nonmetadata fields,44unique shared pin entries/861occurrences across5exact changed files, and20Leanmodules with128changedhashliterals. All relevant current CR blobs equal the checked apply/correction blobs. Six tamper/healthy controls pass. Independent read-only finder/skeptic findings on uniqueness, changed sets and current-head identity were fixed; neither used Lean/server.

This is Git-blob verification, not compiler regeneration, metadata correctness, Lean gate acceptance or reader-outcome parity. CR remains unmerged here. Frozen matrices await re-observation on the landed fixture bytes;7selector-drift and4no-source fixtures remain underH102. The exact H68 commit lookup wait is cleared, and the coordinator says the H44 archive pull is no longer needed. Actual importer migration/fullH90parity remain open. Published master706e36825929d6d0084dc08b88de9349abcd25aa was adopted; the audit pin records that immutable commit. No production Lean definition, statement, proof, budget or axiom changed in this checkpoint.

### Guarded primitive-return runtime repair

`Shared.primitiveReturnObligation` prepares fresh program-local return slots and uses existing `renameStmts`, producer `lowerBodyLoops` and `lowerReturns`; the old return-free branch remains exact under the pinned audit normalization. Primitive parameters/returns with empty width metadata are supported here; reference and width-bearing returns remain refused. Return slots are not entry quantifiers. No Reader interface, proof-search/exported wrapper, Core/Source definition or budget changed.

Eighteen finite box/diamond executions plus one storage side-effect observation pass. Eight fresh compiler-AST production requests yield6proved/2refuted. Fresh regeneration of the original13ControlTuples functions yields9proved/4unsupported, with exact function/source-ID/status/reason controls. Remaining refusals are aliased non-stack tuple targets, unary side effects, narrow inline arrays and tuple calls. These are checker observations, not ABI return-value/source/compiler/native correctness proofs. The existing division guard reverts while source division by zero uses Panic(0x12); the gap is retained.

Correction: nine owned module builds passed; the957e aggregate27-file pass claim overlooked SelectionControls, which also expected the obsolete refusal. Main25/27passed, recovery restored returnGuard for26/27. The later fixed-byte checkpoint migrates exact overload selection controls and reruns that remaining check. The initial expected-refusal failure and earlier diagnostic attempts remain in the offGit evidence. MCP checks pass; new helper/assertion builder axiom inventories are[propext,Quot.sound]. The final recovery gate took20.768s with peak child1285240KiB, exact12GiB/swap0/j1/threads1 and over11GiB outer headroom. KeySort and Lean4.24.0/Lake5.0.0-src+797c613 passed in the main affected gate. Independent read-only finder/skeptic findings on exact13outcome checks were fixed. Native/WASM consumer recheck, stack/native cost repairs and final runtime gate remain open.

### Authenticated historical native/WASM stack and cost intake

The delivered729b0cb18b0d archive and all10named members/request hashes verify locally. Retained files use repository-relative layout under the ignored owned inbox, not live `.lake` roots; extraction rejects symlinked roots/ancestors/members and nonregular targets. Eight external controls pass. No delivered native/JS/WASM code or stopped benchmark was executed. The original artifact source is0140eb13, not the pending957e5def repair.

Both build manifests have identical343distinct source-file rows, each matching exact Git0140bytes, and206recorded compiled-C hashes agree. The206object bytes are not supplied/verified. Saved249native/browser records match on the seven core result fields and source identity; UI enrichment/full wire objects are outside that projection. Saved83function/3round median/p95 statistics reproduce exactly. Native median STOP+21.32percent and browser startup STOP+32.20percent remain; median wire size+22.03percent is a confounder, not a causal explanation. Startup is one saved fresh-page/process observation, not a cold distribution.

All10recorded WASM frame offsets fall inside their indexed function bodies in the exact6ae1d6db binary. Top index3207 is exported malloc; internal indices3126/2208/2210 repeat. The binary has17function imports/3922defined functions and no name section. This does not identify the Lean routine or establish AST traversal/proof-search causality. Request an exact function-index map, or a matching fresh repair-build trace/map, before changing a source algorithm.

Final static diagnosis2.236s/54412KiB and controls0.645s/47744KiB pass; the missing GNUtime setup attempt is retained and Python wait4 accounting used. Finder/skeptic extraction and module-uniqueness findings were fixed/reviewed. No production Lean, theorem, axiom, budget or interface changed; no new Lean gate/cache/runtime acceptance is claimed. Published33eb46304 was merged and recorded as immutable audit baseline. H44 physical delivery is confirmed separately; consumer inspection and fresh957e native/WASM validation remain pending.

### H90 fixed-byte local increment

Canonical bytes1..32 locals retain exact RawTy spelling through the single shared reader and existing intrinsic byte-width/marker elaboration. The general localTypeName_of_fixedBytes decoder theorem uses[propext,Classical.choice,Quot.sound]. Reader signatures and parameter/state/reference callbacks are unchanged.32marker/spelling controls and20fresh AST requests across box/diamond pass:12proved,4refuted,4unsupported. Copy, complement, tuples and width-sensitive widening/indexing are covered. Positive `.length` checking remains unsupported with `4294967296 does not fit uint32`; false length assertions refute. This is not full fixed-byte/source/backend adequacy.

The pinned78-file census remains245admitted of1655functions/1486printed, with3incremental refusal refinements and zero lost admissions. Eight incremental profile observations change(2decode gains/6refinements);12occurrence observations change per reader across55218cases. All earlier decoded behavior, source identities and unknown-root refusals are preserved. The transition verifier authenticates prior archives/members/casefiles/fixture hashes and pointers; fixed-byte subtree presence is a scope indicator, not causal proof. Prior archives remain immutable and are referenced through before-manifest hashes.

Nine owned modules build; all28affected files pass after exact-overload SelectionControls recovery. The separate historical957aggregateclaim is corrected to26/27, not retroactively calledpassing. MCP, KeySort, axioms,20modality requests, full occurrence capture/replay, three transition-integrity controls and frozen inventory verifiers pass under12GiB/swap0/threads1/j1; no proof budget increase. Finder/skeptic archive/case-binding findings were fixed. Source checking18.545s and final20-request checking12.108s are individual samples, not native timing acceptance. Other forms/contexts, CRlanding/migration, latest-source native/WASM closure and final original obligations remain open.

### Exact historical stack symbols received

The d43c81b85561 archive verifies214639bytes,9pinned members plus the delivery receipt.3939unique contiguous symbol entries cover17imports+3922defined functions in the previously delivered exact6aeWASM. All10recorded frame occurrences map to sixindices:3207emscripten_builtin_malloc,2203LTm.fitsM,2205its boxedcontinuation,3126lean_apply_1,2208LFml.fitsM and2210its boxedcontinuation. The supplied ReadBounds source equals exactGit0140bytes and currentSource.

The authenticated producer relink/postprocessing receipt reports a bit-identical diagnosticWASM and successful recovery after its map-filename error. That relinked binary is not separately supplied; no local relink or independent repeated byte comparison was performed. This is engineering attribution of the recorded historical frames, not a rootcause theorem, algorithmrepair or fresh957e/fixed-byte qualification. Three external integrity controls pass; finder/skeptic no confirmed blocker. No ReadBounds definition/statement/budget was edited. Route its named frames to the current owner for diagnosis before any definition repair, preserving current caps and compiled-link theorems. OT-STACK-SYMBOLS artifact wait is cleared; do not resend the accepted request or rerun unchanged timingSTOPs.

### Delivered sourceBuild1e8 intake (2026-11-07)

`verify-sourcebuild-intake.py` pins the three H77 input hashes, verifies all 505
evidence files plus their embedded manifest, checks the exact five runtime archive
members, and matches the native/WASM/JS bytes to their recorded build manifests.
The native and WASM source arrays agree on 343 distinct module names.
`sourcebuild-1e8-intake.json` records these limited observations; the archives stay
outside Git in the coordinator input directory named there. No delivered code was
extracted or executed. Git source identity, current-reader freshness, closure,
performance acceptance and source/compiler preservation remain unverified.

The verifier and its three external negative controls pass. Independent read-only
finder and skeptic reviews used no Lean/server/builds: finder found no blocker;
skeptic requested a unique-module assertion, now added. These external checks are
not Lean proofs; this increment changes no Lean statement, proof, budget or axiom.
The separate address-local draft remains uncommitted and incomplete: source MCP
checks pass, but its end-to-end sender control fails with `unknown name msg`.
Neither that control nor address parity is claimed passing by this intake.

### H90 explicit nonpayable address locals (2026-11-07)

`localValueTypeName` dispatches explicit `ElementaryTypeName/address/nonpayable`
nodes to the existing `.named "address"` marker. Both executable statement paths
use it. Parameters, state, payable and missing metadata retain their refusals.
`localValueTypeName_of_address` is a general decoder equation, closed with only
`propext`, `Classical.choice`, `Quot.sound`. No production module/import was added.
The guarded `msg.sender` bridge requires the compiler magic-message identifier,
negative builtin reference and address result type; user/missing identities stay
ordinary fields. Base decoding still precedes member-name validation.

Nine owned module builds and all 30 affected per-file gates pass, including
KeySort and the axiom inventory. The 16 address box/diamond requests yield
10 proved, two refuted and four unsupported outcomes. These are model/checker
controls, not source/ABI/environment adequacy proofs. The initial combined command
exited 1 only at the static ownership audit because its MCP config overlay was
visible to Git. The audit and downstream controls pass without that overlay;
no allowlist was broadened. Both runs are retained.

The matched78-file census remains 245 admitted/1,486 existing printed out of
1,655 functions: this increment adds no whole-function admission. Four address
refusals reach later unsupported constructs. The incremental eight-profile
transition has two refusal refinements; the occurrence matrices change at10
default/14composed rows. Both readers replay all55,218 occurrences, preserving
observed decoded outcomes and45,711 unknown-root refusals per reader. These
counts do not assert decoded-term equality or importer parity.

Finder/skeptic read-only reviews found no remaining blocker after the diagnostic
order repair. `address-manifest.json` records commands, resource measurements,
source hashes, reviews and the H44 bulk archive path/hash; generated AST/logs
remain outside Git. Full source/semantic closure, other H90 forms/contexts,
CR H68/H102 landing/importer migration, native/WASM qualification and timing
acceptance remain open. Historical STOPs were not rerun.

### H77 fixed-byte recipient inspection (2026-11-07)

The five delivered files from native-browser head `14a39effa376` are now inspected,
resolving their missing-byte wait. `verify-fixed-byte-intake.py` authenticates
875 evidence payloads and five runtime payloads against both pinned outer hashes
and embedded/external indexes. All 343 unique source records match Git build head
1b2bdb490054293c86cddb5e4b7fa15736bae25b. The eight executable-boundary modules
(five Shared modules, ControlTuple.Adapter, Memory.Reader, DirectRuntime) also match producer
2738af99661d7ba582c92519b20d47bcba34a5a4. This is a boundary-subset comparison
against 2738, not an entire producer-tree comparison. Native/WASM/JS bytes match
their recorded build manifests. Nothing was extracted or executed.

Saved native/browser projections agree after removing browser boot and reply
timing fields; unique case identities and actual WASM boot hashes are checked.
Box/diamond fixed-byte inventories contain 11 requests each, including one guard
each; A 9, B 84, C 14 and functional 83 inventories also match. B remains 64 proved,
16 refuted and 4 pending. The four mandatory Identity box/diamond x IR/non-IR rows
are proved and correctly tagged in these saved observations. This is not a
new execution, source-mode adequacy proof or qualification of the newer address
reader. The 206 selected module records are counted; actual C/object bytes are
not independently verified.

All 19 handoff gate receipts match their indexed bytes and commands:18 exit 0 and
one exit 1. The invariantCountsToBound browser stack failure remains; its 10 saved
frames fall inside the delivered WASM's indexed bodies. No function-name/cause
repair is inferred. Native cost/browser startup STOPs remain reported holds;
no stopped benchmark or build was rerun.

Four new external negative controls and three shared archive controls pass.
Finder found an omitted Memory.Reader comparison; it is now included and both
reviewers confirm no remaining static-intake blocker. An initial incorrect
assumption of nine runtime modules and the intermediate report of the seven-module subset
are preserved outside Git. Nine is the development cache count, not this runtime
boundary count. `fixed-byte-intake.json` records provenance, counts, saved gate
commands and limits. No production Lean, theorem, axiom or budget changed.
CR relay remains held under H118; full importer parity/migration, address-native
qualification, authorized stack/cost repair and whole-goal acceptance remain open.

### Existing environment members (2026-11-07)

`Shared.environmentMember?` reuses `EnvKey.ofParts` for guarded `msg.sender`,
`msg.value` and `block.timestamp`. Both executable expression paths share it.
Root kind/name, compiler magic type identifier, negative builtin reference and
result spelling are checked. Matching metadata is not authentication. Ordinary
fields, unsupported members and base-before-member error order remain intact.
No Source/Core, Reader signature, entry premise, import or proof budget changed.
The helper's axiom inventory is empty; no new source adequacy theorem is claimed.

Nine owned modules build and 31 affected Lean files pass. The final strengthened
control file also passes MCP and a per-file gate with exact source-ID assertions.
Its 16 box/diamond requests produce eight proved, four refuted and four unsupported
outcomes; block.number and tx.origin keep their exact unsupported reasons.
These exercise the existing intrinsic model, not source/world/native adequacy.
The compiler first rejected an invalid nonpayable msg.value fixture; the valid
fixture uses payable functions. An initial incomplete MCP response during adopted
master dependency setup is preserved; retry and final validation pass. Neither
failed attempt is retroactively counted as passing.

The strict environment transition requires zero changes across eight saved
profiles, both 55,218-row occurrence matrices and the pinned 78-file census.
All replay unchanged: canonical admissions remain 245 versus 1,486 existing
printed functions among 1,655 functions. This preserves observed outcomes, not
decoded-term equality. The fresh model controls cover the new routing separately.

`environment-manifest.json` records exact commands, source/fixture hashes, source
identities, reviews, resources, timing boundaries and the H44 archive path/hash.
Source checking took four seconds versus six in the earlier address gate; these
are separate warmed runs with different dependency states, not matched runtime
performance acceptance. The production delta is 19 added/eight removed Lean
lines, no new production module and one test module. Global timing STOPs remain.
Finder/skeptic final read-only reviews found no checkpoint blocker. CR relay
remains held under H118; importer parity/migration, fresh native/WASM qualification,
source/physical adequacy and the remaining original queues remain open.

### General environment decoder guard proof (2026-11-07)

`environmentMember?_guard` proves that any successful helper result originates
in the existing `EnvKey.ofParts` map and satisfies the negative builtin-reference
guard. It quantifies over arbitrary JSON inputs, members, result spellings and
keys; it is not a compiler authentication or source/world adequacy theorem.
The exact statement was unchanged throughout repair. Final axioms are only
`propext` and `Quot.sound`; no axiom, admission or budget increase was added.

Removing the lemma/doc block reproduces the pre-work Translate file byte for
byte. There is no executable definition, import, Reader signature or entry-premise
change. The production delta is 37 proof/doc lines and no new module. Nine owned
modules build; six focused files pass, including axiom/signature inventories,
32 existing environment/address model requests and KeySort. Actual versions are
Lean 4.24.0 and Lake 5.0.0-src+797c613. The serial 12 GiB/no-swap gate exits zero
in 34.0344 seconds; the cgroup peak is 229,416,960 bytes and minimum outer
available memory is 11,538,579,456 bytes. This is checking evidence, not runtime
performance acceptance. Prior census outcomes are retained because definitions
are identical; only their source-file proof hash is refreshed.

Failed proof attempts and MCP goal/tactic trials are preserved in the H44 archive
indexed by environment-proof-manifest.json. Independent read-only finder and
skeptic reviews found no remaining proof checkpoint blocker. The scope baseline
is the immutable pre-work head f83a7016, which already contains published05d2c2587
and an inherited README-only bookkeeping commit636fc9880. That unrelated file
was preserved, not authored or modified by this proof increment.

The accepted H71 address handoff still lacks local payload bytes; its transport
route is not duplicated. Existing environment qualification, H118-held CR relay,
importer migration, ReadBounds production-owner resolution and all original
source/physical/performance obligations remain open.


### Address handoff metadata integrity

`verify-handoff-metadata.py` authenticates the delivered native-browser a14d56c9
handoff and its committed manifest, then verifies the two explicit Translate and
Compose source pins at sourceBuild0eb39db1. It checks declared 16-address counts
(10 proved, 2 refuted, 4 unsupported, plus two guards), 24 unique gate receipts
(23 pass, one failure), pending runtime status and retained performance STOPs.
This is metadata consistency, not inspection of receipt contents, the reported
343-module runtime index, 206 selected objects, binaries or request results.
All six referenced address archives/indexes are absent locally at capture.
Presence alone never changes the verifier's `payloadInspected: false` result.

Three external controls include twelve rejecting mutations for independent drift,
coordinated false acceptance, erased failures/STOPs, duplicate gate/artifact
identities and unsafe locators. Read-only finder and skeptic found no confirmed
checkpoint defect; neither used Lean/server/builds or writes. Four lightweight
checks pass, including the unchanged extraction/trust audit and whitespace check.
There are no production Lean changes or new checking/runtime measurements.
The ownership audit now pins adopted published master d93f6839c explicitly;
its scope allowlists are unchanged.

`address-metadata-manifest.json` records portable archive/tool/Git pins and exact
commands. Restore its H44 archive under `artifacts/address-metadata`, then run
`python3 tests/directruntime-20261104/shared-translator/verify-handoff-metadata.py
--handoff tests/directruntime-20261104/shared-translator/artifacts/address-metadata/handoff.ticket`.
The external controls use the original coordinator inbox ticket. The archive
contains that ticket and report, not native-browser's missing runtime payloads.
No duplicate delivery ticket was issued. Fresh environment qualification,
CR fixture/importer migration, ReadBounds production-owner resolution and the
original stack/cost/performance holds remain open.


### Shared environment decoder proofs

`environmentMember?_guards` performs one general successful-decoder inversion
for the existing map entry, negative builtin reference and result spelling.
The existing `environmentMember?_guard` keeps its exact statement and projects
its first two facts; `environmentMember?_resultType` projects the type fact.
`environmentMember?_of_metadata` proves successful decoding from the explicit
root/name/map/magic/reference/result guards for arbitrary JSON. These are
metadata decoder facts, not compiler identity authentication, source/world
adequacy or intrinsic semantics transport. All four theorem axiom reports are
only `propext` and `Quot.sound`.

The initial independent proofs checked correctly but failed the paired local
checking limit: baseline median3.9615s, head6.3626s (+60.61%). That STOP, its
source snapshot, failed proof attempts and tactic trials remain in the H44
archive. Sharing guard inversion and replacing the positive proof's `simp_all`
with explicit rewrites preserves all existing statements and brings three
interleaved same-path checking medians to3.9282s/4.1776s (+6.35%, below10%).
This local proof-checking result releases no native/browser performance hold.

The final serial12GiB/no-swap gate passes nine requested owned module builds
and six affected per-file checks, including 32 existing environment/address
model requests, axiom/signature inventories and KeySort. Gate wall time39.9118s,
child maximum RSS1261764KiB, cgroup peak230342656bytes, minimum outer available
memory11480817664bytes. Lean4.24.0/Lake5.0.0-src+797c613 and threads1/-j1 remain
unchanged. Final source and inventory MCP diagnostics report zero errors.
Inherited dependency warnings are retained. This is checking evidence, not
matched whole-build or runtime performance acceptance.

Normalization verifies the old guard statement byte for byte, removes only
three added theorem/doc blocks and restores its former proof; the resulting
Translate file exactly matches immutable pre-work88a946c78971. Executable
bodies, imports, Reader signatures, entry premises and exclusions are unchanged.
Historical census/profile outcomes are retained, with only the proof-source
SHA refreshed; no fresh census capture is claimed. The pre-work head preserves
the existing clean published3a5b9de41 merge and prior66268454b intake checkpoint.
The ownership allowlists are unchanged.

Manifest: `environment-decoder-proof-manifest.json`; bulk logs, source snapshots,
paired checking script/results and checksums are outside Git in its recorded
archive. Independent read-only finder/skeptic found no confirmed proof or
normalization defect; neither used Lean/server/builds or writes. Original H90
forms/importer migration, inherited queues, absent address runtime payloads,
environment qualification and all stack/native/browser holds remain open.


### Portable decoder validation inputs

The active `environment-decoder-validate.sh` now preflights 185 exact data files
before Lean runs: 73 tracked files remain read-only and 112 untracked inputs
are confined to this lane's artifact directory. `validation-inputs-manifest.json`
records relative paths, sizes, hashes and required Git objects. The input
archive is off Git under H44, 1,571,832 bytes, SHA256
`fde3beea1c7d20ec0af848db05907d3ff66d9f0b2cb3254dbc17f2ee293aad95`.
Its data pins derive from existing committed manifests and authenticated
archives at pre-work16c7ecb40198. Repeat capture produced identical bytes.

```bash
python3 tests/directruntime-20261104/shared-translator/validation-inputs.py
python3 tests/directruntime-20261104/shared-translator/validation-inputs.py --restore /path/to/validation-inputs-fde3beea1c7d20ec.tar.gz
bash tests/directruntime-20261104/shared-translator/bounded.sh bash tests/directruntime-20261104/shared-translator/environment-decoder-validate.sh
```

Preflight reports all missing/changed files and missing Git objects. Restoration
authenticates the whole archive and exact member set before writing, accepts
only missing untracked owned artifact data, and rejects changed existing files,
missing tracked fixtures, path escapes and symlinks. It never replaces CR's
tracked fixtures or silently updates their pins. Git history, Lean/Lake and
managed dependency setup remain separate prerequisites; no executable cache
is included. Unavailable bulk is a delivery dependency, not successful validation.

The proof baseline is an explicit immutable Git constant instead of a VM-only
`base-head.txt`. All nine requested builds, six per-file checks and census,
profile and static verifiers remain. Replay no longer runs the authoring
`--capture-manifest` operation, so expected committed census pins stay frozen.
No statement, premise, exclusion, axiom, gate check or resource budget changes.
This inventory covers the active decoder runner; historical runners retain
their own versioned checkpoint contracts.

Six external controls cover missing/idempotent restoration, changed tracked
and existing data, damaged or extra-member archives, per-member tampering,
unsafe paths/symlinks, tracked reclassification and missing tracked inputs.
A synthetic data tree copied 73 read-only files and restored all 112 archived
files; every one of the 185 hashes matched. This establishes data integrity,
not clean-VM/toolchain, source/compiler or runtime acceptance.

Published master80c156bf13d1 arrived during this work and was fast-forwarded
without discarding it. The full decoder gate and inherited five-fixture-proof
gate passed together in 27.1722 seconds, child maximum RSS1,266,512KiB, cgroup
peak220,766,208bytes and minimum outer available11,132,612,608bytes. Actual
Lean4.24.0/Lake5.0.0-src+797c613 and serial12GiB/no-swap/threads1/-j1 are unchanged.
These are checking measurements, not matched performance acceptance or release
of existing runtime timing STOPs. No production Lean or proof changed.

`portable-validation-manifest.json` records the evidence and input archive pins.
Both archives remain off Git under H44. Read-only finder/skeptic found no
confirmed restore-scope or freeze-boundary defect; neither used Lean/server,
builds or writes. Original H90/importer, inherited extraction, binary-courier
and native/browser obligations remain open.


### Saved H90 first-refusal frontier

After fetching master81512fd7298e, the lane contains that publication and keeps
its prior portability commit. The immutable scope publication pin advances to
81512fd7298e without changing allowlists; historical checkpoint source pins remain
versioned observations, not current-file equality promises.

`census-refusal-frontier.py` reuses the complete frozen H90 census verifier, joins
all1,655 rows to exact pinned fixture/contract/function/source-ID AST identities,
and partitions them as241both,1,245printed-only,4canonical-only and165neither.
The1,245 printed-only rows have66distinct first-refusal diagnostics. The largest
are binary common-type metadata293, unsupported expression211, unsupported type
declaration158, String expected86 and unsupported statement80. These counts
describe the saved reader observations; no fresh reader execution or admission
gain is claimed. Printed bodies still do not establish existing-route elaboration.

Each printed-only row retains its full identity, canonical function-AST hash and
observed elementary/user-defined type occurrences. Context labels follow the
outer function signature versus body; nested function-type parameter syntax in a
body stays body context. Occurrences are neither failing-node attribution nor
later-blocker discovery. The report does not infer an algorithm repair or relax
refusals. All original form-by-form support/parity obligations remain.

`census-refusal-frontier-manifest.json` pins generator, input census and off-Git
H44 report4233c0585c733b012656e8542d3b9dc13a0e06060c2b350de8ec83165cd4238e
(68,357bytes). Default replay compares the frozen manifest and full report bytes
without rewriting either. External controls cover all four partitions, duplicate
identity, invalid outcome/identity rejection and nested type contexts. Capture,
replay and controls pass. No Lean source/proof/interface/budget changes occurred;
no new Lean/MCP/build or stopped runtime benchmark was needed. Independent
read-only finder/skeptic confirmed the context correction and found no remaining
blocker; neither used Lean/server/builds/writes. Producer transport, migration,
runtime STOP and original acceptance dependencies stay open.


### Dynamic bytes/string boundary preparation

Pinned compiler0.8.34 produced DynamicBytesBoundary.sol witnesses for default
locals, alias initializers, allocation/literal bodies, parameters and state roots.
The existing metadata-retention helper preserves raw and normalized ASTs
separately. Eight function contexts and two state-contract contexts retain exact
current bytes/string type refusals. Alias/allocation/literal examples stop at
the enclosing type gate; they do not independently test those expression stages.
No production reader admission changes in this checkpoint.

DynamicBytesBoundaryControls.lean adds the general dynamicByteRows_preserved
equation for the existing elabTyW: every dynamic-byte spelling preserves its
existing dynamic marker rows. Both concrete bytes/string equations and their
distinct marker rows are checked. The theorem depends only on propext; it does
not prove compiler decoding, heap contents, source transport or backend adequacy.

Initial diagnostics exposed an unfinished pure/Except equality and wrong
memory-qualified parameter expectations. Explicit rfl and the actual normalized
bytes/string spellings fix these controls. Failed diagnostics/trials remain in
the off-Git evidence. Recovery MCP has zero errors19.331s; final per-file controls
and KeySort pass4.488s, child maximumRSS1,070,132KiB, cgrouppeak210,022,400bytes,
minimum outer available11,136,221,184bytes. Lean4.24/Lake5.0, serial12GiB/no-swap,
threads1/-j1 unchanged. No production imports changed; no full build or runtime
benchmark rerun was required. There is no pre-work equivalent checking time for
this new additive test; no performance or existing STOP recovery is claimed.

The hash-only dynamic-bytes-boundary-manifest.json records16payloads in the
off-Git H44 archive dynamic-bytes-boundary-c02a4db5d3f2f272.tar.gz,13,933bytes,
SHA256c02a4db5d3f2f272dcc01b46a2de80c2a71766cf4173be7f5e46c99e928ea01e.
Outer hash/size, exact regular member set and every member hash verify. Restore
payloads beneath artifacts/dynamic-bytes to replay the isolated test through
bounded.sh and gate.sh per-file. No generated library-root registration or
production API is added by this test module.

Independent read-only finder/skeptic confirmed marker/refusal/provenance limits
and found no blocker; neither used Lean/server/builds/writes. Dynamic bytes/string
implementation, parameter/storage handling, heap semantics, full H90 parity and
original migration/runtime/final acceptance obligations remain open.


### Historical environment intake and held dynamic-memory candidate

H77 delivered all eight wrapper/index/evidence/runtime/cache inputs for historical
sourceBuild4d7285. verify-environment-intake.py checks their exact outer SHA pins,
safe unique regular members, embedded index equality and every payload hash.
There are522evidence payloads,5runtime payloads and32cache payloads; each archive
also embeds its own separately counted index. Twenty wrapper-index entries match
their sealed executed-private payload bytes. Neither wrappers nor binaries run;
no cache is extracted, installed or adopted.

Native/WASM manifests contain the same343unique source-module rows and match
actual delivered binary bytes. This is consistency, not Git source verification.
The sealed box/diamond inventories have eight selected requests each plus one
mandatory proved harness guard. Exact saved request hashes and core result
objects match native/browser:16selected observations perbackend total8proved,
4refuted,4unsupported, plus2provedguards. The29saved gate receipts retain27exit0
and2exit1 records. The failed invariantCountsToBound request is bound to actual
WASM5a5be87b and retains Maximum call stack size exceeded with nonempty frame
indices. Those frames remain unmapped: old6ae symbols are not this binary's map.
No fresh execution, cause diagnosis, current-reader qualification or STOP release
follows. Original producer d8a141a7 evidence is a separate undelivered archive.

The H90 default-memory candidate passed per-file MCP and a serial capture gate:
strict bytes/string metadata to existing marker-bearing declMemory, initializers
and other locations refused. Two bare-declaration witnesses proved construction/
termination in both modalities; they do not observe empty contents or prove
source default-memory adequacy. Finder/skeptic requested that semantic limit stay
explicit and observable-content controls precede any such claim. The matched
78-file census stays245canonical/241both;17refusals change to String expected.
Six reader-profile refusals also change; no admission gain occurs in those sets.

Automatic approval review rejected proposed frozen verifier/audit expectation
updates because stripping the new decoder from comparison and capturing new
baselines could mask regressions. No rejected edit ran. Candidate source, exact
observations and failed/passing evidence are preserved off Git in the35-member
f7501b31521131172ae774afb006adcee546a90ea503b592ddfb0dfaa55b12ab archive
(630,918bytes), indexed by dynamic-memory-candidate-manifest.json. Production,
legacy controls and frozen observations are restored; no candidate admission is
integrated. Q-H90-DYNAMIC-VALIDATION is routed through coord-ask for a versioned
validation contract or deferral; the question branch is
coord-q/codex/solidity-directruntime-20261104/shared-translator/20261107T091354Z.

The restored nine-target/six-file decoder runner passes25.0735s under unchanged
12GiB/no-swap/threads1/-j1, child maximumRSS1,272,216KiB, cgrouppeak215,810,048bytes,
minimum outer available11,104,948,224bytes. An initial ancestry-check failure
pinned a subsequently advanced remote ref; it is retained and corrected to the
exact fetched/merged8a710f9d44df publication. No allowlist changes. Existing185
inputs, frozen78-file census and5,692reader observations verify unchanged.

Environment-intake-manifest.json pins the new report/tool and off-Git H44 evidence.
Independent read-only finder/skeptic confirmed mandatory guards, byte bindings,
actual stack error and the limits; neither used Lean/server/builds/writes. Full
source/importer migration, ReadBounds authority, runtime/performance repairs and
original final acceptance remain open.


### Exact original environment archive staged for courier

H70's missing-host-original notice was answered by checking actual local bytes.
The original environment-evidence.tar.zst still exists at 65,713 bytes, SHA256
d8a141a7703e95cc81f7aa0741ed12a5073739b1cb7d4363354211ca3cb16060.
Its committed environment-manifest.json is byte-identical to the manifest at
44d89439afd8fe7aca251cd5693b5b7ea36cf603, manifestSHA8ee027cf3c84e2162d98a07cf38e07706076be85948483e8a9d5e35cbeb5f6b5.
All 56 safe unique regular members and 55 internal checksums verify. Archived
Translate bytes equal that historical Git blob; compilation sourceSHA matches
the historical source; original ASTSHA4b57bac4 matches the separately delivered AST.
Nothing is extracted or executed.

A byte-identical copy is staged off Git under H44 at
artifacts/environment-handoff/original-environment-evidence.tar.zst.
Original-environment-staging.json records repository-relative paths and exact
provenance for the existing accepted H71 request. It is the original44d archive,
not native-browser c3c9ce43 evidence. Approved host pull, consumer delivery and
inspection remain unconfirmed; local staging is not transport or qualification.
No duplicate ticket, source push or cache shipment occurred.

Finder and skeptic independently checked custody/provenance limits and found no
blocker, without Lean/server/builds/writes. Publishedf5bfb9ba1 was already merged
before this metadata work; the explicit publication pin advances without any
allowlist change. No Lean/production source or frozen validation contract changes.
All performance/stack holds, production-owner authority, four storage diamonds,
Q-H90-DYNAMIC-VALIDATION and original full acceptance obligations remain open.


### Observable dynamic-reference model backfill

DynamicBytesModelControls.lean addresses the held candidate review's
bare-declaration limitation without installing that candidate or changing any
frozen expectation. Six existing intrinsic Raw-program cases run from explicit
State.init, fuel 128, in both constructed modalities: default bytes length0,
default string-to-bytes length0, their wrong-length1 assertions, and same-kind
empty alias reads. All 12 finite executions match: 8 normal and 4 assertion panics.
These observable length checks go beyond termination-only declarations. Empty
alias reads do not distinguish alias identity from copying. Finite execution
does not prove either modal formula or source/default-memory adequacy.

Four existing encodeCallArg checks admit same-marker bytes/string arguments and
refuse cross-marker arguments. Their contexts are supplied explicitly; this is
ABI argument compatibility testing, not declaration-to-context propagation,
assignment typing or ABI/source transport proof. The prior general marker-row
equation remains unchanged. No AST/compiler fixture or new translator is used.

Initial diagnostics caught a numeral helper declared Int rather than Nat and
Lean.Name constructors used where this repository's Solidity.Name is String.
Both corrections are local to the test; failed diagnostics are retained. Final
MCP reports zero errors in 9.5899 seconds. The final new-model/legacy-refusal/KeySort gate
and the checks for 185 inputs, 78 fixtures, 5,692 profile rows and static scope pass in 7.4837 seconds under unchanged
12GiB/no-swap/threads1/-j1. Child maximum RSS 1,082,720 KiB, cgroup peak 212,951,040 bytes,
minimum outer available 11,102,654,464 bytes. No pre-work equivalent exists for
this new additive test; no performance acceptance or STOP release is claimed.

Dynamic-bytes-model-manifest.json pins source/model inputs, exact observations
and the 15-member off-Git H44 evidence archive 32c5f7e8ed7e30ef68ec4103e76917c0bb2a187643af7664080b3a4e375718ce
(13,282 bytes). Outer size/hash, exact member set and all member hashes verify.
The model source input pins describe this bounded sample, not universal machine
closure. This isolated test adds no production root registration or public API.
Finder and skeptic read-only reviews found no checkpoint blocker; neither used
Lean/server/builds/writes.

Production source, interfaces, theorem statements, axioms, exclusions and budgets
remain unchanged. Dynamic admission and Q-H90-DYNAMIC-VALIDATION remain open;
this backfill does not authorize the previously rejected verifier/audit update.
Original courier, migration, stack/cost/startup, storage-diamond and final gates
remain separate dependencies.


### Candidate archive pin clarification

Published master e286f1843 was adopted by fast-forward before this metadata fix.
The candidate manifest now names its four source pins
`archivedCandidateSourceFiles`. Each entry has an explicit `archiveMember` and
`intendedRepositoryRelative` destination. The hashes identify the preserved draft
bytes, not accepted source or current checkout files. All four archive members
were rehashed against the unchanged sealed archive and member index. The archive
remains at SHA256 f7501b31521131172ae774afb006adcee546a90ea503b592ddfb0dfaa55b12ab.
No candidate was installed and no production, proof, validation contract or
resource budget changed. The test-standing-owner and static-handoff script notes
belong to the audit-calculus scope and were left unchanged in this lane.

### H126 ReadBounds compiled traversal repair

The typed tail worklist preserves every tree occurrence and existing fuel limit. Generic equalities prove exactly the old counters’ remaining-fuel results; the original ReadBounds definitions and statements are unchanged apart from selecting their compiled implementations. The correctness module stays outside the ordinary runtime import path.

The affected DirectRuntime build and 27 per-file checks pass. Matched checking of the existing module has median ratio 0.9265; this is not total cold-build or native performance acceptance. Earlier checking failures remain in the off-Git H44 evidence archive indexed by `read-bounds-stack-manifest.json`. Emitted C has a worklist back edge and no direct recursive worker call. Fresh native/WASM validation and all historical global performance STOPs remain open.
