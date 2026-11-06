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
