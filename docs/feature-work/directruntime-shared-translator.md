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
siblings retain their existing guards. New Scope/Compose registration is proposed
locally, without modifying shared roots.

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
