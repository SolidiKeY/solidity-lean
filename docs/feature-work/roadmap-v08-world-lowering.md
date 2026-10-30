# V08: callable, ABI and world lowering

This lane is **in progress**, not complete. The entire frozen
G20–G23 assignment and both backfill items remain open. This checkpoint
recovers the pinned checkout, traces published evidence and adds independent
intrinsic adapters plus source/intrinsic byte observation proofs and inhabited
controls. It adds no axiom, exclusion or replacement source semantics.

Current continuation inventory: **322** exact lane theorem/control pins in27
owned Lean modules. Source callable metadata, request/environment/transient
projections, selector/Keccak byte observations, emit-effect controls, payment
and declaration-role clauses are implemented below. Every G20–G23 parent remains
incomplete. The initial tables and counts are historical; continuation sections
record subsequent checked progress. Largest retained sampled aggregate RSS is
11715137536 bytes from passing focused TestSuite warm-up474104-a5109491;
its cgroup peak is11363561472bytes. This is not a passing full gate.

## Reproduction and setup

Base: `fb379ae20f10e2c92113453ddd9d40d8f2efbe09`.
Branch: `codex/solidity-v07-v11-20261030/v08-world-lowering`.
Checkout: `/workspace/v08-world-lowering-pinned`.
Original checkout `/workspace/solidity-lean` stays on `work` at
`204eb1545cbf57e436196e4cba346075515b7279`; `bridge-theorems` is preserved.
The exact-SHA fetch from the existing GitHub origin succeeded, and its original
checkout FETCH_HEAD equals the base. A separate worktree was created from it.
FETCH_HEAD is worktree-local: querying it in the new worktree fails; the raw
failed query is retained, alongside verification in the original checkout.

Installed tools were discovered below `/workspace/.setup/tools` rather than
in PATH: Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613 (Lean 4.24.0). The declared toolchain agrees.
No Lean MCP diagnostics or get_goal tool is exposed. No second goal was created.
The cloud runtime skill and its networking guidance were read; identity matches
the attached executor and network policy is enforced. No permissions were
broadened and no proxy or credential configuration was changed.

Both user and system systemd scope probes fail (no user scope bus; systemd is
not PID 1). Creating a dedicated cgroup fails with Permission denied even through
the permitted command escalation. The current cgroup has memory.max=17179869184
and memory.swap.max=max. The observed swap device list is empty, but this does
not supply the required enforceable 12 GiB/no-swap scope. The finder required testing the supported Docker route. A network-isolated
Docker container succeeds with memory.max=12884901888 and memory.swap.max=0.
The mandatory KeySort build then passes with LEAN_NUM_THREADS=1 and -j1 in
a session-specific alternate TOML: Built Solidity.KeySort (1.9s), Build
completed successfully (2 jobs), exit 0. Cgroup peak is 139890688 bytes.
RUNTIME_GATE_PASS is established for this recovered setup; the passing owned 59-module closure (60 Lake jobs) subsequently records 851103744 bytes
sampled aggregate RSS and 255733760 bytes cgroup peak. Failed development
checks are retained; at this historical initial checkpoint the largest sampled RSS was 2399289344 bytes during
a failed conversion-heavy control proof. No proof budget was raised. The
word-stream proof now transports encoder equality through function
extensionality; delegated controls group observation fields and use an empty
paid prefix to stay within the original budget. Broader full gates remain open.

## Concrete gap traced to the pinned source

The [coverage plan](../coverage-plan.md) requires callable and world source
lowering, not just intrinsic execution examples. Manifest localEvidence and
G03 cover entries were traced read-only:

- `publicGetters`: localEvidence names
  `Solidity/Frontend/SolcJson/Getters.lean`, the PublicGetters examples and their
  script. The actual `publicGetterPlan` consumes keys/indexes and selects
  terminal fields; `publicGetterIdentity` validates compiler selectors or
  reconstructs the exact signature. These are importer definitions, not a proof
  relating independent source execution to typed calls. Getter integration,
  reference returns and function-reference arguments remain with their owners.
- `abiDecode`: localEvidence names `Solidity/Syntax/Elab.lean` and ABI examples;
  G03 points more precisely to `Solidity/Syntax/Elab/Lower.lean` and
  `abiDecodeWith`. Its arguments are elaboration functions and it produces an
  elaboration result; it is not a source observation transport theorem.
  Lazy/noncanonical decoding stays reserved. No decoder is added here.
- `libraries`: localEvidence points to the contract importer. G03 additionally
  points to `Solidity/Semantics/ContractWorld.lean` and
  `Solidity/Semantics/ContractWorldCertificates.lean`. `World.libraryCall`
  runs a supplied body in caller storage after runtime role/static and installed-code identity checks;
  `Operation.libraryCall_certificate` erases the result of that same intrinsic
  call. This certifies its world API, not source execution preservation.
- `transientState`: localEvidence includes
  `Solidity/Semantics/TransientWorld.lean`. `World.transact_failure` assumes
  actual frame failure at the reset input and proves restoration of that input
  with the exact halt. `World.transact_commit` assumes actual success and keeps
  the returned world with reset. These published laws are useful backfill
  inputs, not evidence of source-to-intrinsic composition.

`Solidity/Source/World.lean` independently defines accounts, transient cells,
journals, frame rollback, transfers and endTx. Its rollback laws are about
source-state operations. `Solidity/Source/Observe.lean` defines source bytes,
selectors and revert observations independently of the compiler. No inspected
API supplies a completed source execution application or V07 certificate to
close this lane. This audit does not claim to classify all source files.

## Queue and prerequisite accounting

| Item | Status | Remaining obligations |
|---|---|---|
| G20 | Open | All independent callable adapters/proofs, signature/getter/receive/fallback/inheritance/library transport, witnesses and controls; apply reserved getter/function-reference/readonly results only when published |
| G21 | Open | Nested ABI/reference/slice/error/reason/panic/catch observation transport; retain exact failure bytes; consume reserved decoder laws only when published |
| G22.01 | Open | Typed external/self call transport and source-order failures |
| G22.02 | Open | Callback/reentrancy transport and permitted environment execution |
| G22.03 | Open | Creation/try-new installation/rollback and constructor combinations |
| G22.04 | Open | Library/function-value context transport |
| G22.05 | Open | World composition with funded entry and nonzero payments |
| G23 | Open | Transient sharing/reset/rollback, approved environment/crypto observations, emit argument effects; source-unit composition requires G16–G22 |
| Backfill A | Open | Strengthened nested rollback/snapshot/observation laws; funded/callback positives and wrong-payload/wrong-frame negatives |
| Backfill B | Open | Signature/ABI observation extension, repeated calls/transient composition and constructor-combination witnesses |

V04 independent source execution, partial V05/V06 and V07 applications remain
explicit prerequisites. No unpublished V07–V11 branch is imported. Existing
Evm, Bridge, Source, scalar/store representation/environment/failure/creation,
ABI/function-reference and other reserved work is untouched. G15 admission and
runtime frame/bytecode premises are not supplied by this checkpoint. Parameterized
certificates will not discharge those missing applications. No parent group or
lane status should be promoted by the coordinator.

## Validation and handoff

Evidence directory: `/workspace/v08-world-lowering-evidence`.
Baseline layer check passes: 169 core modules, 0 reach the elaborator.
Baseline orphan check passes: 866 reachable, 0 orphaned, 0 not allowed.
The exact-base full doc-path check fails with 46 missing references; raw output
is preserved in base-doc-paths.log. These failures are not relabeled green.
Post-edit comparison and independent finder/skeptic review are recorded in the
external handoff before committing this documentation checkpoint.

All proof budgets, intrinsic representations, source independence, observations,
Fml.inTarget and verdicts remain unchanged. No external compiler/EVM tests were
run, and no such test is presented as a kernel proof. Full validation remains pending implementation and its gates. Exact feature IDs for coordinator reconciliation are
saved in feature-ids.json; no G03 ledger or global coverage status was edited.

## Recovery review findings

Independent read-only finder and skeptic reviews used neither Lean server nor
builds. Finder required testing Docker before declaring an external cap blocker;
that test succeeded and the provisional blocker was removed. Skeptic required
qualifying runtime library identity checks (source resolution and storage mapping
remain obligations), and separating the failed worktree-local FETCH_HEAD probe
from the successful original-checkout verification. Both corrections are applied.
Neither review certifies future implementation.

## Independent proof checkpoint

The owned modules are registered append-only. All 50 initial-checkpoint named theorems
have exact lane-local axiom sets in scripts/v08-axiom-pins.json; Audit prints
all headline laws and controls print their inhabited witnesses. The allowed
sets contain only propext, Classical.choice and Quot.sound. These are kernel
proofs; no compiler/EVM differential test has been run by this lane.

Theorem names below are in Solidity.Lowering.V08 unless qualified otherwise.

| Laws | Exact application premises and limits |
|---|---|
| beBytes_layout, wordBytes_transport, pad32_transport, wordSequence_transport | Arbitrary byte length/natural number, intrinsically bounded Roadmap.Word, bytes or word lists respectively; independent source encoder compared with existing intrinsic encoder |
| panicData_transport, panic_payload_injective | Any published Source.PanicCode; injectivity assumes equality of encoded bytes and concludes equality of codes |
| errorData_transport, catch_error_transport | Explicit bytes.length < 2^256; catch law proves the same decoder result, not a general successful roundtrip |
| callFrame_observeEntry, call_observeEntry, call_observeEntry_error_iff, call_observeEntry_comp | Supplied typed Entry/body/result decoder, actual World/Handle/Context, DecidableEq catalog keys and arbitrary result observations; no source body/signature-resolution certificate |
| resetTransient_idem, transact_congr, transact_observe | Existing typed World and frame; congr requires equal actual results at the reset input; observations preserve snapshot and exact halt |
| transact_descendant_failure | Actual first-frame success at reset input and actual later failure at that returned world/value |
| transact_repeat | First actual success at reset input, second actual success at the first committed reset world; proves two-boundary composition |
| transact_wrong_halt, rollback_observation | Actual failure at reset input; wrong-halt additionally requires actual halt differs from proposed halt |
| transact_atomic_descendant | Actual prefix success, inner failure and actual continuation success at the atomic snapshot/status; ANY THalt may be passed to the supplied tail, so this is not a Solidity-catchability theorem |
| libraryCall_observe | Supplied linked identity and caller-typed body; existing role/static/code checks and caller storage/context retained; source declaration linkage/storage mapping absent |
| tryCreate_observe | Supplied args, target, constructor, context and both continuations; maps both result observations without moving catch boundaries |
| tryCreate_success_continuation_failure | Nonstatic context, actual successful constructor and actual failing success continuation; exact continuation halt remains uncaught |

Controls prove funded calls (100 -> 93 sender, 0 -> 7 receiver), exact return
and failure bytes, a nonidentity length observation, failed decoder payload,
ancestor rollback and wrong-frame rejection, two transaction resets, failing
nonempty constructor catches at the post-payment snapshot, successful nonempty
constructor installation, delegated owner isolation and no duplicate payment,
and exact reason/panic catches with malformed/wrong-code negatives.
These finite witnesses impose no semantic call-expansion bound. The additional
callback witness below supplies a published invariant/havoc callback outcome;
arbitrary source callback/reentrancy execution remains open.

## Historical initial-checkpoint queue status

All parent groups remain incomplete. The earlier queue table lists the full
frozen requirements; the following records only checked progress.

| Item | Checked progress | Remaining blocker/application |
|---|---|---|
| G20 | Typed result/observation extension and composition, exact decoder failures | Source argument/signature/body selection; all getter, receive/fallback, overload, inherited and function-value applications; reserved getter/function-reference/readonly owners |
| G21 | Independent word streams, panic and total reason-byte agreement; positive/negative existing-decoder controls | Nested/reference/slice/custom-error and complete panic/catch source applications; reserved lazy/noncanonical decoder |
| G22.01 | Actual typed call frame/result transport and nonzero funded witnesses | Independent external/self source execution and frame application |
| G22.02 | Generic snapshot/atomic/ancestor failure laws and an inhabited funded invariant/havoc callback | Arbitrary source callbacks/reentrancy and runtime/source relation application; no replacement callback interpreter is introduced |
| G22.03 | Creation continuation transport and successful/failing nonempty constructor combinations | Source new/try-new execution, constructor identity/argument evaluation and installation application |
| G22.04 | Runtime linked caller-context observation law and inhabited owner control | Source declaration linkage, function-value context and storage-parameter mapping |
| G22.05 | Paid, rollback, library and constructor combination controls | Composition of actual G22.01–.04 source relations, admission and runtime premises |
| G23 | Intrinsic full reset/snapshot and repeated-transaction composition | Source transient relation; approved environment/crypto and emit-argument effects; G16–G22 source-unit certificate applications |
| Backfill A | Nested atomic snapshot, ancestor rollback and observation laws; funded/callback positives, wrong-payload/wrong-frame negatives | Source/world lowering applications remain open; the intrinsic callback control below is proved, not declared unavailable |
| Backfill B | Result/ABI observation extension, word-stream agreement, repeated reset and constructor combinations | Signature/ABI applications for full source callable metadata and V07/source execution certificates |

The exact base contains no Solidity/Lowering modules and Source has state,
observations and static relations rather than the required complete S02–S05
execution application. The published world API itself documents fixed supplied
bodies/response tables rather than certification of arbitrary source reentrancy.
Neither its API certificates nor this lane's adapter laws discharge those
prerequisites. No owner is unreserved by this checkpoint. Every reserved owner
listed in the frozen assignment remains reserved, including byte memory/control,
Widths, reference/memory loops/copies, getter/function-reference/readonly calls,
backend scalar/store/environment/failure/creation, hashes/precompiles/stipend,
source/static and roadmap controls/interfaces. Prerequisite revision is the
exact base only; no unpublished revision is consumed.

## Validation continuation

The full bounded gate is being compared with a detached exact-base worktree at
/workspace/v08-baseline-pinned. An initial baseline attempt was intentionally
stopped (exit 137) before executable targets, to ensure explicit -j1 also covers
those targets. Its raw log is preserved, not counted as a pass. The runtime
runner now places -j1 in every library/executable's weak arguments, without
changing the tracked lakefile or proof/test budgets.

The original run-lean.sh invokes check-solkey.sh, whose generated-executable
refresh deletes a file. The user's recovery instruction forbids deleting files.
The bounded full control therefore executes the layer/build/TestSuite/sort-check
coverage without that deletion; the exact original script is not claimed run.
No final gate or lane completion is claimed while full results are pending.
The first root alternate TOML from runtime recovery remains an untracked,
known generated control (lakefile.v08-runtime.toml); it is preserved and is not
part of the patch. The reproducible committed control is scripts/v08-runtime.toml.

## Funded callback backfill and final review corrections

Both final reviewers rejected the earlier inference that absent arbitrary source
callback semantics made a concrete intrinsic callback example unavailable. The
new CallbackControls module constructs the published ExecS.transferResume and
ExecP relations with the closed invariant True and pay=true. This is an
invariant/havoc outcome, not execution of a concrete source callback body and
not an equation with deterministic World.call.

callback_transfer and callback_program retain the actual transfer-output net
ledger and self balance. callback_committed constructs an existential witness
linking installed storage, actual paid World.enter (value 7), that ExecP,
actual World.finish and the concrete observations sender=93, self=4,
recipient=3, saved=5 and transient scratch=0 after normalization. The positive
witness has no hypotheses. The supplied before/getD fallback cannot hide a
failed deployment/entry/settlement: installed storage, exact entry, callback
run and successful settlement are all proved. callback_after_failure binds
that same verified settlement before revertWith [0xfa,0x11], then proves the
raw atomic snapshot sender=100/self=0/store=0; callback_wrong_frame rejects
the successful callback snapshot for this ancestor failure.

The successful 85-module owned closure is recorded in v08-gate-52413.log/json:
exit 0, 816951296 bytes peak sampled aggregate RSS, 199753728 bytes cgroup peak.
That run prints the then-current 46 theorem/control axiom sets, including the previously omitted
pad32_transport (no axioms). Earlier 40-pin claims were incomplete and are
superseded by this checked inventory. The log is bound to before/after SHA256
of all tracked/untracked Lean files and the effective runtime configuration;
the checker rejects changed source, changed inventory or changed log bytes.
It checks tracked and untracked scope, including an exact-content exception
for the preserved initial generated root TOML.

Separate independent read-only finder and skeptic reviews inspected actual
source/diffs, hypotheses, witness nonvacuity, ownership and controls; neither
used a Lean server or build. Confirmed findings fixed: supported Docker route;
precise library identity wording; worktree-local FETCH_HEAD failure accounting;
resource-stop/zero-sample false-green paths; explicit target rejection and time
limit; same-decoder-result wording; actual observation-extension/decoder-failure
controls; two transaction boundaries; exact padding pin; untracked-scope and
stale-log checks; accurate atomic/catch distinction; concrete callback backfill.
The delegated fixture uses an empty paid prefix but retains the nonzero payment,
changed caller store, unaffected second owner and nonidentity return observation.
No proof/fuel/node/time budget was increased to obtain these results.

The corrected exact-base full gate reached its 600-second supervisory limit:
exit 125, guard stop, 2168741888 bytes peak sampled aggregate RSS. Raw evidence
is v08-gate-30261.log/json. This is incomplete validation, not a passing build
or an inherited-proof-error waiver. The patched full attempt is recorded below; it also remains incomplete.
The global source profile/prerequisite applications and the original final
completion gate remain open regardless of the passing local component proofs.

## Total ABI observation strengthening

beBytes_mod proves arbitrary byte-width truncation leaves the source encoding
unchanged; natWordBytes_transport derives agreement for any natural number.
errorData_transport_total and catch_error_transport_total then remove the
reason-list length premise entirely. The old bounded lemmas remain unchanged;
the total laws add no admission bound, emitter or decoder. The catch law still
proves equal decoder outputs, not a universal successful roundtrip for lists
longer than the represented ABI length. Independent finder and skeptic reviews
confirmed these exact statements and source independence without a Lean build.

The source-bound 85-module gate v08-gate-58133.log/json passes with all 50
current theorem/control axiom sets: sampled aggregate RSS 787935232 bytes,
cgroup peak 207249408 bytes. Source/config SHA256 remained unchanged.
The lane checker initially rejected the inherited AST import of built-in Lean;
that was a false-positive against the actual repository layer policy. The
control now checks the repository's source elaborator/printer boundary, while
preserving AST and the dependency-free package. Its raw failed check is retained.
The explicit layer command and orphan/trust checks pass; the global pin checker
currently reports 14 unrecorded Evm.StorageSlots pins outside V08. Its full
failure is retained and compared separately with the exact base; no global pin
inventory or reserved StorageSlots source is edited.

The external evidence checker has adversarial controls for stale source, a
missing source entry, a changed log, a guard stop, zero RSS samples and changes
during a build. These Python tests do not constitute kernel proofs or EVM tests.

## Committed checkpoint handoff

This is a partial implementation checkpoint on the frozen base and assigned
branch recorded above. The exact resulting committed head, original patch,
bundle and checksum manifest are recorded in the external handoff at
/workspace/v08-world-lowering-artifacts/handoff.md. No parent group is complete.

The patched serial full attempt, python3 scripts/v08-bounded.py --full,
v08-gate-64122.log/json, also reaches the 600-second supervisory cap: exit125,
guard stop, source unchanged, 3553173504 bytes peak sampled aggregate RSS.
Cgroup peak was unavailable after stop. This is incomplete import-closure/full
validation; default-build/TestSuite/sort suffixes were not reached. It does not
prove a source error or that the exact base fails to build. The exact-base
attempt30261 likewise stopped at600 seconds; neither is waived as green.

The repository final script itself remains unexecuted because check-solkey.sh
deletes the generated executable, contrary to the recovery no-delete rule.
The separate passing lake exe conformance does not establish that executable
refresh step. No test/time/proof budget is increased to finish the gate.

Final read-only finder/skeptic review confirmed all50 theorem names/pins and
identified one trailing blank line in the generated runtime TOML. The generator
and tracked control are normalized together; refreshed source-bound closure
and whitespace results are retained in the final handoff. Neither reviewer
used Lean/server/builds. They confirmed that signature/argument metadata, nested
ABI/reference/slice/custom-error, environment/crypto and erased-emit effects
remain unimplemented, distinct from unavailable source/V07 composition. This
checkpoint does not assert that all conceivable independent work is exhausted.
The whole original queue remains frozen and incomplete, with checked progress
as tabulated above. No scope answer or exclusion has been inferred.

After normalization, the refreshed 85-module source-bound gate
v08-gate-84788.log/json passes (cached replay,86 Lake jobs), all50 exact axiom sets,
source/config unchanged: sampled RSS58781696 and cgroup peak31449088bytes.
The earlier58133 gate remains the original checked source evidence.

Final artifact review corrected terminology: the focused closure contains85
named modules, reported by Lake as86 jobs; the earlier closure contained59
modules/60jobs. Evidence JSON module lists are authoritative. The implementation
checkpoint is967952d5964db81a77d4fd948028707f51e4a607. The follow-up changes only
this handoff precision; no proof or effective runtime option changes. The
external handoff records the final documentation commit as well.

## Continuation checkpoint: source callable metadata

Continued from12f1216519b774676dd36032494f5043fd0e352d in the same pinned
worktree. No goal/receipt was recreated or reset; get_goal is still not exposed.
The original queues remain binding. Source.Resolved.paramsOf handles event/error
parameter lists, while functions use Decl.fnSig. CallableMetadata now consumes
these actual APIs. It adds no evaluator, type representation or value/state layer.

convertedArgs exposes the explicit conversion nodes in RConvArgs as RArgs.
convert_originTypes proves RArgs.convert retains the full original expression
type spine in order, with no source caps or conversion-preservation assumption.
argsFit_length proves exact arity. paramsOf_unique fixes the selected event/error
parameter list; function_signature_unique fixes both parameter and result lists.
namesMatch checks source declaration labels against reversed actual Args.names;
sourceLabel distinguishes user labels from generated anonymous labels without
relying on configurable printer spelling. namesMatch_iff, target_names_length
and matched_names_length establish the precise names/arity contract, including
primitive/storage/memory argument slots. Names alone do not prove type/body
agreement, unique declaration identity or preservation.

MetadataControls supplies a nonempty two-boolean source function, a resolved
RExpr.call, explicit ordered conversion nodes, actual target Args.evalT with
distinct true/false values, and negative swapped-name/value-order/result-signature
controls. A heterogeneous custom-error declaration consumes paramsOf and retains
the rational argument's conversion to uint8; reversed types fail argsFit. This
is not custom-error emission or a source evaluation theorem. The17 new named
laws/controls pass gate100235 (55 named modules/56 Lake jobs); prior50 remain
unchanged. All67 exact axiom sets are lane-pinned. Final combined gate follows.

Exact missing interfaces: this pin supplies no general checked STy-to-intrinsic
parameter/result representation map or RExpr source execution application;
reserved getter/function-reference/readonly owners remain untouched.
Source.TypingExamples explicitly defers slices to S02, RExpr has no slice
constructor, and Source.Calldata.objects has no fixed decoder relation to input.
A new nested ABI encoder/decoder or invented slice semantics would bypass the
reserved decoder/source owners, so none is introduced. These identified gaps
do not stop other independent environment/transient and rollback backfill.

Full-gate diagnosis: gate64122 scheduled870 named modules via873 Lake processes
but completed216 build invocations before the600-second guard. Several cold
calculus targets took13--24 seconds each; prior logs/caches are retained. Before
another unchanged full attempt, use focused import closures to reuse this
source/toolchain-keyed cache. The cap, proof/fuel/node/TestSuite budgets and
12GiB/no-swap/OS-headroom guards remain unchanged. New Lean checks are serial;
no Lean MCP diagnostics are exposed.

Metadata checkpoint review findings: finder and skeptic required explicit
fixture-environment provenance. MetadataControls now places the function and
error in one actual abstract source unit and proves both declaration-membership
witnesses. These do not prove overload resolution, WellFormed admission or
Typed.toR provenance, which remain open. The finder also required documenting
that sourceLabel maps every generated label to none: anonymous/repeated-label
permutations are not distinguished by this names-only observation. The exact
target value-order negative remains independent of label equality. Neither
reviewer used Lean/server/builds; their read-only review did not close source
execution/type-representation premises.

The reviewed membership extension adds two no-axiom witnesses, so this
checkpoint has19 new named declarations and the combined inventory69. Focused
gate106681 passes55 named modules/56 Lake jobs, source unchanged; sampled
aggregate RSS791875584bytes, cgroup peak188837888bytes. Final combined
source-bound evidence and checkpoint review record are saved alongside the
original logs, with raw historical failures retained.

Metadata checkpoint handoff: combined gate107408 passes92 named modules/93
Lake jobs, all69 exact axiom sets, unchanged source/config, sampled aggregate
RSS810668032bytes/cgroup peak172089344bytes. Separate independent finder and
skeptic confirmed both fixes on actual source, without Lean/server/builds.
Final lane control/negative evidence, layers/orphans/trust and doc comparison
are retained under metadata-* logs. Documentation full exit1/46 remains a
failure; zero-new comparison is separate. Full final validation and all source
composition obligations remain open; this checkpoint is not a lane endpoint.
Checkpoint parent12f1216519b774676dd36032494f5043fd0e352d; frozen base unchanged.
The committed checkpoint head and patch are recorded at
/workspace/v08-world-lowering-artifacts/metadata-checkpoint.md and .patch.
Next independent work is the G23 source/world environment projection adapter
and populated mixed source/intrinsic rollback observations, followed by other
authorized independent clauses.

## Continuation checkpoint: request, session and mixed-frame observations

Parent implementation afe2a93f0387fda7c4de008eb013f4be2c04f8a7.
EnvironmentProjection adds total liftWord/lowerWord and liftAddress/lowerAddress
bijections at the published bounded source/intrinsic types, including zero and
maxima. No representation/profile exclusion or budget increase is added.
request_tx retains the G01 sender/value/time/target and supplied response table
in the actual typed Context.tx; expression_observations proves the actual five
typed environment reads of the projected state. stateEnvironment preserves the
supplied storage/heap/locals/net and replaces only request fields/observed balance.
This is a field projection, not a source evaluator or paid-frame admission proof.

fundsOf/withSourceFunds project source instance-account fields structurally;
they are NOT universal external-account balance semantics. Finder and skeptic
identified that Source.World reserves external balances for G01 SessionEnv and
Fixed.ledger. sessionFunds now chooses installed source balances or the actual
supplied Fixed.ledger/environment.balance/history at code-less addresses, with
separate session_funds_installed/session_funds_external/session_funds_endTx
laws. Installation/domain agreement, constructor-phase handling and the
canonical G03 ledger application remain explicit prerequisites. No replacement
ledger is implemented. Controls reuse existing G07 toyFixed solely as a fixture,
not the canonical ledger: installed balance7 defeats ledger41, while external
ledger41 defeats the default source account0.

reset_funds_projection/state_environment_reset commute published source endTx
and intrinsic reset/transactionEntry with these projections. source_rollback_funds
and source_outer_rollback_funds transport observations through actual arbitrary
source journal runs, including committed descendants; no source-target execution
correspondence or history rollback premise is hidden in them.

ProjectionControls runs two real source instance transfers (7 and2), then
persistent/transient writes, through the existing source journal. Both source
accounts are explicitly installed fixture instances (code1/code0); these are
journal-state controls, not a proved admitted source session. Source payment
success is checked, so getD fallbacks cannot make the witness vacuous. Actual
typed target calls both succeed and reach dirty91/9/5/17, inner failure restores
93/7/3/9 with exact nonempty reason bytes, and outer failure restores100/0/0/0.
The target child uses the actual same outer input world. Independent observations
agree for this populated case. Both actual boundaries produce93/7/3/0; wrong
inner-frame/reason/stale-transient controls distinguish failures. No general
source storage layout/type relation or source RExpr/RStmt execution is supplied.

The36 new generic laws/controls pass gate118536 (58 named modules/59 Lake jobs),
unchanged source/config, sampled aggregate RSS871882752bytes/cgroup256712704bytes.
All105 named declarations are lane-pinned. Finder/skeptic actual-source reviews
use neither Lean/server nor builds. Their boundary-admission wording finding is
fixed: the boundary theorem proves roundtrips, not an admission predicate.
Final combined closure and checkpoint handoff follow before the next work item.

G23 still needs source expression/statement applications, approved crypto
observation applications and erased-emit argument execution; G16--G22 source
composition is unavailable. Read-only trace: Syntax.Grammar.solEmit translates
to RawStmt.eval of the operands; Syntax.Elab.Arms hoists eval operands via
eagerArgsWith and erases only their residual values. SolcJson.Body preserves
positional emit operands and refuses named emits without pipeline-aware context.
These definitions are not preservation proofs. No named-argument exclusion or
source semantics is invented to close that gap.

Projection checkpoint handoff: combined gate119445 passes96 named modules/97
Lake jobs and all105 exact axiom sets, unchanged source/config. Sampled aggregate
RSS812957696bytes/cgroup172580864bytes. Both independent read-only reviewers
confirmed the installed/external ledger fixes and nonvacuity, with no further
mathematical or ownership finding. stateEnvironment still reads a structural
source-instance target balance; it does not use sessionFunds for arbitrary
code-less targets or prove admitted/request execution. Its actual-expression
read theorem remains exactly a projection law. Canonical ledger, constructor
phases, source storage/statement semantics and G16--G22 applications remain open.
This component checkpoint is not a full-lane endpoint. Parent
afe2a93f0387fda7c4de008eb013f4be2c04f8a7; frozen base unchanged. Final committed
head/patch are saved at /workspace/v08-world-lowering-artifacts/projection-checkpoint.md
and .patch. Next independent work is erased-emit effects/selector observation
controls, followed by bounded cache warming and required final validation.

## Continuation checkpoint: signature bytes and erased-emit arguments

Parent961ec71a659e0c4ba7522ddab191a96f24b8b90b. SelectorObservations proves
beBytes_split/beBytes_take for arbitrary high/low byte observations, then
selectorBytes_layout/selectorBytes_ofNat for the existing UInt32 selector
format, including truncation above32 bits. signature_selector relates the
independent Source.selector to actual Semantics.selectorBytes(customSelector)
for every supplied signature string. No raw-hash bound, injectivity/collision
premise, new crypto implementation, emitter or decoder is used.
signature_arguments composes those exact observations with existing typed ABI
word streams in supplied order. Canonical string derivation from source
declarations and full nested/reference ABI lowering remain open applications.

SelectorControls proves literal UTF-8 input vectors, actual standard Error
selector bytes, distinct Error/Panic signatures and distinguishable argument
word order after any selector prefix. Plain kernel conversion was stuck at
ByteArray.toList's well-founded recursion; recursive simp hit the unchanged
recursion limit. Applying one published loop equation at a time with explicit
literal size proofs succeeds. The controls use kernel proofs only; no axiom,
native_decide, implemented_by shortcut or proof/resource budget increase.
Failed development logs are retained, not presented as accepted proofs.

EmitControls consumes the actual solEmit/RawStmt.eval elaboration and existing
withPanics wrapper in typed Entry bodies. Source event E with two parameters
and E3 with three have actual source-unit membership witnesses, and resolved
RStmt.emit/RConvArgs fixtures retain assignment/read expressions explicitly.
The target entries declare the statement bodies' typed local slots (two uint
locals or one), rather than erasing them to force an empty context.

Noncommuting arguments saved=saved+1 then saved=saved*10 yield10 in an actual
nonzero paid call, defeating dropped-effects0/reversed-effects1 controls. A
three-argument E3 first assigns saved2 before10/saved, then writes scratch9;
its actual call succeeds. Moving the divide earlier yields exact Panic0x12
and rolls back payment/storage; Panic0x11 is rejected. The matching three-arg
source event/statement fixtures were added after independent finder/skeptic
identified a two-versus-three-parameter mismatch. These are source-tree and
actual target lowering regressions, NOT a proof of independent RStmt execution
preservation. Source WellFormed/name resolution/Typed.toR/body-lowering and
source effect-order semantics applications remain prerequisites.

Clean focused gate131876 passes the then-current three modules (21 new named laws/
controls; all126 lane declarations pinned), unchanged source/config, sampled
aggregate RSS881311744bytes/cgroup245563392bytes. Original actual selector
computation130398 took17.38s, sampledRSS1906442240bytes, within all original
budgets. Separate independent actual-source finder/skeptic reviews used no
Lean/server/build; their confirmed fixture finding is fixed and rechecked.
Final combined source-bound gate and checkpoint handoff follow.

Final emit fixture review also found the source scratch state-variable flag
was persistent while the target field is transient. It is corrected to true
in the published source syntax constructor, with source membership/conversion
fixtures rechecked. This is provenance fidelity, not a replacement source
state/statement execution theorem; no general layout premise is discharged.

Selector/emit checkpoint handoff: the final source-bound refresh133794 includes
the corrected transient flag and passes99 named modules/100 Lake jobs, all126
exact axiom sets; unchanged source/config, sampledRSS875573248bytes and
cgroup247820288bytes. This supersedes131876/132718 as current-source evidence.
Both independent finder/skeptic reviewers confirmed the matching E/E3 source
arity and transient flag on actual source, no Lean/server/builds. Static gates
and raw documentation failure/zero-new comparison are retained as selector-*.
No source signature derivation, independent source effect execution, general
ABI/reference lowering or full source-unit composition is claimed. Parent
961ec71a659e0c4ba7522ddab191a96f24b8b90b; frozen base unchanged. Exact committed
head/patch: /workspace/v08-world-lowering-artifacts/selector-emit-checkpoint.md
and .patch. Next independent work investigates the published Keccak byte-output
bound needed to transport fixed source crypto observations; no hash implementation
or precompile/backend owner work will be duplicated. Full validation follows
substantive component work with the original600-second/process/proof limits.

## Continuation checkpoint: fixed Keccak observations

Parent56db11be40e0f37edb8314c328ded74504dcc824. CryptoObservations proves a
general fold_byte_bound/ofBytes_bound, then keccak_length_bound (at most four
published lanes of eight bytes), keccak_bytes_bound (existing modulo256 output)
and keccak_word_bound for the actual Keccak.keccak256Nat, without input length,
lane-value, output-bound or collision assumptions. It reads existing hash
definitions without editing/reimplementing Hash/Keccak/precompile/backend code.
byte_input_normalize preserves every input UInt8 through existing intrinsic
Int-to-byte normalization. fixed_keccak_observation consumes the published
Fixed.Keccak pin and proves fixed.hash agrees exactly with keccakBytes;
fixed_keccak_bytes transports the actual result's complete ABI word bytes.
The raw bound is proved, not made a hidden preservation premise. The existing
pin's Sane and fixed-hash contract remain its supplied G01 prerequisites.

CryptoControls applies the checked existing G07 toyFixed_keccak witness to
nonempty binary00/ff/80, checks the actual standard empty-input hash, and
distinguishes a changed input byte and wrong zero result by kernel proofs.
Only the published real Keccak pin of toyFixed is used: its ledger/precompile
mocks do NOT certify G03/G06 production integration or other approved crypto.
No source expression execution or general memory/call lowering is inferred.

Focused gate140654 passes43 named modules/44 Lake jobs, all12 new laws/controls,
unchanged source/config, sampledRSS2101518336bytes/cgroup1568354304bytes in24.8s.
All138 current named declarations are lane-pinned. Hash/output proofs elaborate
within default budgets; no native_decide/axiom/implemented_by shortcut is added.
Remaining crypto applications: actual Source.RExpr execution; G06 published
precompile/observation laws for SHA/RIPEMD/ecrecover and their admissible calling
contexts, plus general memory-byte relations owned by their existing workers.
Neither a source crypto evaluator nor another precompile implementation is
introduced to fill those dependencies. Independent finder/skeptic actual-source
review and combined closure finish this component checkpoint.

Crypto checkpoint handoff: combined141811 passes101 named modules/102 Lake
jobs, all138 exact axiom sets, unchanged source/config; sampledRSS818151424
bytes/cgroup177311744bytes. Separate independent finder/skeptic actual-source
reviews found no theorem, nonvacuity or ownership defect, using no Lean/server/
builds. They confirmed that the raw bound is derived, the G01 Keccak pin is
explicit, toyFixed is used solely for its real hash pin, and no other crypto/
precompile/source execution claim follows. Static/raw doc comparison logs are
crypto-*; source/profile/composition and final full gates remain open.
Parent56db11be40e0f37edb8314c328ded74504dcc824; exact checkpoint committed head
and patch are saved at /workspace/v08-world-lowering-artifacts/crypto-checkpoint.md
and .patch. Next independent G20 work consumes callable payable/receive/fallback
metadata before final cache-warmed validation; no reserved body/getter/function
reference or readonly implementation is taken over.

## Continuation checkpoint: callable payment and declaration roles

Parent395ea6818f11bc0af0738a9596a6992635601a44. PayableMetadata reads actual
Source function/fallback mutability and receive flags, consuming existing
Decl.receiveOK refusal. attach? sets ONLY the supplied Entry.payable; its actual
body, typed locals and decoder remain. Constructors/non-callable declarations
do not manufacture ordinary entries. Source constructor/creation integration
stays separate. attach_of_flag/attach_none state the exact partial adapter.

nonpayable_enter proves the existing guard's exact revert on every nonzero
payment. payable_enter_success proves actual header success from numeric
funding, nonstatic context and bounded receiver-sum checks, not from a desired
execution hypothesis. source_nonpayable_rejected/source_payable_entered compose
those guards with the actual source metadata result. No source body/exposure,
readonly or placement/admission certificate is inferred. Ordinary-entry guards
do NOT describe rejection of ambient msg.value inside Stmt.call; readsValue
for internal/private functions is explicitly distinct from payability.

PayableControls has source receive-unit membership, positive payable function/
fallback/receive flags, malformed receive/noncallable/constructor refusals,
actual funded7 receipt with supplied writes, exact nonpayable rejection,
zero-payment successful effects and a wrong erased-payment negative. Source
bodies here are empty; target bodies are explicitly supplied writing bodies,
so these are payment-metadata witnesses, not body-lowering examples. Function/
fallback variants are directly supplied declarations, not resolved/admitted
source-unit witnesses. Reserved getter/function-reference/readonly work remains
untouched and required for its eventual applications.

DeclarationRoles reads source contract/library kind into the existing Role;
interfaces/non-code declarations do not become deployable roles. setRole changes
one supplied catalogue key and preserves all storage lookups/other keys.
library_role/library_create_refused/library_call_refused and the source metadata
composition prove actual intrinsic ordinary-call/create refusals. RoleControls
uses source library-unit membership, actual empty typed library deployment,
exact ordinary-create refusal and preserved other catalogue funding/state.
Catalogue identity/layout, abstractness, source placement/link resolution and
constructor/body source preservation are still explicit integration premises.

Independent finder/skeptic reviews found no mathematical/ownership/nonvacuity
defect, using no Lean/server/builds. Their wording finding is fixed: ordinary
intrinsic creation after source-role attachment is not source-new execution.
They confirmed the internal ambient-value distinction and direct declaration
fixture limits. Focused149597 passes the32 new laws/controls, all170 lane
declarations pinned, unchanged source/config; sampledRSS785846272bytes and
cgroup193691648bytes. Final combined closure supersedes this log after comment
clarifications, with raw documentation failures/zero-new gates kept separate.

Header metadata checkpoint handoff: current combined150409 passes106 named
modules/107 Lake jobs, all170 exact axiom sets, unchanged source/config,
sampledRSS835645440bytes/cgroup224149504bytes. Finder and skeptic independently
confirmed comment/fixture limits and exact source hashes without Lean/server/
builds; no further finding. Static/raw-doc comparison logs are header-*.
Parent395ea6818f11bc0af0738a9596a6992635601a44; exact committed head/patch at
/workspace/v08-world-lowering-artifacts/header-checkpoint.md and .patch.
This remains partial component coverage, not a parent/lane completion.

Next required validation: warm published import closures serially using the
diagnosed source/toolchain cache, prebuild native executable module facets
serially, then run the same full layer/default/TestSuite/sort gates under the
existing600-second bound. Investigate Lake's supported buildDir setting for a
fresh absent SolKey output directory, retaining the existing executable and
all generated evidence. No removal/reset or guard/budget relaxation is allowed.


## Continuation checkpoint: serial runtime and fresh executable validation

Parent041d313147ad8de5eae7447e954757f060772fac. No Lean theorem or budget
changes. The runtime runner now resolves actual package/library srcDir, including
all8 local LeanTeX modules, and orders local dependencies before each Lake job.
Native executable c.o facets are prebuilt serially. Current full closure891
modules. Header discovery stops at the first non-import command and ignores
nested comments; ambiguous/missing explicit targets fail closed.

Every container carries a unique run token. Finally cleanup verifies that token
before stop/kill, masks repeated termination signals, confirms stopped/absent,
and any intervention/unknown status forces125. Next-run preflight refuses an
active/uninspectable V08 container without touching it. Sanitized Docker env,
12GiB/no-swap, CPU1, LEAN_NUM_THREADS1, explicit Lean-j1, OS headroom and600s
cap are unchanged. Runtime config/source/toolchain hashes and actual versions
are bound to logs. Two generated untracked helper pycs are preserved under the
no-delete instruction, validated by exact hashes and excluded from commits;
future imports disable bytecode generation. The original untracked root TOML
is likewise preserved. No other-owner source is changed.

Refreshed Audit156811-ff29f154 passes106 named modules/107 Lake jobs,170 exact
axiom sets. Nine external evidence-corruption controls reject stale config,
wrong toolchain, unconfirmed cleanup and the prior six corruptions. Additional
external software controls cover actual vendored ordering, nested header
comments, missing target, foreign ownership, timeout/stop/kill, absent container
and repeated interrupt handling. These tests are not kernel or EVM evidence.

Fresh output158030-65d242d6 passes: supported Lake buildDir is the only config
change, unique output initially absent, source/toolchain cache reused, new
executable exists and old binary SHA remains
11eb6e37ff937d79901cb0072027ff3f9382552d7f65b421078934dadb6d216b.
Actual377 taclets/131read-bearing/131covered, annotations match. No file removal
or observation change. Literal run-lean.sh remains unexecuted because its
check-solkey.sh removes the old executable; the fresh output validates that
refresh operation independently, not an unreached full-build suffix.

Published closure158385-d132aac7 passes ProvesSound/Evm.Correct/TypingExamples/
Static.Standalone. Serial warm-up165162-a34945e8 passes Symex/Derived6, including
actual Derived6 build31s, final228Lakejobs; cgrouppeak3314925568bytes. This
cache progress justifies a new unchanged bounded full attempt; historical
baseline/task600-second exit125 logs remain failed gates, not baseline proof
errors. Full default/TestSuite/sort remains pending until actually reached.

Separate read-only finder/skeptic reviews used no Lean/server/builds. Fixed
findings: skipped vendor srcDir; cleanup could abort on repeated interrupt;
preserved generated pycs needed explicit accounting; old50-theorem/RSS text
needed historical labels. Both confirmed fixes and no new false-pass defect.
The full170-declaration implementation reviews found no new proof/nonvacuity/
ownership issue, while retaining all actual source/representation/decoder/
reserved-owner/composition prerequisites. No claim that every independent
conceivable clause is exhausted. Checkpoint exact head/patch and raw gate logs
are retained with the artifact handoff; the final full gate remains separate.


## Continuation checkpoint: inherited payment metadata

Parentbbaa90fdc2ecb423f03149cf8ec6dc2ad18bf211. Published Source.Inheritance
has FnOverrideOK.mutab and actual mutOK cases, allowing another independent G20
clause without source execution. InheritedMetadata.mutOK_payable proves every
accepted override retains the payable tag, including stricter nonpayable
view/pure cases. override_payable consumes the ACTUAL static certificate and
membership in environment.baseFns; override_enter transports only that tag in
existing World.enter, on the SAME supplied world/storage/context.
override_nonzero_rejected derives the ordinary-entry nonzero-payment refusal
from the source base's false tag, actual override check and existing frame law.
Internal ambient msg.value, source body identity/selection/dispatch, visibility
admission and V07 type/layout certificates remain separate.

InheritedControls builds an actual nonempty abstract A/B source unit with an
inheritance edge, virtual payable base and public payable override. Both function
memberships, computed baseFns=[base] and the ENTIRE FnOverrideOK record are
proved, so the checked relation is inhabited with a real base member. Source
function bodies are absent; the funded target uses the existing supplied
writing Entry and payment7, producing93/7/3/9 and exact bytes. It does NOT lower
these abstract source bodies. Dropping the actual header flag gives exact
.revert; payable/nonpayable override swaps are rejected, while none->view and
view->pure remain accepted. No new type/state/AST/semantics or profile cap.

Focused344280-0ca8d978 passes61 named modules/62Lakejobs,13 new exact axiom sets,
unchanged source/config, sampledRSS818855936bytes/cgroup203902976bytes. Initial
repeat-case proof was deliberately interrupted through the owned runner's
SIGTERM/finally path; cleanup was confirmed and125 retained, not passed. An
explicit finite-case proof checks quickly without a budget increase. Two
fixture-interface failures are retained and corrected; failed generated
sorryAx output is not delivered theorem evidence. Combined Audit/registration,
static gates and independent finder/skeptic reviews finish this checkpoint.

Validation progress since runtime checkpoint: full180746-5e221633 stopped125
at600s after346 successful invocations; default/TestSuite/sort suffixes unreached.
Serial segment205659-f689d24f stopped125 after256invocations during Bytes;
225601-77e8acda after293during CallOperands;245903-08312b5a after261during
Recursion;279023-fca93815 after300during OpenLoops;317963-c9d58b5f after415during
Frontend.Checked.UnitExamples. Raw failures remain failed. Successful focused
published checks include201735-c71be7f5, Recursion265909-e064e903(build346s),
and OpenLoops299349-1fb8f9fa(build529s, command565s). Caps remain600s/12GiB/
no-swap/Lean-j1; no reserved source changes. Remaining full-closure suffix and
unchanged final full gate are still pending. A passing cold target after a
segment timeout does not turn that timed-out command green.

Inherited checkpoint handoff: combined345133-8b7d471a passes110 named modules/
111Lakejobs,183exact axioms, unchanged source/config and confirmed cleanup;
sampledRSS824496128bytes/cgroup185667584bytes. Separate independent finder and
skeptic actual-source reviews used no Lean/server/builds and found no defect.
They confirmed the real nonempty base-list witness and explicitly independent
supplied target header fixture: source functions have zero parameters/results
and absent bodies, while the target returns bytes. No source body/result/
dispatch/readonly preservation follows. Static checks and raw-doc/no-new logs
are inherited-*. Exact committed head/patch is saved in inherited-checkpoint.md
and .patch under the artifact root. Parents/groups/lane remain incomplete.


## Terminal validation and committed handoff

Code checkpoint8230f88cf703841f1e12b4755a350d95289ee604, frozen base
fb379ae20f10e2c92113453ddd9d40d8f2efbe09, actual worktree
/workspace/v08-world-lowering-pinned. Entire frozen assignment remains PARTIAL;
source composition and full validation BLOCKED. No G parent or lane is complete.
The existing blocked persistent goal is unchanged. No goal creation/reset/
reactivation/completion, push/merge/PR or other-owner source edit occurred.

The final unchanged python3 scripts/v08-bounded.py --full command496841-193e914c
exits125 at the600-second guard after721 successful named invocations, during
Examples.Decision. Default-build/TestSuite/sort suffixes are UNREACHED. Sources/
config unchanged, actual Lean/Lake versions recorded and owned cleanup confirmed.
Decision isolated413142-e923f94d likewise exits125; exact-base isolated433573-
d4f1306f at the full frozen SHA also exits125 under IDENTICAL source/config/
toolchain/caps. Decision source byte equality and pristine baseline source are
recorded in decision-exact-base-binding.log. This establishes a validation
limit at both revisions, not a proof error, passing baseline or waiver. The
known generated baseline runtime config differed only in trailing whitespace;
old bytes were preserved before normalization. No proof/test/time budget rose.

Independent mandatory TestSuite command492734-76b30c10 PASSES260named modules/
262Lakejobs, including the actual aggregate SolkeyTestSuite pinned report.
Earlier cold suite453807-d2c2346a remains FAILED125 at Derived15. Focused
Derived15–21 warm-up474104-a5109491 PASSES in561.95seconds, with actual builds
88/6.4/146/8.5/57/144/73seconds. Largest sampled aggregate RSS11715137536bytes,
measured cgroup peak11363561472bytes, within enforced12GiB/no-swap. Sampled
RSS sums shared mappings and differs from cgroup accounting; both are retained.
Lean -j1, LEAN_NUM_THREADS1, CPU1 and OS headroom remain; no competing build/LSP.

Current full-inventory fresh executable496611-9f4df211 PASSES in3.09seconds:
unique initially absent supported buildDir output; new binary exists, old binary
SHA unchanged11eb6e37ff937d79901cb0072027ff3f9382552d7f65b421078934dadb6d216b;
377taclets/131read-bearing/131covered, annotations match. Only buildDir differs
in supported effective config; source/config/toolchain bindings retained.
Literal run-lean.sh remains unexecuted because its check-solkey.sh removes the
old executable under the explicit no-delete restriction. The fresh-output
refresh operation passes independently; unreached full suffixes are NOT claimed
passed. No compiler/EVM differential run or whole-source preservation follows.

The183 kernel-pinned component laws/controls,24owned modules and all conditional
premises remain as described in the continuation sections. G20 now includes
resolved signature/name/order/result metadata, payable/receive/fallback/role
clauses and real inherited payment metadata; source selection/body/type/layout/
getter/function-reference/readonly applications are still open. G21 remains
word/selector/panic/reason/existing-decoder observation coverage, with nested/
reference/slice/custom-error source applications blocked by the named missing
source/type/decoder interfaces. All G22.01–.05 source/runtime-frame/creation/
callback/library/function-value composition applications remain open. G23
projects actual source account/request/endTx fields and actual Keccak pin,
with target erased-emit effects and mixed rollback controls; source evaluation,
transient/layout, remaining reserved crypto and G16–G22 composition remain open.
Backfill A/B components are strengthened, not source applications discharged.
No arbitrary input exclusion, replacement source semantics or desired
preservation premise is introduced. Frozen V04/V05/V06/G15/V07 dependencies and
all existing owner reservations remain. No claim of exhaustive conceivable
independent lemmas is made; exact remaining prerequisites are preserved.

Final artifact finder/skeptic reviews verified actual base..8230diff,183pins,
24modules, patch bytes, copied feature, bundle head, proof/source bindings and
all checkpoint checksum entries, without Lean/server/builds. Reporting finding
fixed: emit controls use typed Entry.locals, not a capture/closure transport
certificate. Source capture/closure transport is not asserted. The previous
wording meant local slots and is now narrowed. Independent implementation
reviews found no new semantic/nonvacuity/ownership defect. Final artifact review
and static refresh are retained in reviews.md and final-* logs.

Process deviation: one early runtime-helper/checker edit was made without
acquiring the writer lock after an idle-build inspection. No unexpected change
or discarded work was observed; subsequent repository edits, bounded builds
and checkpoints were serialized. No locking claim is made for that early edit.
All three known generated untracked artifacts remain preserved and narrowly
validated; none is committed or removed. Original work/bridge branches and
same-VM caches remain. get_goal/Lean MCP are unavailable; the prior goal-tool
trusted-context limitation remains recorded and was not reset/retried.

Coordinator reconciliation proposal is EVIDENCE ONLY: add the owned adapter/
control theorem references as local component evidence for the exact feature IDs
in /workspace/v08-world-lowering-evidence/feature-ids.json. G20 evidence maps to
Callable/CallableMetadata/PayableMetadata/DeclarationRoles/InheritedMetadata;
G21 to AbiObservations/SelectorObservations; G22.01 to Callable/Controls,
G22.02 to Transactions/CallbackControls/ProjectionControls, G22.03 to
LibraryCreation/LibraryControls/Controls, G22.04 to LibraryCreation/DeclarationRoles/
RoleControls, G22.05 to funded/mixed/atomic controls, G23 to Transactions/
EnvironmentProjection/CryptoObservations/EmitControls. This does NOT mark every
listed feature covered, in particular reserved fixedPoint/precompile/reference/
getter/decoder applications. No global status, manifest, G03 ledger or reserved
TrustAudit pin was edited. Exact feature-ID lists are copied into final handoff.

Final original patch, incremental bundle, copied committed feature, handoff,
full evidence archive and SHA256SUMS are at /workspace/v08-world-lowering-artifacts.
Exact final committed head is recorded in handoff.md and repository-state.json,
with base/branch/absolute paths. Patch applicability against the exact base,
bundle verification and checksums are required and retained as separate gates.
All raw historical failures remain archived; final no-new-findings comparisons
do not turn raw documentation/axiom-pin failures green. No RUNTIME_GATE_PASS is
claimed beyond the actual recorded KeySort runtime pass with Lean4.24.0 and
Lake5.0.0-src+797c613. The full assignment remains unfinished.

Final static/axiom-binding handoff: refreshed519008-04a49e64 PASS110named modules/
111Lakejobs,183exact axiom sets, source/config unchanged and cleanup confirmed.
Final lane checker,9corruption controls, runtime controls, layers/orphans/trust
all PASS (final-* logs). Raw docs task/base exits1/1,46findings; raw global axiom
pins task/base exits1/1,14StorageSlots notes/613pins/0errors. Explicit separate
exact-base no-new comparisons PASS0; raw failures remain failures. Final code
proof binding is8230f88cf703841f1e12b4755a350d95289ee604; only this owned document
changes in the terminal handoff commit. Exact final head is saved externally
with verified patch/bundle/evidence/checksum artifacts. No goal completion.

## Nested rollback and creation continuation checkpoint

This continuation starts at ca730b02753d91e6db039bc07213c2e6020ca5b2, on the same
assigned worktree/branch/frozen base. New laws are in Transactions and
LibraryCreation, with NestedControls using published intrinsic operations. No
existing source semantics, owner files, goal or budgets change. Per-file Lean MCP
and get_goal remain unavailable. The cloud runtime skill was reapplied.

Missing law reproduced: prior transact_atomic_descendant covers one caught
boundary and a successful tail; prior descendant_failure returns outer failure;
prior tryCreate_success_continuation_failure lacks the enclosing atomic
application. None supplies two reached snapshots with two distinct failures and
a successful outer tail. New transact_two_boundaries consumes actual successful
enterOuter at reset input, actual successful enterMiddle at outer, exact inner
failure at middle, exact middleTail failure at middle/inner status, and exact
outerTail success at outer/middle status. It concludes exact reset final world
and result. Atomic consumers are arbitrary THalt consumers, NOT Solidity catch
handlers. transact_complete_observation transports ANY observation of the complete
world/TRes pair. transact_repeat_failure adds the missing failed second transaction
case, consuming actual first success and actual second failure at the committed
world's reset. It never restores the earlier transaction entry on second failure.

atomic_tryCreate_success_continuation_failure explicitly consumes the EXISTING
tryCreate_success_continuation_failure, with nonstatic context, actual successful
create, and actual failed success continuation. It restores its enclosing atomic
entry snapshot with the exact halt, without running the creation handler.
tryCreate_static and tryCreate_completed_failure preserve argument-before-catch,
static rejection and the existing catchable predicate. No exhaustion/divergence
constructor run is fabricated; their controls classify existing halts only.

New inhabited catalogue has original Cell at false and separate CreatedCell at
true with explicit payable constructor metadata. Supplied constructor Prog has
nonempty persistent/transient writes; its actual execution/payment/install is
checked. Both handlers and both status consumers are named separately. Extracted
world defaults cannot establish success: setup_reached/outer_reached/
middle_reached/creation_reached/tail_reached give actual successful TRes equalities.
A private extraction lemma uses a checked successful result observation, avoiding
function-valued world equality/reduction budget changes.

The complete ordered vector of the listed observations is: (sender balance,self balance,self persistent
saved,self transient scratch), third balance, third persistent/transient slots
if installed, third account-isSome, created-kind library-role. Exact statuses
are reported separately, with raw TRes preserved by complete_status and the
repeated-failure theorem. Checked vectors:

| Reached point | Full ordered vector | Exact result/halt |
|---|---|---|
| outer snapshot | ((93,7,3,9),0,none,false,false) | ok [ab,cd] |
| middle snapshot | ((91,9,5,17),0,none,false,false) | ok unit |
| successful constructor | ((88,9,5,17),3,some(8,12),true,false) | ok Handle true third |
| inner caught at middle | ((91,9,5,17),0,none,false,false) | revertWith [de,ad] |
| actual middle-tail paid call before later failure | ((84,16,3,9),0,none,false,false) | call ok [ab,cd], then revertWith [fa,02] |
| successful outer tail before reset | ((92,8,11,23),0,none,false,false) | ok [ab,cd] |
| committed/reset complete outcome | ((92,8,11,0),0,none,false,false) | ok [ab,cd] |
| repeated real scratch read | ((92,8,11,0),0,none,false,false) | ok 0 |
| second-transaction failure rollback | ((92,8,11,0),0,none,false,false) | revertWith [66,77] |
| actual wrong-ancestor tail from base | ((99,1,11,0),0,none,false,false) | ok [ab,cd] |

The dirty direct scratch read returns23 and differs from repeated transaction0;
wrong ancestor is an ACTUAL alternate continuation, not an invented tuple.
Nonempty wrong-result/payload [ab,ce], wrong second halt[66,78], stale transient23,
and success-continuation recatch alternatives are rejected. Static/argument
failures bypass handlers; a real paid reverting constructor is caught at middle
without installed account or leaked writes/payment. distinct_halts checks exact
[de,ad] vs[fa,02]. nested_application, repeated_application and
repeated_failure_application explicitly apply the general laws, not just compute
an unrelated toy expression. These are intrinsic supplied-body applications;
arbitrary source callback/body execution, source/V07 layout/ABI/bytecode/frame
certificates and all reserved owner applications remain open. Every G20-G23
parent and BackfillA/B full source application is still PARTIAL.

Independent finder and skeptic identified two concrete initial fixture issues:
original Cell lacked payable ctor metadata for payment3; an arbitrary wrong
balance tuple was too weak a wrong-ancestor control. Both fixed as above and
independently confirmed. Early failed bounded checks retained: recursion-depth,
missing local Decidable instances and context-name ambiguity were repaired with
staged observation instances/checked extraction/qualified Context, no budget
increase. One repeated-failure proof needed explicit reset idempotence; fixed.
Final actual-source reviews found no further defect (no Lean/server/builds).

Current Audit541494-647280cc passes111named modules/112Lakejobs,222exact printed
axiom sets,42.58seconds; sampled aggregateRSS974155776,cgrouppeak362598400,
unchanged sources/config and verified stopped container. Axiom sets contain only
propext/Classical.choice/Quot.sound. Lane checker and nine corrupted-evidence
controls PASS. Final static/executable validation and reviewed committed export
are recorded in the separate nested checkpoint handoff, preserving all previous
sealed exports. No global G03/status/TrustAudit pins are rewritten.

Decision forensics is retained in nested-decision-forensics.json/.md. Exact-base
isolated setup occurred48.79seconds after start and still produced no Decision
result before the600s guard; no native phase or cold Built dependency in that
isolated log. Full run spent238.45seconds before Decision setup, but eliminating
startup alone is not a demonstrated sufficient repair. Actual setup/options/cache
bindings and stopped-container timestamps are retained. No supported repair was
established under frozen constraints, so NO identical full retry was performed.
Prior full496841-193e914c and isolated task/base remain FAILED125 with full suffixes
UNREACHED, not waived by the baseline timeout. Literal run-lean remains PENDING
under the previously recorded no-delete conflict; independent fresh refresh is
separate evidence. Prior98gate records and sealed exports remain untouched.

Nested checkpoint validation handoff: TestSuite543634-f3408386 PASS260named/
262jobs,41.59seconds, sampledRSS63152128/cgroup38506496. Fresh-sort546423-
6372f597 PASS3.05seconds, sampledRSS216166400/cgroup408039424, actual initially
absent supported output directory and old executable preserved;377taclets/
131read-bearing/131covered/annotations match. Actual Lean4.24.0 commit797c613/
Lake5.0.0-src+797c613, passing KeySort2jobs in the fresh log, recorded before
runtime success claim. Runtime evidence is not full source validation.
Nested static/lane controls PASS:222pins,9evidence corruptions, runtime controls,
169core/0elaborator,891reachable/0orphan/0disallowed,906sources/241trustsites/
0findings. Raw task/base docs exits1/1 with46missing; raw global axiom pins
exits1/1 with14StorageSlots notes/613pins/0errors; exact-base separate NEW0 PASS.
Raw failures remain FAILED. git diff --check PASS. Neither full gate nor literal
run-lean is relabelled green. No external compiler/EVM tests were run.

Separate independent read-only finder/skeptic final source/doc/evidence reviews
confirmed both substantive fixes and source/config/log/222pin bindings, with no
remaining mathematical/nonvacuity/ownership finding. Finder wording precision
fixed: this is the complete listed observation vector, not every world field;
the generic law separately proves exact world equality. No Lean/server/build by
reviewers. New scoped commit/export and final artifact reviews are saved under
/workspace/v08-world-lowering-artifacts/checkpoint-nested-20261030 and
nested-reviews.md, without overwriting any prior sealed export/checksum. Every
queue item's source applications and mandatory full validation remain unfinished.
Further independent repeated-failure backfill was completed beyond the suggested
two-boundary milestone; no claim of exhaustive possible adapter lemmas is made.
Named source-execution/type/layout/owner prerequisites above block full-lane
completion, without being assumed or replaced by target evaluation.

Process correction for this checkpoint: proof/document/evidence edits and builds
held the writer lock. The git add/commit commands for c522d898 ran after the
Python lock-owning process exited, so those two Git mutations were not locked.
No competing build/writer or unexpected change was observed. This deviation is
recorded rather than claiming lock coverage; subsequent Git/export commands
retain the lock in their parent through completion. The original earlier helper
lock omission remains recorded separately above.

## Catch-handler failure checkpoint

Same frozen branch/base/worktree, continuation from7a8a8884e6020cb9a207df631bdc607e7a17609c.
No goal mutation, other-owner edit, unpublished import, new VM/thread or budget
change. get_goal and per-file Lean MCP remain unavailable. Repository lean-verify
and cloud runtime guidance were reapplied; focused closure substitutes for absent
MCP. Every original G20-G23 and Backfill A/B parent remains PARTIAL; whole-source
composition and mandatory full validation remain BLOCKED.

Missing branch reproduced by actual source audit: prior NestedControls.handler
returns ok(snapshot,unit), caught_creation_vector therefore exercises successful
catch continuation only. inner_not_reCaught/creation_atomic exercise failed
SUCCESS continuation after successful construction. Neither proves nontrivial
catch-handler work followed by failure. LibraryCreation.tryCreate_completed_failure
retains the branch predicate, but supplies no application of this failed-handler
case. New laws consume it directly, without another evaluator or payload emitter.

New generic laws:

- tryCreate_handler_steps_failure consumes nonstatic context, actual World.create
  failure, catchable=true, actual handler work success at the SAME failed-create
  snapshot, and actual later failure at the work's returned world/result. The
  handler result is DERIVED by monadic sequencing, not supplied as a desired
  whole-handler failure hypothesis. Exact handlerHalt propagates, not the original
  creation halt. Generic halts need not be distinct; fixtures prove distinctness.
  Creation-frame failure can include guards; body execution is not inferred from
  the generic failed-create premise alone.
- atomic_tryCreate_handler_steps_failure restores the creation entry snapshot,
  discarding the successful handler prefix and preserving its later exact halt.
- transact_tryCreate_handler_steps_failure additionally consumes actual ancestor
  prelude success at transaction.resetTransient input. The enclosing transaction
  restores ITS OWN reset entry, not the later creation or handler snapshot.
- transact_failure_then_commit preserves BOTH raw statuses of a failed transaction
  followed by actual success at the reset entry. Reset idempotence supplies the
  second transaction's actual input; dirty handler/setup state is not reused.

HandlerControls inhabits these laws with the existing Bool catalogue: original
Cell at false, payable CreatedCell at true. Actual setup creates another false
Cell at address4, writes saved19/scratch29 and pays it5 from sender100. A paid7
ancestor writes self3/9. A typed nonempty constructor writes8/12 then existing
revertData with published Semantics.encodeError("ctor" bytes). Its actual result
is revertWith(Error bytes), distinct from guard revert. A separate actual typed
entry/prefix view checks constructor incoming balance3,msg.value3,slots8/12 and
pending sender debit3 BEFORE the joined failure; no installed world is fabricated
for an incomplete constructor. The constructor failure returns no world.

The handler checks the EXACT original halt, pays2 to self, writes11/23 and returns
[b1,b2]. A later real paid1 typed call writes31/37 and fails with existing
revertData/encodeError("handler" bytes). Only the prefix payment2 completed; the failing later frame has attempted
payment1 with no successful settlement or returned world. Work and later actual-run equalities
are checked independently; handler_failed derives their composite. The handler's
failure is outside the creation catch. Both reasons are nonempty, exact encoded
Error bytes. Source.errorData equality is reused only for payload observations;
there is NO Source execution, canonical ABI/layout, string-allocation lowering,
source catchability or bytecode preservation claim.

The complete ordered LISTED vector is: (sender/self balances,self saved/scratch),
third balance,third saved/scratch if installed,third isSome,created-kind library
role; then (fourth balance,saved,scratch),[fourth installed,fourth wrong-kind-true
storage exists,false-kind library role]. It does not enumerate every World field.
Generic rollback laws separately preserve the complete exact snapshot.

| Point | Full listed vector | Exact status |
|---|---|---|
| setup/base | ((95,0,0,0),0,none,false,false);(5,19,29);[true,false,false] | setup ok(base) |
| paid ancestor/creation snapshot | ((88,7,3,9),0,none,false,false);(5,19,0);[true,false,false] | ok[ab,cd] |
| completed failed constructor | no returned world; handler input is exact ancestor above | revertWith(Semantics.encodeError[99,116,111,114]) |
| actual paid handler prefix | ((86,9,11,23),0,none,false,false);(5,19,0);[true,false,false] | ok[b1,b2] |
| failed later handler call | no returned world | revertWith(Semantics.encodeError[104,97,110,100,108,101,114]) |
| enclosing atomic | ((88,7,3,9),0,none,false,false);(5,19,0);[true,false,false] | exact handler halt |
| enclosing transaction | ((95,0,0,0),0,none,false,false);(5,19,0);[true,false,false] | exact handler halt |
| actual wrong handler snapshot(base.resetTransient) prefix | ((93,2,11,23),0,none,false,false);(5,19,0);[true,false,false] | ok[b1,b2] |
| actual skipped-payment prefix | ((88,7,11,23),0,none,false,false);(5,19,0);[true,false,false] | ok[b1,b2] |
| repeated fourth scratch read after rollback | ((95,0,0,0),0,none,false,false);(5,19,0);[true,false,false] | first exact handler halt; second ok0 |

Actual panic constructor and actual panic handler-call controls use assert(false),
with distinct catch-input versus propagated-output boundaries. Collision at an
already installed self returns guard revert, enters a matching paid/write handler
and propagates its new encoded halt. Panic/collision atomic controls include full
listed vector and RAW TRes status. Argument error[a0,01] and static revert bypass
the handler. Existing catch_classification is classification evidence only for
exhausted/diverge; no actual such execution is asserted. Actual handler panic is
proved different from exhausted/diverge. All refusals/panic/error distinctions
remain. Untouched_atomic/untouched_transaction give exact fourth-account equality
at the appropriate snapshot (transaction compares to RESET entry, not dirty base).

Wrong-snapshot and skipped-payment negatives are independently executed real calls,
not invented tuples. Reapplying the handler to its NEW halt produces panic because
its original-payload guard refuses it; recatch_negative distinguishes this actual
alternative. Original constructor halt, one-byte-wrong handler reason, wrong ancestor
boundary and dirty fourth transient29 alternatives are rejected. The published
tryCreate_observe law maps BOTH continuations and preserves this exact failure;
observed_handler_failure/observed_atomic_status are actual applications. Repeated
failure-then-success application retains both exact statuses and actual scratch0,
not a constant result stand-in.

Proof iteration raw failures remain preserved: invalid namespace alias, local
instance naming/qualification, staged setup extraction, explicit implicit-kind
argument and observation-law/projection elaboration repairs. Initial string-literal
reverts exceeded reduction depth; fixtures now use the existing typed revertData
with published encodeError bytes, preserving the specified observed payloads.
This is a supplied intrinsic-byte fixture, NOT a proved source string-allocation
lowering. No maxRecDepth/maxHeartbeats/proof/fuel/node/test/time increase, new
axiom/sorry/native_decide/implemented_by or profile exclusion was introduced.

The lane evidence test now creates a unique PERSISTENT mkdtemp directory per run
(no deletion/overwriting prior fixtures), retains existing nine corruptions and
adds changed/missing HandlerControls source corruptions. These are external
software evidence-integrity tests, separate from kernel negative controls. No
runtime helper/config/cache policy or target/exclusion was changed.

Current Audit574247-19f3ea03 PASS112named modules/113Lakejobs,276exact axiom sets,
37.40seconds; sampledRSS1172090880,cgroup575324160; source/config unchanged and
owned container cleanup verified. Actual Lean4.24.0 commit797c613/Lake5.0.0-src+
797c613 recorded by bounded runner. Serial Lean-j1/LEAN_NUM_THREADS1,CPU1,
aggregate12GiB/no-swap,600s guard and OS headroom preserved. Scoped source-bound
checker, eleven corruption cases, structural/trust/docs comparisons and independent
Suite/fresh executable refresh are recorded in handler-* logs/final handoff.

Separate independent read-only finder/skeptic reviews (no Lean/server/builds)
found no semantic/nonvacuity/ownership defect. Wording fixes distinguish generic
creation-frame guards from actual constructor execution and permit equal generic
halts; actual fixtures prove distinct reasons. They require supplied-byte wording
rather than source string-allocation lowering; the distinction is explicit above.
Final source/script/evidence/artifact reviews are retained in handler-reviews.md.
All source/build/git/export operations in THIS continuation retain the writer lock
through completion; earlier recorded lock gaps remain historical, not erased.

No supported new Decision repair evidence arose. Full496841-193e914c and isolated
task413142/base433573 remain FAILED125 at600s; full default/Suite/sort suffixes
UNREACHED, current whole-source gate unvalidated. No unchanged Decision/full retry,
owner-file/Elab.async edit, omitted verdict or budget increase. Existing forensics
remain unchanged. Literal run-lean remains PENDING under the no-delete wrapper
conflict; independent fresh refresh is not a full-gate substitute. Raw docs/global
pin exit1 failures and exact-base NEW0 comparisons stay separate. No external
compiler/EVM differential tests. No G parent or lane completion/goal mutation.

Coordinator proposal: add Transactions/LibraryCreation/HandlerControls checked
component evidence to the existing exact feature IDs for G21/G22.03/G22.05/G23
and BackfillA/B where applicable, EVIDENCE ONLY. No manifest/global ledger/status/
reserved pin edit or missing Source/V07/frame/layout/decoder premise discharge.
Full original queue still applies: G20 callable resolution/body/type/getter/function-
reference/readonly applications; G21 nested/reference/calldata/slice/custom-error
source applications; G22.01-.05 source call/callback/create/library/function-value/
world/runtime composition; G23 source transient/environment/crypto/emit execution
and G16-G22 source-unit composition; BackfillA/B source applications. All remain
PARTIAL under the same named prerequisites. This checkpoint also strengthened
observation extension and failed-transaction repetition beyond the suggested
handler case; it is not the entire lane's completion.

Handler checkpoint validation/committed handoff:54new public kernel-pinned laws/
controls,276total in26owned modules. Suite576120-01a3b2c8 PASS260named/262jobs,
43.38s,sampledRSS63242240/cgroup38350848. Fresh578874-a4a2def8 PASS3.10s,
sampledRSS54697984/cgroup408510464,initially absent
supported output directory;old executable unchanged;377taclets/131read-bearing/
131covered/annotations match. Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
Lake5.0.0-src+797c613;actual KeySort two-job build PASS in fresh log before any
runtime-success claim. No whole-lane RUNTIME_GATE_PASS is inferred.

Current handler-check.log and handler-controls.log bind574247/276pins and eleven
corruptions. Earlier570092/269pin check/control logs were preserved separately
as handler-check-269.log and handler-controls-269.log before refresh. Unique
persistent fixture directories retain each run. Runtime controls PASS, layers
169core/0elaborator,orphans892reachable/0orphan/0disallowed,trust907sources/
241sites/0findings. Raw docs task/base exits1/1 with46missing;rawglobalpins
exits1/1 with14StorageSlots notes/613pins/0errors. Separate exact-base NEW0 PASS;
raw failures stay FAILED. New original/checkpoint patches,bundle,handoff,full
command/evidence archive and checksum manifest use fresh export directory
/workspace/v08-world-lowering-artifacts/checkpoint-handler-20261030. Prior64-entry
root and10-entry nested seals remain unchanged;all raw prior gate records/logs
and failed developmental checks are retained. Exact new committed head is recorded
in the external handoff/repository-state evidence,not guessed in this document.
Separate final finder/skeptic artifact reviews follow source/script/doc reviews.
The original queue and existing blocked goal remain unfinished and unchanged.

## Library work in a failed creation handler

Continuation froma8a1b099162bd46283216de45057fe1e9d19e291 on the unchanged frozen
branch/base/worktree. Existing blocked goal untouched;get_goal/LeanMCP unavailable.
Original276pins retained with identical axiom sets;46new declarations make322total
in27owned modules. No other-owner edit,unpublished import,new semantics/AST/value/
state layer,decoder/emitter,premise weakening,exclusion,changed original observation
or proof/fuel/node/test/time/resource budget. All original queues remain PARTIAL.

Missing combination reproduced against actual code: LibraryControls.delegated_owner
is successful caller-context delegation; HandlerControls.work is ordinary paid
World.call in a failed creation handler. Neither combines actual library work,
creation catch and a later failed call/ancestor rollback. New LibraryHandlerControls
uses only published typed Contract/World/Library/Entry/Prog and actual operations.
It reuses LibraryControls.linkedCatalog(false Cell,true Empty) and roles, rather
than introducing another catalogue/interpreter. Empty library storage is REQUIRED
by deployLibrary's guard. Actual setup_reached includes successful deployLibrary,
therefore all role/vars/ctor/inits/runtime guards; library_fields_empty alone is
only its field fact, not a sufficient deployment certificate.

New core adapters tryCreate_library_handler_failure,
atomic_tryCreate_library_handler_failure and
transact_tryCreate_library_handler_failure specialize the existing handler-step
laws to an ACTUAL caller-typed libraryCall at the creation-entry snapshot. They
retain explicit actual creation failure,catchable predicate,delegated success and
later failure premises; transaction adapter also retains actual ancestor success
at reset input. Handler result is derived by bind,not assumed as a whole-handler
equation. Supplied libraryContext/source linkage/body selection/admission/frame/
bytecode relations remain unproved prerequisites. Generic creation failure may
be guards; no source catchability or arbitrary source callback is asserted.

libraryCall_other_accounts derives the published World.finish_other through the
actual successful library invocation. It preserves complete NONCALLER account
storage/code records only; a supplied body's explicit ledger can change balances,
so no generic balance or readonly preservation claim is made. The actual fixture
body has no transfer, and its exact balance vector is checked separately. Applied
account equalities preserve both installed library and populated other instance,
not merely selected empty fields. This does not redo ordinary readonly-call owners.

Actual setup creates caller/self2 and other3,deploys library4,then pays5 to other
and writes its slots19/29. Initial timestamp is12345,sender1 has100. Paid ancestor7
writes caller3/9. Creation of fresh candidate5 uses ZERO-value ctorCtx(sender2),
consistent with Cell's implicit nonpayable constructor metadata. Its nonempty
closed typed body writes8/12 then existing revertData/encodeError(ctor bytes);
actual create returns its nonempty encoded halt. ctor_input_reached and
ctor_input_context check actual State entry[2,0,5,0,12345],not a fabricated installed
world. Candidate never installs. Handler delegates using actual caller handle and
paidCtx(sender1,value7); it writes caller.saved=msg.value+4=11 and scratch23,returns
[b1,b2] plus all five actual context fields. libraryCall starts its net ledger
empty and does not charge value7 again. A later actual ordinary1 call writes31/37
then fails with encoded binary reason[6c,00,ff,48]. Its attempted payment1 never
settles or returns a changed world. Failure is outside the creation catch.

Complete ordered LISTED vector:

- balances=[sender,caller,library,other,candidate];
- stores=[caller(saved,scratch),other(saved,scratch),library roots];some[] is an
  INSTALLED empty library store,none would mean missing/wrong runtime kind;
- flags=[caller installed,library installed,other installed,candidate installed,
  caller false-kind lookup,library true-kind lookup,library false-kind lookup,
  other false-kind lookup,false-kind library-role,true-kind library-role].

Flags are F=[true,true,true,false,true,true,false,true,false,true] at every
successful reached/rollback point below. Empty library has no persistent or
transient slots to invent. This projection does not enumerate every World field;
generic rollback/account equalities separately preserve exact worlds/records.
Context vector is [sender,value,self,balance,timestamp].

| Actual point | Balances; stores; flags | Exact status/context |
|---|---|---|
| setup/base | [95,0,0,5,0];[[0,0],[19,29],[]];F | setup ok(base) |
| paid ancestor/creation snapshot | [88,7,0,5,0];[[3,9],[19,0],[]];F | ok[ab,cd];ordinary caller ctx sender1,value7 |
| creation entry/failure | same entry snapshot;no world returned by failure | actual entry ctx[2,0,5,0,12345];revertWith(encodeError[63,74,6f,72]) |
| delegated handler prefix | [88,7,0,5,0];[[11,23],[19,0],[]];F | ok([b1,b2],[1,7,2,7,12345]) |
| later failed call | no returned world | revertWith(encodeError[6c,00,ff,48]);attempted payment1,unsettled |
| enclosing atomic | [88,7,0,5,0];[[3,9],[19,0],[]];F | exact later halt |
| outer transaction | [95,0,0,5,0];[[0,0],[19,0],[]];F | exact later halt |
| real ordinary double-payment alternative | [81,14,0,5,0];[[11,23],[19,0],[]];F | ok([b1,b2],[1,7,2,14,12345]) |
| real wrong-caller delegation | [88,7,0,5,0];[[3,9],[11,23],[]];F | ok([b1,b2],[1,7,3,5,12345]) |
| real wrong-context delegation(value0) | [88,7,0,5,0];[[4,23],[19,0],[]];F | ok([b1,b2],[1,0,2,7,12345]) |
| subsequent two real read calls | [95,0,0,5,0];[[0,0],[19,0],[]];F | first exact later halt;next ok[0,0,19,0] |

All store rows above mean some lists,including some[] for library. Actual
wrong-runtime-identity points the true-kind link at an installed FALSE-kind other
account and returns revert before writes. Wrong-role and static-writing-library
contexts also actually return revert under published guards. Double-payment,
wrong-caller/context,wrong ancestor snapshot and stale-other-transient29 controls
are independently checked actual alternatives,not invented world states. Exact
one-byte-wrong binary reason is rejected. Encoded creation/later halts are distinct;
Source.errorData equality is consumed only for byte observation,not Source execution.
No exhausted/diverge execution is fabricated; prior classifications are retained.

Observation extension is deliberately LOSSLESS: observe returns(original Result,
byte length). observation_retains_result proves that every original result byte
AND all context fields remain. libraryCall_observe gives actual observed prefix
success; observedLater consumes its ORIGINAL returned result in the actual later
call. Specialized creation-handler law then proves the same exact failure. The
published tryCreate_observe also maps BOTH complete continuations in mappedAttempt
without swallowing the halt. No inverse of a lossy length observation is assumed.
Repeated application consumes transact_failure_then_commit with actual frame
failure and two actual caller/other storage-read calls; it retains BOTH raw statuses
and actual [0,0,19,0],not a constant-read stand-in. Source library/function-value/
ABI/layout/runtime/callback composition remains absent and unclaimed.

Initial libraryCall_other_accounts proof produced unused-simp warnings; removed
without disabling linters. Observation normalization hit the original200000
heartbeat limit once; factored a small map lemma over an abstract existing World
instead of expanding the concrete reached world. Raw failed595699-c47a6339 retained;
no budget increase or weakened statement. New fixture/compiler source untouched
outside owned namespace. Thirteen external evidence-integrity corruptions retain
the earlier eleven plus changed/missing LibraryHandlerControls source; unique
persistent test directories preserve all prior fixtures. Kernel controls and
software evidence tests are distinct from external solc/EVM testing (not run).

Audit598615-a8cbdaeb passes113named modules/114Lakejobs,322exact axiom sets,
25.74seconds;sampled aggregateRSS1137020928,cgroup535224320;source/config unchanged,
owned container cleanup verified. Old276sets are unchanged,all322subsets of
propext/Classical.choice/Quot.sound. Earlier321gate/check/control evidence is
historical and preserved before final322refresh. No per-file MCP/get_goal exposed.
Runtime/build constraints unchanged: existing approved runner enforces actual
memory.max12884901888/swap.max0,CPU1,LEAN_NUM_THREADS1/Lean-j1,600s and OSheadroom;
heavy checks serial with no LSP/build competition. Initial disk free2880647168bytes,
recorded before builds; caches/files/seals preserved. New export remains separate.

Independent finder/skeptic read actual proof/control/script source without Lean/
server/builds. No semantic/nonvacuity/ownership finding. They confirmed account
frame excludes balances/readonly,actual complete deployment guards via setup,
zero-value constructor context,populated other account,exact statuses and source
boundaries. Final lossless observation refinement,current source-bound gates,
strict/Suite/runtime/static checks and artifact reviews are recorded separately.

All original G20,G21,G22.01-.05,G23 and BackfillA/B remain PARTIAL. Full source
execution/V07/type/layout/ABI/frame/bytecode/library-resolution/function-value/
getter/readonly/decoder/precompile applications and source-unit composition stay
open under the SAME frozen prerequisites/reservations. Whole lane not complete;
existing blocked goal untouched. No unchanged Decision/full retry or distinct
supported repair evidence: full496841 and task/base413142/433573 stay FAILED125;
full suffixes UNREACHED,currentfullunvalidated,literalrun-leanPENDING. No global
doc/inventory gate is called passed from a no-new comparison. Actual raw full
finding lists (missing AND ambiguous) are compared,not just unique missing paths.
Proposed ledger reconciliation is EVIDENCE ONLY for G22.03-.05/BackfillA-B and
payload/reset observations where applicable; exact feature IDs remain inherited.
No global ledger/status/manifest/reserved TrustAudit pins edited.

Library-handler checkpoint final validation/handoff:46new declarations,322total
pins/27modules,all original276sets unchanged. Suite600083-a1505eac PASS260named/
262jobs,41.08s,RSS63111168/cgroup36298752. Fresh602778-aba5e9e8 PASS3.02s,
RSS228888576/cgroup408064000,new supported initially absent
output directory,old executable SHA unchanged;377taclets/131read-bearing/131covered/
annotations match. Actual Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b
and Lake5.0.0-src+797c613,actual two-job KeySort build PASS recorded before runtime
success. Runtime component success is not full-source/lane validation.

Current source-bound checker PASS322pins/59coreclosure;13corruptions PASS,including
newfile omissions/changes;earlier321logs preserved separately. Runtime controls,
layers169core/0elaborator,orphans893reachable/0orphan/0disallowed,trust908sources/
241sites/0findings PASS. Strict automatic coverage PASS491automatic/61step-budget/
0manual/11refuted/0pending. Raw doc task/base exits1/1 with FULL72/72 identical
finding rows:46missing+26ambiguous. Separate full-list NEW0 PASS;earlier46 figures
counted missing only,not all finding classes. Raw global axiom inventory task/base
exits1/1,14StorageSlots notes/613pins/0errors;separate identical-list NEW0 PASS.
Neither raw global gate is called passed. No reserved global pins/docs rewritten.

Separate bash scripts/check-testsuite.sh inventory attempt FAILED1 because its
default ../solkey examples directory is absent;parity suffix was UNREACHED. Existing
supported --solkey root /workspace/.setup/solkey/keyext.solidity.examples was then
discovered read-only. Inspection also found its EXIT trap removes its OWN newly
allocated scratch directory: that cleanup ran in the failed invocation. No
preserved checkout/cache/seal path was removed. This process deviation under the
frozen no-delete constraint is disclosed;wrapper not rerun/rewritten to bypass
cleanup. Inventory remains failed/unvalidated,not promoted by strict/Suite/fresh
or NEW0. Initial static driver stopped there;global docs/pins ran separately
later with actual raw failures. Subsequent independent fresh command passed;
combined shell exit0 never makes the failed driver/inventory green. Raw output
and explanation are library-handler-testsuite-inventory.log and
library-handler-inventory-limitation.md. Literal run-lean remains separately
pending under its previously recorded deleting-wrapper restriction.

Runtime code identity here means the PUBLISHED catalogue-kind/role/installed
lookup,not EVM bytecode hash or source-resolved declaration identity. The supplied
Library body and source linkage/admission remain prerequisites. Account preservation
covers complete catalogue-key/storage records;bytecode/runtime-source composition
is not certified. Lossless observation refinement and all current source/pin/log
bindings were independently finder/skeptic reviewed read-only without Lean/server/
builds,no findings. Source/build/Git/export writer-lock coverage in this continuation
is retained through completion. Historical earlier lock gaps remain recorded.

New reviewed commit/export uses
/workspace/v08-world-lowering-artifacts/checkpoint-library-handler-20261030;
original patch,checkpoint patch,named branch bundle,current/inherited handoffs,
full120+record evidence archive and checksums use NEW paths. Prior64root/10nested/
11handler seals remain. Head/base/branch/path and every original queue item are
recorded in new handoff. Goal untouched/blocked,no get_goal exposed. No Source/V07/
type/layout/ABI/runtime-frame or reserved-owner prerequisite is assumed or closed;
all G20-G23/BackfillA-B source applications remain unfinished. This checkpoint
adds real lossless observation and repeated-read backfill beyond the suggested
combined case;it is not the original lane's completion. No supported distinct
Decision repair appeared,no unchanged full/Decision retry,and all old failed125/
unreached/pending boundaries are retained. No external solc/EVM run claimed.

### Independent inventory audit followup

After the retained literal wrapper failure, a distinct non-deleting inventory
route was inspected and completed. Published solkey-port.mjs ran WITHOUT --probe,
using supported --solkey pointing to the frozen checked-in migration snapshot and
--out a NEW persistent evidence directory. It verifies snapshot/source hashes
against existing AST/pins;no source re-pin,compiler invocation,Lean build,network
or repository-generated-output change. The wrapper's ENTIRE inline Node audit
was copied byte-for-byte (SHAfd3ba52fd9fadcafc18914c600af1bad9842691f62284d9dd8af44db6899abae)
and executed as stdin with complete=1 against those persistent outputs. No audit
condition was removed or modified. Original wrapper remains byte-identical to
exact base(SHA901475da34815efa09338b1129f3aa3fc2110b8d2e7a8b103d81115bd56c0223)
and was NOT rerun;its default-root FAILED1 and initial-driver failure stay FAILED.

Independent generation/audit actual exits0/0:31modules trust;existing axiom pin;
564testSuiteFunctions=552derived+11refuted+0pending+0divergent+1EXISTINGexcluded,
2skip. No new exclusion or proof premise. Source snapshot473da8944c and TestSuite
source hash were checked by the existing generator. sole generator rmSync occurs
inside probe(),not called because PROBE=false. All new outputs persist. Actual
Nodev24.19.0. Both independent read-only finder/skeptic verified exact audit bytes,
parameters,pin binding,no deletion/probing and actual output;no Lean/server/builds.
This is genuine independent inventory/parity PASS,not NEW0,not literal wrapper
PASS and not kernel/source/full-gate completion. Evidence is
library-handler-inventory-independent.json/.log,library-handler-inventory-generate.log
and library-handler-inventory-audit.mjs plus persistent output directory.

The prepared df2f9b4f export is retained unchanged. Final documentation followup
and all source fingerprints are recorded at a NEW final export path:
/workspace/v08-world-lowering-artifacts/checkpoint-library-handler-final-20261030.
No Lean/script/proof/pin/budget changes in this followup. All original queues,
reserved prerequisites,failed125/full suffixes and pending literalrun-lean remain
unfinished. Original persistent blocked goal unchanged.


## Successful creation and library success continuation (2026-10-30)

Starting checkpoint c3895e4140ad974467ca42c327e9505e9f12fbd8. The coordinator's
reviewed optional-cache repair restored3282042880 available bytes; its receipt
is preserved at /tmp/cloudvm-cache-repair-20261030.json. No worker cleanup was
performed. New scripts/v08-no-artifact-cache.py executes the existing bounded
runner with exactly two asserted substitutions: Docker receives LAKE_CACHE_DIR
as the empty string and LAKE_ARTIFACT_CACHE=false, and inner shell assertions
verify them before Lake. Warm package outputs and every resource/proof/test/time
budget remain unchanged. The original runner and wrapper are separately hashed.
All new builds use this wrapper; the preserved artifact cache remains1365files.

The previously missing combination is now inhabited in
Solidity/Lowering/V08/CreationSuccessControls.lean: actual nonempty goodCtor
installs candidate5 with persistent8/transient12, then caller-typed linked
library work runs in the SUCCESS continuation, followed by the real paid failing
call and its exact encoded binary reason [0x6c,0,0xff,0x48]. This complements the
previous failed-constructor CATCH-continuation witness. The new general
tryCreate_library_success_failure explicitly requires the actual create,
libraryCall and later-failure executions plus the nonstatic creation context;
it does not supply source linkage/admission/body/runtime preservation.

The complete previous ordered vector is retained, with candidate typed cells
and typed installation identity appended. Shared setup, paid ancestor and
constructor-entry contexts are the existing LibraryHandlerControls witnesses.
Constructor entry remains [2,0,5,0,12345]; delegated result retains bytes[b1,b2]
and the entire incoming context [1,7,2,7,12345]. Created and delegated worlds
have balances[88,7,0,5,0]; caller cells move3/9 to11/23, candidate remains8/12,
other remains19/0 and installed library has empty fields. Complete library,
other and candidate account records are preserved by actual library execution;
no generic balance or readonly-body inference is made. Runtime identity means
published catalogue-kind/role lookup, not deployed bytecode hashing.

The exact later halt is not recaught by the distinguishable panic handler.
Atomic rollback returns paid ancestor3/9 with candidate absent; outer rollback
returns reset base0/0 with candidate absent and balances[95,0,0,5,0]. Positive
keep/commit retains candidate8/0 and caller11/0 after reset. Actual subsequent
reads return[11,0,19,0,8,0]. Failure-then-recreation really creates and commits
the SAME address next transaction, retaining both original statuses and the
complete extended vector. Wrong-world/snapshot, actual double payment,
wrong-role/runtime-kind, binary payload and wrong-context success-continuation
runs discriminate actual executions. Lossless observed library success and
failure retain original bytes/context plus length and feed actual returned
values to the later continuation.

Current Audit gate632880-f112508e passes115Lake jobs in24.792s:355exact axiom
sets, including all322previous sets unchanged (and therefore original276).
Sampled aggregateRSS1040109568,cgrouppeak439570432;12GiB/no-swap,CPU1,
LEAN_NUM_THREADS1/Lean-j1,600s and OSheadroom guards unchanged. Actual Lean4.24.0
and Lake5.0.0-src+797c613 are recorded with passing KeySort in the log.
Proof iterations622173/624200, import-header failure626323 and keyword syntax
failure631953 remain raw failed evidence; all corrected without budget rises.
Fifteen external corruption controls include changed/missing new source.

Independent finder and skeptic read the actual proofs/controls/wrapper without
Lean/server/builds: no substantive findings. Both required separate hashes of
wrapper and original runner because the transformed runner executes in memory;
that provenance requirement is included in the new evidence. Current scoped
checks do not waive full496841/taskDecision413142/baseDecision433573 exit125,
raw global docs/pin exits1, or pending literal-wrapper validation.

Every original G20,G21,G22.01-.05,G23 and BackfillA/B source/application queue
remains PARTIAL. Canonical Source/V07/type/layout/ABI/body/runtime-frame/
bytecode/linkage and reserved-owner applications remain open; this checkpoint
is intrinsic supplied-body execution, not Source lowering, callbacks or an
external compiler/EVM test. No claim that all independent adapter work is
exhausted. Proposed G03 reconciliation is additional local evidence for
G22.03-.05/BackfillA-B only; no global status or ledger was edited.


### Final boundary and validation record

The preceding355-pin Audit is stage evidence. Final Audit704511-e74a9e12
passes115jobs in25.287s with357exact standard axiom sets: all previous355,
322 and original276 sets unchanged. New repeat_vector_statuses proves the
ENTIRE extended vector after actual repeated reads with BOTH statuses; actual
rollback_candidate_read_fails runs that same procedure at the rollback world
and returns exact revert. Independent finder/skeptic reviews found no defects
in these two boundary proofs. SampledRSS1066622976/cgrouppeak487723008.

Current Suite705959-ff5fe225 PASSES all260 requested modules/262jobs in179.811s;
sampledRSS5984354304,cgrouppeak6023221248. Prior Suite643413/664651/684784 remain
FAILED125 under the unchanged600s guard (cleanup adds about10s), respectively
stopping at Derived1/14/21 after226/239/248 completed requested commands. Each
subsequent run was justified by recorded newly available source/toolchain/
configuration-keyed package outputs, not by changing tests or limits. Derived7
and17 alone took175s/166s; these are build-time measurements, not proof failures.
The largest sampledRSS among these failures was11642351616, below12GiB;
cgrouppeak is null on interrupted runs and is NOT inferred from RSS.

Fresh634358-b1856fc6 PASS23.096s includes actual KeySort2jobs and377taclets,
131read-bearing/131covered; original executable SHA11eb6e37ff937d79901cb0072027ff3f9382552d7f65b421078934dadb6d216b
preserved. Fresh output executable SHAa6cce6c2d7283a7b8faa1da2873baba12537744ad592d63ad36d8cde5b47f458.
That run precedes only two fixture-proof additions: its GLOBAL fingerprint is
historical, while its entire closed sort-source input set remains byte-identical
to current. The final evidence records this distinction explicitly; it is not
an all-source/default-build or literal-wrapper pass. All current builds used
empty LAKE_CACHE_DIR and LAKE_ARTIFACT_CACHE=false inside Docker;1365preserved
optional cache entries remain, with no worker cleanup or copied toolchains.

The initial static driver failed because direct node check-trust lacked its
required NUL file list; its exit1/full stderr are retained. Supported
bash scripts/check-trust.sh passes909sources/241sites/0findings. Final source
binding,15corruptions, strict491automatic/61step-budget/11refuted/0pending,
169core/0elaborator,894reachable/0orphan/0disallowed are separate scoped gates.
Raw task/base docs remain exit1 with identicalFULL72findings (46missing plus
26ambiguous), and global pins exit1 with identical14StorageSlots notes; both
separate NEW0 comparisons pass, neither raw gate is relabeled green.

No unchanged Decision/full retry occurred. Full496841-193e914c and isolated
task413142/exactbase433573 remain FAILED125; default-build/Suite suffixes in
that full run were unreached. Current mandatory full and literal run-lean
confirmation remain unresolved. Existing blocked goal was not changed;
get_goal and Lean MCP diagnostics are unavailable. Final artifacts and
independent artifact reviews are recorded in the new owning handoff at
/workspace/v08-world-lowering-artifacts/checkpoint-creation-success-20261030.
Every original Work/Backfill source queue and reserved dependency stays partial.


## Arbitrary finite transaction prefixes (2026-10-30)

Starting head5f2651bf6be91ecf2f29b57482a28dbe0083964e; same frozen base/branch/VM.
Existing Transactions laws cover at most two boundary applications; the missing
arbitrary-prefix/history clause is now proved in TransactionPrefixes and
inhabited in PrefixControls. The only execution in the ordinary List.foldl
step is existing World.transact. Accumulator is the existing intrinsic World
paired with its ordered List(TRes alpha), not another state/value/interpreter.
There is no public length/depth cutoff or Source-execution claim.

Fourteen general laws prove cons/singleton/append/snoc, exact history length,
input/output reset and normalization at every nonempty boundary, plus
per-frame success/failure and a failed transaction followed by arbitrary suffix.
The failure premise reads the ACTUAL reached prefix world's reset input.
Its conclusion preserves the previous committed reset world and exact THalt,
appends the error to all earlier statuses, then executes the remaining suffix.
Empty prefixes deliberately retain the dirty initial world; this distinction
is tested, not hidden in a normalization premise.

Twenty-seven concrete laws use successive actual operations: funded constructor/
library commit; real ordinary1 paid body failure with encoded binary reason
[0x6c,0,0xff,0x48] AT THE POST-COMMIT INPUT; real occupied-candidate create
failure with plain revert AT THAT SAME REACHED SNAPSHOT; real caller/other/
candidate reads after both failures. The two failure equations are independently
kernel checked at linked.resetTransient, never transplanted from base-world
failure. Existing result values are losslessly tagged in nested standard Sum:
full library bytes/context, Unit, typed Handle false and List Int respectively.

The ENTIRE previous extended vector is kept at every prefix: balances
[sender,caller,library,other,candidate]; caller/other persistent+transient cells;
installed empty-library fields; every old installation/type-lookup/role flag;
candidate typed cells/lookup. Empty input has balances95/0/0/5/0,caller0/0,
other19/29,candidate absent. All nonempty reached boundaries have balances
88/7/0/5/0,caller11/0,other19/0,candidate8/0 installed,library installed/empty.
History is exactly [ok tagged full library([b1,b2],[1,7,2,7,12345]),
error encoded binary reason,error plain revert,ok tagged[11,0,19,0,8,0]].
Initial/one/multiple-prefix append controls, arbitrary suffix-after-failure,
dirty direct reads observing23/12, wrong ancestor snapshot, wrong halt and
swapped-status negatives are checked. Empty dirtyother29 differs from reset0.

Current standalone focused target PrefixControls imports the unchanged prior
Audit plus both new modules, printing all357 preserved sets and41 new sets:
398exact standard axiom sets. Old Audit source is byte-identical to starting
head; no import cycle/core-to-elaborator edge is introduced. Additional core
closure registration in the lane checker covers TransactionPrefixes. Nineteen
external corruption controls preserve all15 old cases and changed/missing
source cases for both new modules. No old theorem or fixture was removed.

A measured operational correction was necessary. Initial free658808832bytes
was enough for the conservative64MiB proof/evidence estimate, but two NEW
bounded gate containers consumed about352MiB: Docker uses vfs and retains
independent base-filesystem copies. Optional artifact count stayed1365.
Both raw failed gates717877/718396 remain; no source/cache/container/evidence
was deleted and no capacity/resource limit changed. Default sandbox read-only
append-lock/socket inspections failed; corrected read-descriptor lock and
approved local Docker inspection worked. These are operational invocation
errors, not theorem failures.

New scripts/v08-reuse-prefix.py reuses ONLY this turn's owned, unsealed failed
container718396: same ID,unchanged configured command/all67 explicit targets,
image,user,mounts,networknone,12GiB/no-swap,CPU1,cacheflags and Lean-j1. Selected
nonsecret before/after inspection is retained with unique new logs; seed JSON
and raw-log SHA remain unchanged. The final existing PrefixControls target
resolves the116-module current import closure. Its49 added prior-Audit imports
are bound to successful704511 source/config/toolchain/raw-log validation and
unchanged output/trace/setup files predating that run, with newly recorded
SHA/size/ctime and trace-output/hash agreement. These SHAs are new forensic
snapshots, not hashes claimed to have been captured historically by704511.

Independent finder identified the initial .olean-existence-only evidence gap;
it was fixed before any restart. Both finder and skeptic reviewed the stronger
guard and actual controls without Lean/server/builds. Reuse720591-bf21fe57
passes117jobs in32.169s with all398 sets, fresh sampledRSS1017917440 and
reported cgrouppeak365793280 (conservatively possibly cumulative on reuse).
Same containerID and0 writable-root bytes before/after; only about2MiB disk
increment, no new filesystem copy. All original monitor/time/memory/OSheadroom/
token-cleanup logic remains; only create->start and container identity plumbing
change. Full current-closure and previous-explicit-command lists are separate
evidence. A corrected external inspector harness tests14 corrupt profiles
after accepting a positive profile; its initial ad-hoc missing-fmt NameError
is retained in terminal history and is not classified as a helper failure.

Every G20,G21,G22.01-.05,G23 and BackfillA/B SOURCE/application queue stays
PARTIAL. No Source/V07/type/layout/ABI/body/linkage/runtime-frame/bytecode/
precompile or arbitrary callback relation is supplied. The original goal stays
blocked/untouched; get_goal and Lean MCP diagnostics remain unavailable.
Mandatory full496841/taskDecision413142/baseDecision433573 exit125 are retained,
with no unchanged retry. Literal-wrapper confirmation remains pending.
Global docs/pin raw exits1 stay failed; only complete exact-base NEW0 comparisons
may pass. Existing Suite705959 and fresh634358 evidence is retained only for
its unchanged closed source dependencies, not a new global source fingerprint
or whole-lane/source/runtime proof. Further independent obligations are not
claimed exhausted. Proposed G03 localEvidence additions: BackfillB prefix laws
and G22.03-.05/G23 intrinsic examples only, no global status/ledger rewrite.


Finite-prefix checkpoint gates complete: prefix-binding.log398pins/60coreclosure;
prefix-controls.log19corruptions;prefix-reuse-controls.log14corruptprofiles;
trust911sources/241sites/0findings;strict491automatic/61step-budget/11refuted/
0pending;layers169core/0elaborator;orphans896reachable/0orphan/0disallowed.
Full current docs/pin raw exits1 retained with72/14 complete exact-base rows
identical and separate NEW0 passes. Current public law count41 (14general,
27controls), all357previous axiom sets unchanged. Both independent actual
proof/control/reuse-protocol reviews pass after the warm-artifact finding was
fixed; no Lean/server/builds by reviewers. Source/mandatory-full obligations
remain open. Original storage estimate omitted VFS container copies; repaired
reuse incurs only small output/log growth without any deletion or cap change.
This committed section is the handoff for this first prefix checkpoint.


### Prefix observation extension checkpoint

After committed first prefix checkpoint b010202f46208b60682f37f12a5114c9711c9d01,
the next independent BackfillB clause is now proved: transact_prefix_observe
lifts existing transact_observe to arbitrary finite lists, preserving exact
world and every ordered error while mapping successful values. An arbitrary
observation need not be injective; no generic losslessness is claimed.
Concrete extendOutput pairs EACH WHOLE ORIGINAL typed Sum value with its size;
observed_complete retains the ENTIRE extended world vector and allfour statuses,
and observed_recovery removes ONLY the added Nat to recover the exact original
ordered history, including both real failures and full return bytes/context.
These consume the actual constructor/library/postcommit failure/collision/read
runs already checked, not a Source preservation hypothesis or another evaluator.

Gate726724-3deff8c6 passes the same117-job/116-module focused closure using the
same unchanged67-command owned-container configuration. The raw gate records
actual fresh RSS,reported reused cgrouppeak(possiblycumulative),exact tool
versions,source/config hashes,before/after identity/resource/mount checks and
zero writable-root bytes. Forty-four new theorems now give401standard sets;
all398 first-stage,357previous,322earlier and original276 sets are unchanged.
The first398 result remains stage evidence, not a current global fingerprint.
Both read-only finder/skeptic observation-law reviews pass with no findings.
The new general law is not Source/body/ABI/runtime/bytecode lowering. Every
original group and Backfill source application remains PARTIAL; all mandatory
full/Decision/rawglobal failures and literal-wrapper pending boundaries persist.
This section records the second checkpoint's committed handoff; current final
script gates, exact statuses, both checkpoint heads and sealed artifacts are
also recorded in the final owning handoff. No further independent work is
claimed exhausted or goal complete.


### Indexed finite-history locality checkpoint

Starting committed d3dd46928f7bd1e84eff82ec77e3a8a53bdddde7, the missing
Backfill B indexed clause is now proved over the ACTUAL existing transaction
fold. transact_prefix_index_bound derives every history bound from the exact
frame-list length. transact_prefix_index identifies the full TRes at any valid
index with World.transact applied to that frame at the world reached by take i.
The success/failure clauses require only the actual indexed frame equation at
that reached reset input, retain the full typed value or exact THalt, and prove
the immediately following boundary world. They do not assert that later frames
leave that world unchanged. take_history and drop_history preserve complete
ordered earlier results and run the suffix at the actually reached world.
Take/drop are total beyond length; indexed access requires a proof of validity.
Empty prefixes retain dirty input. No evaluator, Source relation, cutoff or
whole-trace preservation assumption was added. Indexed observation extension
maps success values at the same index and retains exact errors.

Controls instantiate positions0/1/2/3 of the actual funded constructor/library
commit, post-commit paid binary-reason failure, occupied candidate failure and
real reads. indexed_complete_vectors retains EVERY previous listed balance,
store, transient, installation/kind/role/lookup observation at boundaries0..4
and all exact typed result/status values. The vector is not every World field.
Middle and outofrange locality and wrong-index, shifted-success, wrong-suffix-
order controls discriminate the actual runs. Existing dirty/snapshot/error
controls and all401 prior axiom sets are preserved. Twenty new theorems give
421 standard exact pins. Finder and skeptic independently read the actual
proofs/controls without Lean/server/builds and reported no substantive findings.

Gate738526-2cf27af0 passes117 jobs in34.9364s; fresh RSS1022394368,
reported reused cgroup peak371789824 (conservatively possibly cumulative).
It reuses only the exact inspected stopped d07aa75f runtime, without allocating
another VFS root, changing commands/guards or deleting any file/cache/container.
48MiB conservative incremental budget at282943488 available bytes; actual
remaining space before sealing will be recorded. The inner max12GiB/swap0,
CPU1, cacheempty/false and serial-j1 checks remain unchanged. Initial list proof
failure733295 and concrete unification/heartbeat failure735448 exit1 are retained;
explicit list rewriting fixed them without budget increases. Failed-build
printed sorryAx comes from Lean error recovery only: no authored sorry/axiom
and none in the successful421 sets. Per-file MCP/get_goal remain unavailable.

Every original G20,G21,G22.01-.05,G23 and BackfillA/B source/application parent
remains PARTIAL, with Source/V07/type/layout/ABI/body/linkage/runtime-frame/
bytecode/admission/reserved-owner applications open. Mandatory full496841 and
task/baseDecision413142/433573 failed125 remain; no unchanged retry or waiver.
Literal run-lean wrapper remains pending. Raw global docs/pins exits1 are
retained separately from complete exact-base NEW0 comparisons. No other
independent obligation is claimed exhausted and the existing goal stays blocked.
This section is the committed checkpoint handoff; additive exports record
all exact heads, complete queues, gates, reviews and checksum evidence.

Checkpoint final script gates:421 exactpins/60coreclosure;19 evidence corruptions
and14 runtime profile corruptions rejected after positive controls; trust911/
241sites/0findings;strict491automatic/61step-budget/11refuted/0pending;
layers169/0elaborator;orphans896/0orphan/0disallowed. Raw task/base docs exits1
have identical complete72 findings; raw globalpin exits1 have identical14 notes.
Separate NEW0 comparisons pass, without waiving either rawfailure. Both final
independent read-only proof/control/inventory reviews pass. Remaining disk before
commit271130624bytes, within the measured48MiB incremental envelope.


### Retrospective indexed error checkpoint

After d33c3ce2d4f10d9c71977f9f956fbfa78731efb3, a further independent
Backfill B clause is proved: transact_prefix_failure_of_index consumes ONLY an
exact recorded indexed error and validindex, derives the actual frame error at
the reached reset input by cases on published World.transact, and proves the
immediate rollback snapshot. transact_prefix_index_error_iff establishes both
directions. No frame execution equality or whole source preservation premise is
assumed in the converse. Populated paid/collision history reconstruction controls
consume the previously checked actual indexed histories; these are derived
reconstructions, not independent external observations or new Source executions.
All prior vectors/results/pins retained; four new theorems give425 standard sets.

Gate749814-1701c3a7 passes117jobs/33.7169s, freshRSS1027612672, reported reused
cgrouppeak380309504(possiblycumulative). The initial dependent-case target error
749303 exit1 is retained; fixed by using the already rewritten case target,
without statement or budget changes. Finder/skeptic independently reviewed the
actual converse hypotheses and controls read-only with no findings/builds.
Same checked bounded runtime/cache identity and unchanged commands/limits; no
container allocation, deletion, capacity change or Decision/full retry.
Every original Work/Backfill source/application parent remains PARTIAL; missing
Source/V07/ABI/layout/body/linkage/runtime-frame/bytecode/admission/owner
applications and mandatory full/Decision/literal-wrapper boundaries stay open.
Final scoped checks and raw-vs-NEW0 outcomes accompany the additive sealed handoff.

Retrospective checkpoint final gates pass425exactpins/60coreclosure,19evidence
and14runtime-profile corruption controls, trust911/241/0findings, strict491/
61budget/11refuted/0pending, layers169/0elaborator,orphans896/0orphan. Raw global
docs/pins task/base exits1 retained with complete72/14 rows identical and
separate NEW0 passes. Both final independent proof/control/evidence reviewers
pass with no findings; no Lean/server/builds by reviewers. Source/application
and mandatory whole-gate blockers remain exactly as recorded above.


### Successful indexed-history reconstruction checkpoint

Starting ac9ef3be33a1b87a1d4fa008159682a62e151b1d, the missing success
counterpart is now proved. transact_prefix_success_of_index assumes ONLY a valid
index and exact typed.okvalue in the actual transaction history. Cases on the
published World.transact/frame return derive existence of an actual RAW next
world returned by that frame at the reached prefix reset input, with only its
resetTransient equal to the immediate(i+1)boundary. index_ok_iff gives both
directions. No raw=normalized, later/finalworld, arbitrary worldfield or Source/
ABI/bytecode inference follows from a successful value. All halt distinctions
remain unchanged. The ordinary intrinsic fold/types/semantics are unchanged.

Concrete commit/read reconstructions consume actual funded constructor/library
and finalread history entries. reconstructed_complete_boundaries retains EVERY
old balance/store/transient/installation/kind/role/type lookup observation at
all0..4 boundaries and ALL ordered statuses (including both distinct errors)
and full typed result values. Wrongbinarysuccess bytes discriminate same-tag
values, and wrong_raw_reset_world checks actual dirty raw linked transientcells
against its committed reset snapshot. Existing shiftedindex/order and dirtyempty
controls preserved. Seven new checked theorems give432 standard exactpins with
all425 prior sets unchanged. These are derived intrinsic history reconstructions,
not independent Source/external observations. Both finder and skeptic reviewed
the actual statements/premises/controls read-only, without Lean/server/builds,
and found no substantive issue.

Gate760938-beadbc03 passes117jobs in37.0845s, freshRSS1026854912 and reported
reusedcgrouppeak381874176(possiblycumulative). Same stoppedowned runtime/image/
CMD/mount/token/cache/config checked fresh; parent16GiB,inner12GiB/swap0/CPU1,
LEAN_NUM_THREADS1/Lean-j1 and600s unchanged. No container allocation, deletion,
capacity/guard/proofbudget change. Actual affected compiledoutput1035226bytes;
initialfree254799872 with conservative40MiB entirecontinuation envelope and
expectedremaining212856832bytes. Fresh budget/preflight evidence retained.
PerfileMCP/get_goal unavailable; existing blockedgoal untouched.

Every original G20,G21,G22.01-.05,G23/BackfillA-B application parent remains
PARTIAL. Source/V07/type/layout/ABI/body/linkage/runtimeframe/bytecode/admission/
reservedowner applications open; no independentqueue exhaustion claimed.
Mandatoryfull496841/taskDecision413142/baseDecision433573 FAILED125 retained;
no unchanged retry/waiver. Literalwrapper remains pending. Raw globaldocs/pins
failures and complete exactbase NEW0 comparisons remain separate. This section
is the checkpoint handoff; exact final scopedgates and additive artifacts follow.

Successcheckpoint final scopedgates PASS432exactpins/60coreclosure,19evidence
corruptions+14runtimeprofiles afterpositivecontrols;trust911/241/0findings,
strict491/61stepbudget/11refuted/0pending,layers169/0elaborator,orphans896/0.
Rawtask/base docs/pins exits1 retained, complete72/14 findings identical and
separateNEW0 passes. Both finalindependent reviews PASS/no findings. Remaining
space247001088bytes beforecommit, within40MiBcontinuation envelope. Wholelane
and mandatoryvalidation remainunfinished; nextmiddle-segment clause continues.


### Arbitrary middle-segment history and snapshot checkpoint

Following0a593f0e856e65e29304984054e548d52ab41249, six further general laws
prove exact middle history, endpoint, completepair, localindexbounds and local
success/error iff. Segment execution is ONLY existing transactPrefix of
(frames.drop start).take count at the ACTUAL world reached by frames.take start.
The endpoint equals the actual fullprefix(start+count)world; the complete ordered
middlehistory is history.drop start.take count. Arbitrary Nat start/count permit
natural truncation and emptysegments, with no publiccap. Localindices require a
proof against actualtruncatedsegmentlength, yielding a proved historyslicebound.
The two-sided local success/error observations reconstruct actualframes at
actual localprefix reset worlds; only rawsuccess.reset equals immediateboundary,
and exact THalt/rollback are preserved. No wholetrace preservation assumption,
extra reset, evaluator, raw=normalized/laterfinalworld or Source claim.

Nine populated controls run the genuinely reached post-constructor/library
middle segment: paidbinaryreasonfailure,occupiedcandidate plainrevert,then real
read. Both exacterrors/fulltypedread stay ordered. middle_complete_vectors
retains EVERY previous listed observation and orderedhistory at all0..4 original
boundaries plus the complete middleendpoint vector/history. Emptyatdirtybase is
not reset; emptyatreachedcommit stays there; start7/count12 truncates naturally.
Wrongorder and wrongbase snapshot distinguish actual runs; existing wrongsuccess
bytes/rawreset/shiftedindex/dirtycontrols and all432 earlier pins remain intact.
These reconstruct supplied intrinsicframe executions, never Source execution.

Gate775603-bac38803 passes117jobs/34.2515s,freshRSS1047134208,reportedreusedpeak
399007744(possiblycumulative). Fifteennewtheorems give447standardexactsets,
all425 starting sets unchanged. Initial771685 failed1 at unchanged200000HB in
concreteproof unification;774087 failed1 on dependentindex rewrite. Explicit
history factoring/dependent-safe simp and emptylistsimplification fixed these
without changing statements or proof/time/resource budgets. Rawfailures retained;
no authoredsorry/newaxiom and no sorryAx in successful447sets. Finder/skeptic
independently reviewed actual general/local laws and inhabited/fullvector/negative
controls read-only,withoutLean/builds,with no substantivefindings.

Sameexistingboundedruntime/config/image/CMD/token/mount/cache/cgroupchecks,
noVFSallocation/deletion/capacitychange. Initialfree254799872,40MiBconservative
entirecontinuation budget; actualfinalgrowth measured in additive seal.
AlloriginalWork/Backfillsourceapplicationparents stayPARTIAL,goalblocked/untouched,
no independentqueue exhaustion claimed. Missing Source/V07/type/layout/ABI/body/
linkage/runtimeframe/bytecode/admission/reservedowner applications remain explicit.
Mandatoryfull/Decision FAILED125 and literalwrapperpending remain; none waived.
Actualforensics and current wrappers were reinspected: no Decisionoutput/trace,
most exactbaseisolatedbudget aftersetup; cache/startup reuse does not demonstrate
a repair ofdominantelaboration. No unchangedretry/owneredit/async/target/guard/
budgetchange. Current run-lean requires defaultbuild first; check-solkey refresh
removes generatedbinary, so historical isolatedfreshsort is not a literalwrapper
pass. Operationalmechanism repairs do not imply completedmandatoryvalidation.

Middlecheckpoint final scopedgates PASS447exactpins/60coreclosure,19sourcebound
evidencecorruptions and14runtimeprofilecorruptions afterpositivecontrols;
trust911/241/0findings,strict491automatic/61budget/11refuted/0pending,
layers169/0elaborator,orphans896/0orphan. Rawtask/base docs/pins exit1 stayfailed;
complete72/14 findingrows identical and separatelynamedNEW0 pass. Both final
independentproof/control/sourcebinding reviews pass with nofindings. Remaining
space235712512bytes precommit, inside40MiBcontinuationenvelope. Alloriginal
source/applicationqueues and mandatoryvalidation remainunfinished.


### Injective complete-history reflection checkpoint

Starting f9088913b5fb1cb6594f8eeccfc836d625addebd, six new general laws
reflect exact TRes and ENTIRE ordered histories under an EXPLICIT injective
typed success observer. Every THalt/error/success distinction and list order is
retained. Actual observedprefixhistories reflect originalprefixhistories, even
between different initialworlds/frame lists, but imply NO World equality or
Source/ABI equivalence. Segment complete/history/reflection corollaries preserve
the genuinely reached prefixworld and exact endpoint, natural truncation/empty
behavior, all ordered successes/errors. The premise is observerinjectivity,
never a relation assuming desired preservation. Existing intrinsicfold unchanged.

Eight controls prove actual extendOutput injectivity (wholeoriginaltypedvalue
retained), full/middle history reflection, and all previous listed vectors and
ordered results at ALL0..4 boundaries. Same-taglibrarybinary bytes/context,
fullread and both exact distinct errors retained. A lossyconstant-success observer
merges actualhistory with a wrongbytecandidate despite their inequality; stronger
lossy_actual_runs compares two ACTUAL World.transactfolds using pure result
adapters on the same funded operations/worlds. Their rawhistories differ but
constant-success observedhistories coincide. Neither is claimed an independent
Source execution or source-equivalent program. Wrongbyte/order observations are
rejected by injective reflection. Existing rawreset/emptydirty controls preserved.

Gate788245-4ed664a2 PASS117jobs/37.5548s,freshRSS1028800512,reportedreusedpeak
381345792(possiblycumulative);461 exactstandardsets preserve all447startingpins.
Initial786593 FAIL1 was a concrete listtypeannotation, fixed without statement/
budget change. No authoredsorry/newaxiom or nonstandardaxiom in successfulsets.
Same stoppedownedruntime/image/CMD/token/mount/config/cache checkedfresh; inner
12GiB/swap0/CPU1,parent16GiB,serialLEAN_NUM_THREADS1/Lean-j1,600s unchanged.
No newVFSroot/deletion/capacity/guardchange. Initialavailable227966976; measured
changedcompiled1192401bytes; conservative32MiB totalgrowth envelope leaves at
least194412544bytes. Runtimepreflight/budget evidence additive. get_goal/LeanMCP
unavailable; existingblockedgoal untouched. Independent finder/skeptic readactual
proofs/controls without Lean/builds/writes and found no substantive issue.

All original G20,G21,G22.01-.05,G23/BackfillA-B source/applicationparents remain
PARTIAL; no independentqueue exhaustion claimed. MissingSource/V07/type/layout/
ABI/body/linkage/runtimeframe/bytecode/admission/reserved-owner applications open.
Mandatoryfull496841/taskDecision413142/baseDecision433573 FAILED125 remain,
literalwrapperpending; no unchangedretry/waiver. Raw globaldocs/pins exits1 and
complete exactbase NEW0 comparisons remain separate. This is the committed
checkpoint handoff; scopedgate results and exact artifacts follow.

Reflectioncheckpoint final scopedgates PASS461exactpins/60coreclosure,19evidence
and14runtimeprofile corruptions afterpositivecontrols;trust911/241/0findings,
strict491/61budget/11refuted/0pending,layers169/0elaborator,orphans896/0orphan.
Rawtask/base docs/pins exits1 remainfailed, complete72/14 identicalfindingrows
and separatelynamedNEW0 pass. Both finalindependentproof/control/pins/doc reviews
PASS/no findings. Precommitavailable218337280bytes inside32MiBenvelope; next
adjacentsegmentcomposition continues. Alloriginalsource/applicationparents and
mandatorywholevalidation remainunfinished.


### Adjacent naturally truncated segment checkpoint

After f02e01669ffad2cd8976627c56df82a6eb151a86, four general laws derive
actual adjacent subdivision, complete orderedhistory subdivision, forwardmapped
observation (noinjectivityneeded), and reflection of BOTH labelled component
histories under explicitinjectivity. Secondsegment starts at actualprefix
(start+left)world, even when lengths truncate or a segment is empty. No public
length/depth cap or evaluator. Exact errors/order/fullsuccesses retained.
Reflection of only concatenation never identifies partitionboundaries/Worlds.

Ten populated controls instantiate the genuinely reached postcommit split into
actual paidbinaryfailure followed by actualplainfailure/read; retain EVERY old
listedvector and orderedhistory at ALL0..4 boundaries; and explicitly apply both
new generic subdivision/observation laws. Labelledreflection preserves BOTH
componenthistories. Wrongpartition distinguishes empty/shiftedfirstcomponents.
ambiguous_partition_concat proves SAMEENTIREconcatenation with different labelled
firstcomponents AND actualprefixsnapshots (dirtybase vsfundedcommittedworld).
Emptyfirstpartition precedes fullactualtrace without addingreset; overlongfirst
segment naturally consumes only remainingframes and secondsegment empty atactual
finalsnapshot. Existingrawreset/dirtyinput/successbyte/errorcontrols retained.

Independentfinder/skeptic identified two evidence gaps: explicit actualapplications
of the newlaws missing, and wrong_partitioncomment claimed equalconcatenations
beyond its statement. Both fixed: explicit inhabited applications added, original
comment narrowed, separate complete ambiguouspartitionwitness added. Both reviewers
accepted fixes read-only withoutLean/builds/writes. No theorem/premise weakened.

Gate802903-f0c31091 PASS117jobs/39.2770s,freshRSS1068470272,reusedreportedpeak
413327360(possiblycumulative);475standardexactsets preserve all461prior/447starting
entries. Raw799016/801042FAIL1 at unchanged200000HB in concreteempty-inputproof
retained. Explicit inputequality and rewriting the knownboundary theorem fixed
unification without statement/budget changes; no authorsorry/newaxiom andnone
in successfulsets. Same boundedruntime/cache/config/commands/cgroupidentity,
no newVFSroot/deletion/capacity/guardchange.32MiBentirecontinuation envelope.

Every original G20,G21,G22.01-.05,G23 and BackfillA/B sourceapplicationparent
remainsPARTIAL; no independentqueue exhaustion claimed. Source/V07/type/layout/
ABI/body/linkage/runtimeframe/bytecode/admission/reservedowner applications open.
Mandatoryfull496841/taskDecision413142/baseDecision433573 FAILED125 and literal
run-leanpending retained. Fresh321dependency comparisons show no changed Decision
input; no output/trace and no supported distinct repair. No unchangedretry,
target/verdict/async/owner/budgetchange or baselinewaiver. Raw globaldocs/pins
exits1 remainfailed, separate complete exactbase NEW0 comparisons only.
This is the committed checkpoint handoff; finalscopedgates/artifacts follow.

Adjacentcheckpoint final scopedgates PASS475exactpins/60coreclosure,19evidence
and14runtimeprofilecorruptions afterpositivecontrols;trust911/241/0findings,
strict491/61budget/11refuted/0pending,layers169/0elaborator,orphans896/0orphan.
Rawtask/base docs/pins exits1 remainfailed; complete72/14findingrows identical,
separatelynamedNEW0 pass. Both finalindependentproof/control/pins/doc reviews
PASS/no findings after evidencegap fixes. Precommitavailable207007744bytes,
inside32MiBtotalcontinuation envelope. Measuredcompact additiveexports follow.
Alloriginalsource/applicationparents and mandatorywholevalidation unfinished.


### Reachable-input frame and segment replacement checkpoint

Starting ca7fa9da632a6a7d37823ea44c2afc27c078aae3, the missing list/contextual
congruence is now proved. Equal-length lists require INDIVIDUAL COMPLETE rawframe
TRes(World x typedvalue) agreement ONLY at each LEFT execution's actual reached
prefixworld.resetTransient. This explicit premise is stronger than normalized-
result agreement; neither globalfunction equality, source adequacy nor wholetrace
preservation is assumed. Induction derives exact World AND COMPLETE orderedTRes
history equality for EVERY finiteprefix, incl naturaltruncation/empty. Full-list,
localizedframe and localizedsegment corollaries retain arbitrary precedinghistory
and arbitrary subsequentexecution at the reachedworld. No cutoff/newinterpreter/
state layer or raw=normalized identification. Perframepremises stay obligations.

Fourteen controls use existing fundedconstructor/library/paidbinaryfailure/
occupiedcreate/plainfailure/read fixture. paidReplacement selects actualpaidcall
when candidate installed, otherwise actualcreate. Perframeagreement is established
at actualpostcommitreset, not base ordirtyworld; general everyprefix and actual
middleframe/segment theorems instantiated directly. Full listedvector/history at
ALLold0..4 boundaries and everyreplacedprefix retained, including bothfullsame-tag
success bytes/context/readvalue and exactbothorderederrors. baseOnlyReplacement
agrees atoriginalbase yet producesplainrevert at reachedinput instead ofbinaryhalt.
dirtyOnlyReplacement agrees atrawlinkedworld yet likewise fails at resetinput.
No arbitrary inventedworld or callinterpreter; guards read existingtypedworldcells/
accounts and branches invoke actualpublished operations. No Source execution claim.

Gate814624-7aaf3c68 PASS117jobs/39.9992s;493standardexactpins retain475starting
entries. Initial814065FAIL1 from owninsertionanchor matchingthreeprintprefixes,
plus indexedfunction parentheses; removed ONLYgenerated duplicates with an exact
base+addition assertion and parenthesized indexedframe, no oldcommittedtext lost.
Rawfailure retained; no authorsorry/axiom and no nonstandardaxes in successfulsets.
Both independent finder/skeptic reviewed actualpremises/nonvacuity/fullobservations
read-only withoutLean/server/builds/writes, no substantivefinding. Rawworldpremise
must not be marketed as merelyobservational agreement. Nextprecisenormalization
clause remains separate. get_goal/LeanMCPunavailable,blockedgoaluntouched.

Same existing checked boundedruntime, no allocation/deletion/capacitychange;
12GiB/swap0under16GiBparent,CPU1,LEAN_NUM_THREADS1/Lean-j1,600s and allproofbudgets
unchanged. Initialavailable199041024; affectedcompiled1444171;32MiBentiregrowth
envelope leaves at least165486592. Fresh preflight/budget evidence retained.
Every original G20,G21,G22.01-.05,G23/BackfillA-B parent remainsPARTIAL, Source/
V07/type/layout/ABI/body/linkage/runtimeframe/bytecode/admission/reservedowner
applications and mandatoryfull/Decision/literalwrapper gates open. No independent
queueexhaustion claimed; no unchangedfailedmandatoryretry or baselinewaiver.
Rawglobaldocs/pins exits1 and complete exactbase NEW0 comparisons separate.
This section is the checkpoint handoff; scopedgates/additiveartifacts follow.

Rawreplacement checkpoint final scopedgates PASS493exactpins/60coreclosure,
19evidence+14runtimeprofilecorruptions afterpositivecontrols,trust911/241/0findings,
strict491/61budget/11refuted/0pending,layers169/0elaborator,orphans896/0orphan.
Rawtask/base docs/pins exits1 retained, complete72/14 findingrows identical and
separateNEW0 passes. Both finalindependent reviews PASS/no findings. GatefreshRSS
1133637632,reusedreportedpeak516050944(possiblycumulative). Precommitavailable
190365696bytes inside32MiBenvelope. Originalsource/application/mandatorywhole
obligations unfinished; next independentprecisenormalization clause continues.
