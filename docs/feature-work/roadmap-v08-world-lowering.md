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
Checkout: VM location `v08-world-lowering-pinned`.
The VM's original `solidity-lean` checkout stays on `work` at
`204eb1545cbf57e436196e4cba346075515b7279`; `bridge-theorems` is preserved.
The exact-SHA fetch from the existing GitHub origin succeeded, and its original
checkout FETCH_HEAD equals the base. A separate worktree was created from it.
FETCH_HEAD is worktree-local: querying it in the new worktree fails; the raw
failed query is retained, alongside verification in the original checkout.

Installed tools were discovered below VM location `.setup/tools` rather than
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

Evidence directory: VM location `v08-world-lowering-evidence`.
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
VM location: v08-baseline-pinned. An initial baseline attempt was intentionally
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
VM location: v08-world-lowering-artifacts/handoff.md. No parent group is complete.

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
VM location: v08-world-lowering-artifacts/metadata-checkpoint.md and .patch.
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
head/patch are saved at VM location: v08-world-lowering-artifacts/projection-checkpoint.md
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
head/patch: VM location: v08-world-lowering-artifacts/selector-emit-checkpoint.md
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
and patch are saved at VM location: v08-world-lowering-artifacts/crypto-checkpoint.md
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
VM location: v08-world-lowering-artifacts/header-checkpoint.md and .patch.
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
VM location: v08-world-lowering-pinned. Entire frozen assignment remains PARTIAL;
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
in VM location: v08-world-lowering-evidence/feature-ids.json. G20 evidence maps to
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
full evidence archive and SHA256SUMS are at VM location: v08-world-lowering-artifacts.
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
VM location: v08-world-lowering-artifacts/checkpoint-nested-20261030 and
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
VM location: v08-world-lowering-artifacts/checkpoint-handler-20261030. Prior64-entry
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
supported --solkey root VM setup: solkey/keyext.solidity.examples was then
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
VM location: v08-world-lowering-artifacts/checkpoint-library-handler-20261030;
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
VM location: v08-world-lowering-artifacts/checkpoint-library-handler-final-20261030.
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
VM location: v08-world-lowering-artifacts/checkpoint-creation-success-20261030.
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


### Precise completed-frame normalization checkpoint

Following c91b4af318f4f35249b4cea7e81a0b1502774736, four separate general laws
prove normalized-result congruence at actualreachedresetinput, a completed-frame
outputadapter, exact fullprefix normalizationtransport, and localizednormalized
replacement. Normalizedpremise maps ONLY successful returnedWorlds through
published resetTransient and retains exacttypedvalue/errorTHalt. It permits
unequalRAWworlds; only completepostresetWorlds/results must agree. Casing the
actual published World.transact proves this step explicitly. The adapter applies
ONLYafter a suppliedframe has completed at an outertransaction boundary, never
inside an unfinishedinternalcall/frame. Emptyfold retains dirtyinput; no new
state/interpreter or raw=normalized identification. Rawreplacementtheorems unchanged.

Nine actual controls prove rawcompletedcommit differs from normalization on caller
scratch23->0,candidate scratch12->0 while everyother oldlistedfield and fulltyped
success retained. The real fundedconstructor/library body is unchanged; only its
completedoutput is normalized before World.transact would normalize it anyway.
Everyprefix world/history and everylistedvector preserved; explicit normalized
localizedreplacement instantiated. Actual invalid baseOnlyReplacement instead
runs occupiedcreation at reachedinput: derived bad_trace_reached has identical
completefinalWorld AND lasttypedread to original, but completehistory differs
because binaryhalt replaced byplainrevert. Bothfullsame-tag successvalues and
read/payload/order remain explicit; no terminal-only/state-only premise substituted.
All existing completeold0..4vector controls/negatives retained. These are intrinsic
suppliedbody adapters, not Source/ABI/body/linkage/runtimeframe/bytecode adequacy.

Gate827597-abfc4a74 PASS117jobs/44.2260s,freshRSS1184374784,reusedreportedpeak
552538112(possiblycumulative);506standardexactsets retain493prior/475starting.
Initial825535FAIL1 at unchanged200000HB in concretemap reduction retained;
abstract-world normalize_success helper and congrArg on actualprovedcommit fixed
it without statement/budgetchanges. No authoredsorry/newaxiom/nonstandardaxes.
Both independent read-only reviews of actualhypotheses/nonvacuity/fullobservations
found no issue; no Lean/server/builds/writes by reviewers. Sameexistingbounded
runtime/config/commands/cache/profile, no allocation/deletion/capacitychange.
32MiBcontinuationenvelope; finalcompactexport measured beforewrite.

AlloriginalG20,G21,G22.01-.05,G23/BackfillA-B sourceapplicationparents PARTIAL;
Source/V07/type/layout/ABI/body/linkage/runtimeframe/bytecode/admission/reserved
applications and mandatorywholevalidation unfinished. Goalblockeduntouched,
get_goal/LeanMCPunavailable. No independentqueue exhaustion claimed. Fresh Decision
321dependency sourcecomparisons unchanged, no completedoutput/trace/newpermitted
repair. Retain full496841/task413142/base433573FAILED125 and literalwrapperpending;
no unchangedretry/owneredit/async/target/guard/budgetchange orbaselinewaiver.
Rawglobaldocs/pins exits1 stayfailed; completeexactbaseNEW0 comparisons separate.
This section is the committedcheckpoint handoff; finalscopedgates/artifacts follow.

Normalizedcheckpoint final scopedgates PASS506exactpins/60coreclosure,
19evidence+14runtimeprofilecorruptions afterpositivecontrols,trust911/241/0findings,
strict491/61budget/11refuted/0pending,layers169/0elaborator,orphans896/0orphan.
Rawtask/base docs/pins exits1 remainfailed; complete72/14findingrows identical
and separateNEW0 passes. Both finalindependentproof/pins/sourcebinding reviews
PASS/no findings. Precommitavailable180695040bytes inside32MiBenvelope; measured
compact additiveexports follow. Alloriginalsource/applicationparents and mandatory
wholevalidation unfinished; no independentqueue exhaustion claimed.


### Normalized reached-input arbitrary-prefix and middle-segment checkpoint

Starting0f4d9284965b7e82facc0c7e2096b119b25422a0, four missing normalized
list/context laws are now proved. Equal-length lists require INDIVIDUAL COMPLETE
normalizedrawresult agreement at LEFTexecution's actualreachedprefix.reset input.
Normalization maps only successful returnedWorlds through publishedreset, retaining
fulltypedvalue and EVERY exactTHalt/error. Existing transact_normalized_result_congr
supplies eachinductiveboundary; exact World AND ENTIRE orderedhistories follow
forEVERYfiniteprefix, full-list, contextualpartialsegment and complete middlesegment
with arbitrary before/aftercontext. No equalityofwholetraces as premise, no raw=
normalizedWorld inference, publiccutoff, newstate/AST/interpreter or internalreset.
Perframehypotheses remain explicit proofobligations, not Source/body adequacy.

Thirteen controls use actual fundedconstructor/librarycommit with completedoutput
normalized, unchangedpaidbinaryfailure, normalizedoccupiedplainfailure and real
rawread. Generic everyprefix/full laws directly applied. mixed_complete_boundaries
retains EVERY previous listedbalance/cell/transient/installed/kind/role/type/
candidate lookup observation, fullsame-tagbinarysuccess/context/read and BOTH
exactorderederrors at ALLoriginal0..4 boundaries. mixed_weaker_than_raw keeps
inhabited normalizedagreement together with non-equal RAWcommit views (caller
scratch23/candidate12 vsreset0), not silentrawidentity. Empty mixedprefix remains
dirtybase, not reset. Existingbad_trace_reached and alloldnegatives unchanged.
New normalized_world_only_not_enough proves two ACTUAL reachedtransactionboundary
Worlds identical while fullTRes differ binaryhalt vsplainrevert: state-onlyagreement
cannot replace complete normalizedresult equality. Terminal-onlyagreement remains
explicitly insufficient through existingbadtracecounterexample.

A real read beforeconstruction fails at absentcandidate, providing a NONEMPTY
reachedprefix. Successfulmiddleconstructor/librarywork then bothrealerrors andread
are executed afterit. Generic normalizedsegment law and contextualPARTIALsegment
law are instantiated there for everyprefixcount, includingzero/truncation.
Complete augmentedhistory retains preludeplainerror followed by ENTIRE originalh4.
Finder/skeptic identified missingdirectpartiallawapplication in initialcontrols;
added middle_success_prefixes and bothacceptedcoveragefix. Allsource/hypothesis/
nonvacuity/fullobservations reviewed read-only,noLean/server/builds/writes, no
substantivefindings. No Source/ABI/linkage/runtimeframe/bytecode claim.

Gate841312-91187aee PASS117jobs/41.0881s,freshRSS1233989632,reusedreportedpeak
602947584(possiblycumulative).523standardexactsets retain all506startingpins.
Raw838867FAIL1 reservedlocalidentifierpartial fixedto prefixPart;839468FAIL1
simplifiedTruecontrol fixedwithTrue.intro. Statements/observations/budgets unchanged;
no authorsorry/newaxiom and none in successfulsets. Existingruntime/image/CMD/
token/mount/cache/config/cgroupcheckedfresh, noVFSallocation/deletion/capacitychange.
Inner12GiB/swap0/CPU1under16GiBparent,LEAN_NUM_THREADS1/Lean-j1,600s and allproof/
testbudgets unchanged. Initialavailable172802048,affectedcompiled1763471bytes;
24MiBentirecontinuationplanningbound leavesminimum147636224. Onecoherent checkpoint
and compactadditivearchive measured beforewrite. get_goal/LeanMCPunavailable,
existingblockedgoaluntouched.

EveryoriginalG20,G21,G22.01-.05,G23/BackfillA-B sourceapplicationparent staysPARTIAL.
MissingSource/V07/type/layout/ABI/body/linkage/runtimeframe/bytecode/admission/
reservedowner applications and mandatorywholevalidation remainopen. No independent
queueexhaustion claimed. Full496841/taskDecision413142/baseDecision433573 FAILED125
retained, both321dependencyclosures unchanged/no completedoutput/trace/newpermitted
repair. Literalwrapperpending; no unchangedretry/owner/async/target/guard/budget
change or baselinewaiver. Rawglobaldocs/pins exits1 remainfailed, separate complete
exactbaseNEW0 comparisons only. This is the committedcheckpoint handoff; exact
scopedgates,fullqueue table and additiveartifacts follow.

Normalizedprefix checkpoint final scopedgates PASS523exactpins/60coreclosure,
19evidence+14runtimeprofilecorruptions afterpositivecontrols,trust911/241/0findings,
strict491/61budget/11refuted/0pending,layers169/0elaborator,orphans896/0orphan.
Rawtask/base docs/pins exits1 remainfailed; complete72/14findingrows identical
and separatelynamedNEW0 pass. Both finalindependentproof/pins/sourcebinding
reviews PASS/no findings. Precommitavailable162390016bytes within24MiBenvelope;
streammeasuredcompact additiveexports follow. Alloriginalsource/applicationparents
and mandatorywholevalidation remainunfinished; no independentqueue exhaustion.


## Published prerequisites and actual source execution — 2026-10-31

The original frozen base remains `fb379ae20f10e2c92113453ddd9d40d8f2efbe09`.
This checkpoint consumes only public `origin/master`
`2fe1f8932f96be15b00df03ba2cde46f64a87758`, fetched and checked as its
ancestor's descendant. It contains independent `Source.evalE`/`execS`, machine,
typing/progress and backend scalar/environment components. Earlier statements
that only source journal operations existed describe the frozen base, not this
published revision. V04/V05/V06 remain partial in the published coverage plan;
there is still no published V07 lowering namespace in this tree.

The sealed old checkout VM location `v08-world-lowering-pinned` remains detached
at `e7d2c06046a22cf46ccbcc23882f7e31f429fd53`; its files, caches and sealed exports
are preserved. The assigned branch continues in the separate
VM location `v08-world-lowering-published` worktree. The published merge's three
registration conflicts retain all incoming imports/docs entries and append all
V08 entries. Independent review verified every incoming owner file against the
exact publication. No unpublished branches or owner implementations were taken.

### New actual source clauses

[SourceEnvironment](../../Solidity/Lowering/V08/SourceEnvironment.lean) proves
actual resolved sender/value/timestamp evaluation for every positive horizon and
both pipelines, retaining the COMPLETE source `(locals, St)`, including world,
transient storage, journal, heap, events, logs and function locals. `exec_sender`
executes the actual resolved expression statement. The zero horizon is exactly
`Source.Halt.timeout`; it is not a target revert or a divergence assertion.
Source addresses/words use the existing total numeric adapters. The intrinsic
state is explicitly projected; frame admission and general state/body lowering
are not inferred. Bounded source-word range is proved, not a new premise.

[SourceEnvironmentControls](../../Solidity/Lowering/V08/SourceEnvironmentControls.lean)
uses source balances 93/7, installed identity/nonce, persistent/transient booleans,
three actual journal entries, binary heap contents/events/logs and nonempty locals.
Both pipelines preserve the entire machine. A separate actual paid intrinsic
body writes saved=3/scratch=9 and returns the complete context
`[sender,value,time,self,balance] = [1,7,12345,2,7]`, retaining balances 93/7.
Wrong sender, skipped payment, swapped value/time, maximum-address and timeout
controls discriminate the claims. This fixture supplies a direct declaration
Env and mock global configuration, not an admitted SourceSpec/source-unit or
canonical frame/layout certificate. Its source boolean and target integer stores
are deliberately not identified.

[SourceFailures](../../Solidity/Lowering/V08/SourceFailures.lean) executes the
published source literal-reason builtin and expression statement. For every byte
list and both pipelines, sufficient horizons yield exact `Source.errorData` with
full source-state retention. The existing total byte-layout law identifies this
with `Semantics.encodeError`; actual `Stmt.revertData` returns the exact intrinsic
`revertWith` payload. It introduces no emitter, decoder or replacement semantics.
The n+5/n+6 formulas are sufficient horizons for these finite constructors, not
admission depth cutoffs. Horizon 2 remains timeout. General argument effects,
compiler body selection, catchability, frame rollback and bytecode are not
assumed or claimed by the execution transport conjunction.

[SourceFailureControls](../../Solidity/Lowering/V08/SourceFailureControls.lean)
retains the same populated source machine, tests binary `[0,255,128]`, empty and
33-byte reasons, rejects a wrong byte and empty-reason/plain-revert confusion,
and executes a real paid target call under `World.transact`. Its complete listed
rollback observation is balances/stores `(100,0,0,0)` AND the exact raw `TRes Unit`
error containing the encoded binary reason. Wrong paid snapshot and wrong plain
halt are rejected. Rollback follows this actual enclosing transaction, not from
the existence of a target halt alone.

### Full original queue accounting

| Item | Status | Remaining original applications |
|---|---|---|
| G20 | PARTIAL | Metadata/argument/result/role laws retained. Source declaration/body selection and canonical parameter/result/type/layout, getter/function-reference/readonly applications remain open. |
| G21 | PARTIAL | Actual source literal-reason execution and intrinsic payload transport added. Nested/reference/calldata/slice/custom-error/catch and canonical decoder/layout applications remain open. |
| G22.01 | PARTIAL | Existing actual typed calls retained. Source external/self-call, admission, runtime-frame and bytecode relations remain open. |
| G22.02 | PARTIAL | Existing funded callback/nested rollback laws and full controls retained. General source callback/reentrancy/frame applications remain open. |
| G22.03 | PARTIAL | Constructor/library success/catch continuation and rollback controls retained. Source new/try-new/body/admission applications remain open. |
| G22.04 | PARTIAL | Existing real library caller/context/kind/role controls retained. Source linkage/function-value/storage mapping remains open. |
| G22.05 | PARTIAL | All finite-prefix, exact-history and normalized reached-input laws from e7d2c060 retained. Source/world/runtime/admission composition remains open. |
| G23 | PARTIAL | Actual source environment reads and statement fragment added. General transient/layout, crypto/erased-emit argument execution and G16–G22 composition remain open. |
| Backfill A | PARTIAL | Full previous populated nested/callback/creation snapshots retained, plus actual literal-reason paid rollback. Source frame/layout applications remain open. |
| Backfill B | PARTIAL | All previous signature/ABI/prefix/repeated-reset/constructor laws retained. Source/V07 certificate applications remain open. |

Current `Source.decodeArg` supports memory bytes/strings and dynamic value arrays;
it explicitly refuses unmodelled dynamic shapes. The published coverage plan
still lists calldata references, abi.decode, slices/new/try and source admission
or failure/progress obligations. The old unconstrained `Calldata.objects` issue
must not be substituted for this new evaluator's actual supported interfaces.
Canonical source-to-intrinsic representation and reserved decoder laws remain
necessary. Published `CallsOK` and source body/admission obligations are not
silently discharged. No whole-source/lane theorem or independent-queue exhaustion
is claimed by these component clauses.

### Checks, reviews and mandatory hold

Twenty source-environment and fifteen source-reason laws/controls add to all 523
preserved exact standard axiom sets: 558 total. No new axiom/sorry/native trust
shortcut or proof/fuel/node/test budget change. Initial failed proof checks are
retained: record layout/fixture decidability and literal-list normalization were
fixed without weakening statements, observations or premises. Final gates and
exact command/resource evidence are recorded in the additive handoff.

Independent read-only finder/skeptic reviews confirmed genuine independent source
execution, nonvacuity, complete observations and explicit projection/admission
limits; neither used Lean/server/builds. The finder required a stronger warm-cache
certificate; the retry now checks all completed-prefix source/config/toolchain
bindings and eight artifacts per module, trace/hash consistency and timestamps
not newer than the retained run completion boundary. Both reviews accepted the
fix. Scoped stopped-runtime maintenance was separately reviewed, fixed to exact
historically owned IDs and preserved full inspect/State/mount/diff/merged logs;
only zero-byte copied roots with known mount scaffolding were removed. No bind,
source, warm output, image, volume, seal or raw failure was deleted.

The same original runner enforces aggregate 12GiB/no swap under the 16GiB parent,
CPU1, serial Lean-j1/LEAN_NUM_THREADS1, OS headroom and the unchanged 600s guard.
Optional artifact caching is disabled inside Docker. Source-keyed separate warm
outputs preserve the old checkout. Actual Lean4.24.0/Lake5.0.0-src+797c613 and
KeySort2-job success were observed before component runtime claims.

Original full496841/taskDecision413142/baseDecision433573 FAILED125 records remain.
The new publication changes Decision's Closers/Callback dependencies, justifying
new checking. Cold published gate22265 FAILED125 in DecisionHashes, after a real
128-second Hashing rebuild. The independently reviewed warm attempt45496 also
FAILED125, but completed DecisionHashes in269seconds before its parent Decision
remained unfinished. These are failed gates, not baseline waivers or full passes.
No target/verdict/async/guard/budget was changed. Default/full/literal-wrapper
completion is still pending actual passing evidence. Raw global checks and their
separate exact-base no-new comparisons are recorded distinctly in the handoff.
No external compiler/EVM, bytecode or general SourceSpec proof is claimed.


Final source closure65693 PASS125jobs/51.1287s, sampled aggregateRSS1273528320,
reported cgrouppeak619229184; 558 exact sets retain all523 starting sets. Static
binding/corruption/runtime/trust/strict/layer/orphan/whitespace checks pass. The
legacy profile test first failed when invoked from the new worktree against its
old-root seed; its unchanged test passes in the preserved old checkout. This
invocation failure is retained, not relabelled a passing current-runtime test.
Current-runtime profile controls separately pass against the new-root seed.
Raw docs/current/public-base exit1/1: COMPLETE83findings (46missing/37ambiguous)
match exactly. Raw globalpin/current/public-base exit1/1:359notes,1161pins,0errors
match exactly. Separate public-base NEW0 comparisons pass. Compared with the
frozen baseline's72/14 findings,11doc ambiguities and345pin notes were introduced
by the consumed publication; the frozen-base no-new comparisons FAIL and are not
waived. Owner/global debt is not rewritten in this lane.

A separate final retry helper binds the newly completed269second DecisionHashes
output and all320 imported modules to45496's source/config/toolchain/cache traces,
with exact original command/targets/runtime/600s guard. Both read-only reviews
accepted this distinct cache-progress justification for one final check. It does
not assert a repaired parent proof; no further unchanged retry is justified if
the fully warm parent itself times out. Its actual outcome is in the handoff.

Process limitation: the initial public fetch and some early draft/setup edits
preceded acquiring the writer lock. Builds, integration writes, subsequent
reviewed edits and exports use the lock. No concurrent writer was observed, and
preserved source/seal hashes are checked. This is recorded rather than claiming
perfect retrospective lock compliance.


All-imports-warm parentDecision78278 also FAILED125 at the original guard,
sampled aggregateRSS5571874816, no cgrouppeak emitted after stop and no
Decision.olean/trace. No further unchanged Decision/default/full retry is made.
This isolates the parent check as the remaining mandatory runtime bottleneck;
completed Hashes is component evidence only. Cold currentSuite98977 FAILED125
while building Derived10 after completing Derived1–9, including157s/80s Derived7/8.
A separately reviewed same-runtime continuation certifies all235completed-prefix
modules against the immutable cold source/config/toolchain/log and8artifacts per
module before reuse, preserving the exact targets and600s/resource guards.
Its actual final outcome remains separate from mandatory full/literal validation.


WarmSuite119252 also FAILED125 at600s guard (610.84s includesunchangedcleanup),
sampled aggregateRSS11744055296, no final cgrouppeak emitted. It nevertheless
completed Derived10–20, including Derived17(144s)/Derived20(149s), leavingDerived21
uncompiled. Both reviews independently accepted a separate exact-runtime final
continuation, certifying all248completed-prefix modules (8artifacts each) before
Derived21 against119252's source/config/toolchain/log/trace/timestamp boundary.
No limit was raised; earlierSuite failures remainfailed. The finaloutcome follows.


FinalcurrentSuite139309 PASS262jobs/177.7931seconds after the explicitly recorded
bounded cold/warm progress. Sampled aggregateRSS5988339712, reported reused
cgrouppeak6010142720 (conservativelypossiblycumulative). Source/config unchanged,
actualLean4.24.0/Lake5.0.0-src+797c613/KeySort2job output retained. Earlier98977 and
119252 remainFAILED125, notrelabeled. CurrentSuite iscomponent evidence, not a
passingDecision/default/full/literalwrapper. No furtherDecision retry occurred.
All35newsource laws/controls retain558exactstandardsets and allold523pins.
The additive handoff records rawgate commands/exits/resources, bothbaseline
comparisons, exactrevision/input/artifacthashes and completeoriginalqueue status.
EveryparentG20-G23/BackfillA-B remainsPARTIAL; no SourceSpec/admission/V07/runtime/
bytecode or canonicalwhole-world certificate is asserted. Further independent
work is not claimed exhausted. Candidate next work includes actualSourcecrypto
read observations; canonicalmemory/type/layout and wholecall/body applications
remain distinct prerequisite obligations. All priorseals are preserved.


The raw stagedmerge whitespace gate exits2 on sixtrailing-space lines in the
published Source/Horizon.lean. Its COMPLETEoutput exactlyequals the publication's
frozenfb→2fe whitespace findings. The separate owned2fe→task whitespace gate
passes0. OwnerSourcebytes remainexactpublication; no whitespacefix/sourceowner
edit is made. The rawstaged gate is FAILED, notconvertedgreen by NEW0.


## Actual source literal Keccak application (2026-10-31, partial)

The independent published evaluator now has a checked application in the owned
SourceKeccak module. `eval_literal` executes the resolved builtin with a literal
binary byte argument at every horizon n+5, for either pipeline. This is a
constructor-specific sufficient horizon, not an admission cutoff. Conversion
allocates a memory byte object: the exact resulting heap is `afterLiteral`, not
the original heap. Complete locals and all nonheap fields (world, transient,
journal, events, logs and function locals) remain exact. `allocated` checks the
fresh object; `mk_wordBytes` proves bytes32 keeps every output byte and
`word_observation` recovers the exact bounded word.

`eval_transport` consumes ONLY the existing explicit `global.fixed.Keccak`
contract and the checked fixed_keccak_bytes law. It relates actual source
execution to the existing intrinsic typed keccakBytes/wordBytes observation.
It does not execute an intrinsic heap hash expression, certify a canonical
source/target heap relation, implement Keccak/a decoder/precompile, or prove
SourceSpec, compiler body selection, ABI/layout/linkage/runtime/bytecode adequacy.
The fixture's globals retain their existing mock ledger/precompile boundaries.

SourceKeccakControls uses the same populated source machine, preserving every
previous observation plus old heap object0, new object1 and next2. Binary
[0,255,128], empty and33-byte inputs execute under both pipelines with complete
result bytes and state. The standard empty hash word and wrong-input/output
controls are retained; wrong_source_output rejects an actual successful source
run returning32zero bytes. Zero horizon is exact timeout with unchanged input,
not revert/divergence. A wrong unchanged-heap state is independently rejected.
All558 starting axiom sets are unchanged;19 new exact standard sets make577.

Every original parent remains PARTIAL: G20 source callable/body/type/parameter/
result/getter/function-reference/readonly applications; G21 nested/reference/
calldata/slice/custom-error/catch and canonical decoding; G22.01 source self/
external call/admission/runtime frames; G22.02 source callback/reentrancy;
G22.03 source new/try-new/body; G22.04 linkage/function-value/storage mapping;
G22.05 source/world/runtime/admission composition; G23 effecting hash arguments,
general transient/layout, erased-emit argument execution and G16–G22 composition;
BackfillA source frame/layout applications; BackfillB source/V07 applications.
Existing complete histories, snapshots, controls and premises are unchanged.

Independent finder/skeptic reviews found no semantic defect in the allocation
or explicit hash premise. The skeptic requested a negative actual source-output
control (added), and both required exact Audit/dependency guards in the reused
runtime (added). Reviewers used no builds/Lean servers. Final checks/artifact
reviews are recorded in the additive handoff. Per-file MCP and get_goal remain
unavailable; no goal transition was attempted.

Mandatory Decision/default/full/literal-wrapper validation remains unresolved.
All earlier FAILED125 attempts, especially the fully warm published Decision78278
with320certifiedimports/noDecision.olean, are preserved. No unchanged retry,
owner edit, guard/verdict/async change or budget increase was performed.
Suite139309 PASS262jobs is component evidence only. Raw docs/global pins remain
FAIL1; complete public-base NEW0 and frozen-base regressions remain separate.

Next investigated independent clause: the actual Source.execS emit branch
executes evalConvArgs and encodeVals before its static guard/log prepend.
Erasure must preserve argument/encoding effects and exact failure, and may erase
only the approved log observation. Existing EmitControls checks typed target
operations and resolved syntax, not this independent source execution. This
application remains genuinely unfinished; it is not claimed exhausted.

Final registered closure180303 PASS in18.440870596s, aggregate sampledRSS60870656,
reported cgrouppeak34881536; stopped runtime identity/cleanup/source/config
bindings verified. Core+controls177907 PASS is retained separately. Binding577
exactsets/67coreclosure modules; positive evidence and23corruption cases; wrapper
positive+9extension corruptions and14profile corruptions; runtimecontrols PASS.
Trust1047sources/246sites/0findings; strict491automatic/61budget/11refuted/0pending;
layers172core/0elaborator; orphans1032reachable/0orphan; ownedwhitespace PASS.
Raw docs and pins task/public exit1 with identical complete83findings/359notes;
PUBLIC NEW0 PASS, frozen comparisonFAIL retained. No mandatory gate was retried.


## Actual source emit arguments, encoding and failure boundaries (2026-10-31)

The owned SourceEmit module now factors the PUBLISHED execS emit branch into
actual evalConvArgs, actual encodeVals, static check, and log prepend, in that
order. exec_success/exec_static/exec_argument_failure/exec_encoding_failure use
individual step-run premises, never an assumed whole execution/preservation
result. Every exact resulting Source.St and error is retained; EM.sub restores
the outer L0 while returning argument locals on success. Static failure retains
the encoding-final state; no rollback is inferred without an enclosing frame.
The log-only observation eraseLogs keeps ex/world/transient/journal, heap,
events and function locals. logged_payload_injective preserves exact bytes.
three_static/three_words_transport consume the existing independent ABI and
intrinsic word observers; no encoder/decoder or interpreter is added.

SourceEmitControls declares actual event nodes and proves event membership in
its supplied declaration environment. It reproduces EVERY old populated vector:
sender/self93/7, selfnonce1/codeSome0, saved/scratch true, journal3, oldheapobject0,
events/call bytes and oldlogs, functionlocals true and inputlocal true. The real
argument trace is literal binary hash allocation, local=false, dependent read
false; the reordered trace reads true before assigning false. Complete ordered
Vals and encoded bytes are checked, although both traces end at the same locals
and nonlog state. Actual execS runs differ in exact log bytes. Successful log
erasure retains allocation/object1/next2. Static rejection follows successful
argument+encoding execution, keeps oldlogs and allocation. A real divisionzero
argument after allocation yields exact nonempty panic0x12 BEFORE static refusal
under either static mode and both pipelines; intrinsic_panic_observation uses
existing independent source/intrinsic encoders. Zero statement horizon and a
positive statement horizon with zero argument horizon are timeout, not revert
or divergence. All bounds are constructor-specific sufficient horizons, never
public source admission/length cutoffs.

An additional DELIBERATELY MALFORMED memory-reference negative first completes
actual argument evaluation, then fails in actual encodeVals with exact stuck
"dangling memory reference" before static checking. It is not an admitted
SourceSpec machine or a positive heap-validity claim. It inhabits the general
encoding-failure boundary without replacing the valid populated positive cases.

These are actual independent Source executions plus exact intrinsic HASH/ABI
BYTE observations, NOT a proof of actual erased intrinsic target-body execution,
canonical Source/V07/layout/body/ABI relation, SourceSpec/admission, compiler,
frame/linkage/bytecode or external solc/EVM adequacy. The published global Keccak
pin remains explicit in the hash-byte observation. Existing EmitControls target
execution remains separate. The approved log exclusion in solidity-scope does
not erase argument/encoding effects, failure or events. All prior577 exact axiom
sets remain unchanged;37 new checked declarations make614 standard sets.

Every original parent remains PARTIAL: G20 callable declaration/body/parameter/
result/type/layout/getter/function-reference/readonly applications; G21 nested/
reference/calldata/slice/custom-error/catch and canonical decoding; G22.01 source
external/self-call/frame/admission; G22.02 source callback/reentrancy; G22.03
source new/try-new/body/admission; G22.04 source linkage/function-value/storage;
G22.05 source/world/runtime/admission composition; G23 actual target erased-emit
argument translation, general effecting hash/transient/layout and G16–G22
composition; BackfillA source frame/layout and BackfillB source/V07 applications.
Missing/reserved interfaces remain prerequisites, not preservation assumptions.
Independent work is not claimed exhausted by this checkpoint.

Review corrections: undefined simp typo and monad-run normalization fixed;
log erasure direct rfl hit original heartbeat limit, replaced with the already
proved small generic erasure law. No limit was raised. Both read-only reviews
requested an inhabited encoding-failure application (added as explicit malformed
negative) and certificate config/tool checks (added). Reviewers use no builds or
Lean servers. Final artifact review is separate. Per-file Lean MCP/get_goal are
unavailable; existing blocked goal unchanged.

Operational additive disclosure is saved outside all old seals. Keccak measured
growth68911104 exceeded estimate67108864 by1802240bytes; the estimate was NOT an
enforced resource guard. No sealed record was rewritten. This checkpoint starts
at729522176 available bytes with96MiB conservative growth estimate, same stopped
runtime and warm outputs,12GiB/no-swap/CPU1 under16GiBparent, serial Lean-j1 and
LEAN_NUM_THREADS1, original600s/proof/fuel/node/test limits/cache-off unchanged.
Mandatory full/Decision failures and literal-wrapper hold remain: no identical
retry or reserved Decision edit. Rawdocs/globalpins exits1 remain failures;
complete public-base NEW0 comparisons are separate from frozen-base regressions.

Final registered closure14531 PASS18.331969510s, sampled aggregateRSS60600320,
reported cgrouppeak37191680; exact source/config/runtime bindings/cleanup verified.
Binding614precisesets/68coreclosure; current positive evidence+27corruptions;
additive runner9extension+12priorcertificate corruptions; runtime/profile tests
PASS. Trust1049sources/246sites/0findings; strict491/61budget/11refuted/0pending;
layers172core/0elaborator; orphans1034reachable/0orphan; ownedwhitespace0.
Historical Keccak-only currentroot guard test FAIL1 (expected exact Audit mismatch)
is retained; separate exact committed aa640 Audit fixture compatibility PASS.
Rawdocs task/public1/1 with identical83completefindings and globalpins1/1 with
identical359notes; PUBLIC NEW0 PASS, frozen+11/+345 FAIL retained. Decision321
and priorSuite260 requested dependency source hashes unchanged; no retry/waiver.
Next inspected source callable boundary is callInternal at Eval:1248. It selects
G.prog.body via dispatchFn, builds typed parameters/returns and runs runMods.
No V07 argument/body/modifier/heap translation to intrinsic Entry is published in
the consumed tree; that application cannot be discharged by supplied target
results or another interpreter. This investigation is not a claim all further
independent Work/Backfill is exhausted. Whole assignment and goal stay blocked.


## Actual source callable execution and historical fixture repair (2026-10-31)

SourceCallable now proves the actual published callInternal boundary: selected
G.prog.body(G.dispatchFn F.contract d), actual zeroVals, exact dependent reversed
parameter/return frame, runMods with checked=true, retVals and mkRet. complete,
body_failure and wrong_frame require individual initialization/body/extraction
step equations. These are explicit component premises, not assumed whole target
preservation or general modifier/body lowering. missing_body and zero_horizon
retain complete input state. expression_complete/expression_failure/argument_failure
execute actual evalE.call/evalConvArgs/EM.sub and retain complete reached state.
Caller-local restoration means the caller's POST-ARGUMENT locals are retained;
it never rolls back argument writes or copies callee return slots into caller
locals. No second evaluator, state layer, AST/IR or compiler is introduced.

SourceCallableControls has actual member function declarations, two bool
parameters and one bool return, matching body.ps/body.rs metadata, zero return
slot, exact frame and a supplied resolved Program body table. Both pipelines
execute caller local=false followed by a dependent read, then a real callee
binary hash allocation and first-parameter return. Reordered arguments produce
true instead of false while keeping the caller local false and identical full
nonlocal state. Actual decoy execution returns the second parameter and a
wrong-declaration control distinguishes it from choose with parameters(true,false).
These exercise direct dispatch/body selection, not canonical inheritance/parser
resolution or function-reference lowering. Program bodies are supplied resolved
fixtures, not certificates relating parsed declaration bodies to target Entry.

EVERY old populated observation is retained: sender/self93/7, selfnonce1/code0,
saved/scratch true, journal3, heap object0 bytes[0,255], call events/old logs,
function locals true and caller input true. Successful/failed-return body execution
adds exactly object1 binary[0,255,128], next2; complete ex/events/logs/fnLocals
remain exact. Return/parameter frames and raw result values are checked separately.
The complete checked callee Fr retains this/sender/value/static/contract/depth;
its checked bit is true despite unchecked caller. A typed uint8 overflow in the
return expression gives real panic0x11 AFTER allocation; divisionzero in an
argument gives real panic0x12 BEFORE body execution and keeps heapnext1. Exact
bytes consume existing source/intrinsic panic encoding laws, not a new emitter.
Missing body preserves argument effects. A deliberately mismatched supplied body
checks the call-frame guard, not SourceSpec admission. Timeout at call horizon0,
expression0 and expression1/argument0 remains distinct from revert/stuck. No
admission/fuel/depth cutoff or budget increase. No fictional failing retVals
extraction from a correctly matching typed frame is offered as an inhabited case.

The historical Keccak unit-test regression is repaired: its positive Audit bytes
come from committed aa640d21 and SHA73c54e69dad346b59e1026f9b0b49cf107fdcf77460e0306a1d67c64289fd2ba,
also checked against certificate180303. It explicitly rejects current extended
Audit through the UNCHANGED production guard. Emit's historical positive is
similarly bound to committed3c4f9f82/SHAde5a0ae3ab1b21dd7ed961ae0804c39667a287b7c1c0cfdf34bbd129bc8aec07
and certificate14531, with current extension rejection. Old raw script exit1
records/seals remain unchanged. The new Callable wrapper keeps the exact stopped
runtime, original explicit command/targets/config/cache/resource checks, exact
Audit prefix/rest SHA, all old source hashes, and four prior checked modules
pinned to14531. Its positive fixture derives only from the exact committed Emit
Audit plus the one explicit Callable import; no arbitrary import stripping.

All614 starting exact axiom sets remain unchanged;42 new checked sets make656.
Read-only finder/skeptic reviews requested executed decoy discrimination (added)
and precise caller-local wording (corrected); neither builds/uses Lean servers.
Per-file Lean MCP and get_goal remain unavailable; goal unchanged. Final checks
and additive artifacts/reviews are recorded separately. Initial free693719040;
96MiB conservative growth estimate, same12GiB/no-swap/CPU1 under16GiBparent,
serial LEAN_NUM_THREADS1/Lean-j1 and original600s/proof/fuel/node/test budgets.

Every original parent stays PARTIAL: G20 canonical callable declaration/body/
parameter/result/type/layout, inherited/library/getter/function-reference/readonly
applications; G21 canonical nested/reference/calldata/slice/custom-error/catch;
G22.01 source external/self-call/runtime frame/admission; G22.02 source callback/
reentrancy; G22.03 source new/try-new/body/admission; G22.04 source linkage/function
value/storage; G22.05 Source/world/runtime/admission composition; G23 actual target
erased-argument/general hash/transient/layout and G16–G22 composition; BackfillA
source frame/layout and BackfillB Source/V07 applications. Published source
execution exists and is used here, while canonical G16–G19/V07 argument/body/
heap/modifier-to-Entry relations remain absent. No actual intrinsic internal-call
compiler, general modifier lowering or reserved owner implementation is redone.
These component proofs and finite controls do not close any G parent or lane.
Mandatory full/Decision exit125 records, raw docs/pins exit1, frozen increases and
literal-wrapper hold remain. No identical Decision retry or guard/owner change.
Further independent original work is not claimed exhausted by this checkpoint.

Final registered35093 PASS18.968478829s, sampledaggregateRSS60669952, reported
cgrouppeak33468416, exact current source/config/runtime/cleanup bindings.
Inventory656exactsets/69coreclosure; currentpositive+31corruptions; Keccak9,
Emit9+12 andCallable9+16 extension/priorcertificate controls PASS; existing
profile/runtime controls PASS. Trust1051sources/246sites/0findings;
strict491/61budget/11refuted/0pending; layers172/0; orphans1036/0;
ownedwhitespace0. Rawdocs/task/public1/1 with complete83equalfindings and
pins1/1 with359equalnotes, separatePUBLIC NEW0 PASS; frozen+11/+345 FAIL kept.
Decision321 and priorSuite260 dependency sources unchanged; no identicalretry.
A next independently useful G20/G22.04 clause is actual nonvirtual free/library
selection through published dispatchFn, with supplied source bodies and exact
caller context. This is separate from canonical compiler/linkage and modifier
lowering; no claim independent clauses are exhausted at the callable checkpoint.


## Free/library source selection and reached repeated calls (2026-10-31)

After the reviewed/committed/sealed callable checkpoint bf705c0d, original
G20/G22.04/BackfillB work continues independently. SourceDispatch proves actual
published dispatchFn identity for scope=None and for a scope outside the ACTUAL
(E.linearize caller).getD[caller] chain. The consequent body lookup laws do not
assume body preservation or canonical parsing/linking. Both fnSig branches are
covered, and no compiler/modifier implementation is duplicated.

SourceDispatchControls supplies actual contract C, library L, library-function
and free-function member declarations, real signatures(two bool parameters and
two heterogeneous address/uint256 returns), library role metadata and actual
C3 chain[C]. Actual runMods/callInternal initialize return slots, execute a real
binary hash allocation, read ambient sender/value and return the complete typed
tuple(1,7) under both pipelines. All old populated machine observations remain:
balances93/7, code0/nonce1, persistent/transient true, journal3, object0[0,255],
events/oldlogs and functionlocals; actual added object1[0,255,128]/next2 and full
raw outcomes are checked. Actual changed frame sender=self/value0 yields(2,0).
A same-name caller-scope decoy with a genuinely different body also yields(2,0),
so wrong virtual redirection of the library declaration is discriminated by
actual executions. Full context retains this2/sender1/value7/staticfalse/C/
checkedtrue/depth0. Actual source internal calls leave both paid balances93/7;
wrong-extra-charge86 is rejected. Internal ambient msg.value is not a second
payment or an external nonpayable-entry admission.

The actual library call is then executed at the REACHED free-call state, not
at the original input. Both exact statuses/results and both boundary states
are retained. The second call allocates object2/next3 while preserving object0,
object1, complete ex/events/logs/fnLocals and shared transient scratch=true.
The wrong internal-call transient-reset control rejects none. These are internal
source calls, not transaction boundaries; no reset is inserted between them.
General source transaction/reset-to-intrinsic frame/layout composition stays open.

The complete actual Source result is supplemented by an ordered observation
[sender,value,timestamp,this,selfBalance]=[1,7,12345,2,7], using existing typed
unRet/toVals/getAt/word observers. It does NOT replace raw outcomes/full states.
Existing typed intrinsic environment expressions on an explicitly projected
state agree on sender/value; an independently executed ordinary PAID intrinsic
contextEntry retains its full vector93/7/3/9 and[1,7,12345,2,7]. This is observation
transport, NOT actual compiled-library execution, deployed-library/code identity,
World.libraryCall linkage, canonical SourceSpec/runtime-frame/body/layout/ABI
adequacy or an arbitrary target world equality. Source library role metadata is
separate from deployment; no library account/storage/hash is invented. Supplied
resolved program bodies and mock ledger/globals retain the earlier boundaries.

All656 prior exact standard axiom sets are unchanged;37 new checked declarations
make693. The old historical Keccak/Emit positive fixtures remain SHA-bound and
reject the extended Audit. Callable's historical positive remains exact prior
Audit+oneimport and rejects differing current Audit; its label is clarified.
The new additive Dispatch runner retains original command/targets/runtime/cache/
config/source guards and pins six prior modules to checked35093; only two new
modules and the exact fourth Audit import are admitted. No source/owner edits,
new interpreter, decoder, payload emitter, axiom/sorry/native shortcut, source
profile/target/exclusion or proof/fuel/node/test/time/resource increase.

Resource disclosure: second-checkpoint32MiB STORAGE PLANNING estimate was revised
PROACTIVELY to40MiB in a new budget-reestimate record because retained diagnostics
and corruption fixtures consumed more than forecast. The initial record is
preserved; it was not an enforced runtime guard. Both checkpoints remain within
the original96MiB turn planning envelope and ample measured OS/disk headroom.
Actual12GiB/no-swap/CPU1/16GiBparent/serialLean-j1/600s guards remain unchanged.

Every original G20,G21,G22.01-.05,G23 and BackfillA/B parent stays PARTIAL. G20
canonical declaration/body/argument/result/type/layout/inherited/getter/ref/readonly
applications; G21 nested/reference/calldata/slice/custom-error/catch/canonicalABI;
G22 source calls/callbacks/creation/library/function-value/world/runtime/admission;
G23 actual target erased-args/general hash/transient/layout and G16–G22 composition;
BackfillA/B Source/V07/frame/layout applications remain open. No independent
exhaustion or whole-source/bytecode/compiler/EVM adequacy is claimed. Mandatory
full/Decision125 failures and literal-wrapper hold persist with no identical
retry. Rawdocs/pins failures remain separate from public NEW0/frozen increases.

Final registered60048 PASS18.392024251s, sampledaggregateRSS58572800,
reportedcgrouppeak35028992; allcurrent source/config/runtime/cleanup bindings.
Inventory693exactsets/70coreclosure; currentpositive+35corruptions. Historical
Keccak9,Emit9+12,Callable9+16 andDispatch9+20 fixture/certificate controls PASS;
allproductionguards unchanged. Trust1053/246/0; strict491/61budget/11refuted/
0pending; layers172/0; orphans1038/0; ownedwhitespace0. Rawdocs/task/public1/1
with83equalfindings, pins1/1 with359equalnotes; PUBLIC NEW0 PASS separately;
frozen+11/+345 FAIL retained. Decision321/priorSuite260dependency sources
unchanged, no retry. Finalstatic/export storage forecast further recorded
ADDITIVELY as48MiB (not runtimeguard): retained Docker stdout grows alongside
raw logs, so allow18MiB remaining before checks/export. Both checkpoints remain
within original96MiB turn forecast; all old estimate records remain intact.
Next investigated G21 application: actual execS.revertError evaluates/encodes
arguments before returning selector++bytes. Unlike Source.selector's UTF8
signature input, Glob.selector uses asciiBytes. Exact input-byte equality must
be justified for a canonical signature; do not silently assume it or add an ASCII
source-profile cap. Concrete ASCII declarations can discharge it, while general
canonical signature/representation applications remain open. No exclusion or
semantic choice is inferred from this investigation.


## Actual custom-error execution and signature inputs (2026-10-31)

After source callable and free/library checkpoints, original G21 independent
work continues. SourceCustomErrors executes the PUBLISHED execS.revertError
argument-conversion then encoding then selector++data halt boundary. Individual
actual step equations are explicit, with complete exact final state; no target
preservation, new interpreter, decoder or generic payload emitter. The branch
has no emit-style static empty-revert guard. Effects/errors outside this fragment
and catch/runtime/SourceSpec composition remain open.

A concrete current representation gap is reproduced: Glob.selector hashes
asciiBytes of signature characters, while Source.selector hashes String UTF8.
selector_of_bytes bridges to existing Semantics.customSelector/selectorBytes
ONLY with independent input-byte equality and the existing global.fixed.Keccak
contract. It never assumes the desired hash/output equality or injectivity.
Concrete Bad(bytes32,bool,bool) uses a kernel ByteArray unfolding proof to
establish the UTF8 bytes and exact input equality. A pure non-ASCII input
counterexample shows why that premise cannot simply disappear; this does not
claim an admitted Unicode identifier or introduce an ASCII source-profile cap.
General canonical signature/admission/representation evidence remains required.

SourceCustomErrorControls retains every old populated observation and actual
member error declaration. Real binary hash allocation, local=false and dependent
readfalse execute under both pipelines/static modes, followed by real encodeVals.
Raw error data is exactly4selectorbytes+96orderedstaticABIbytes(length100), with
oldheap0/newheap1/next2 and complete ex/events/logs/fnLocals retained. The error
outer locals are L0; the actual argument step's changed locals and complete typed
values are separately checked. Actual reordered arguments yield different actual
custom-error payloads via shared-prefix cancellation, without any collision
assumption. Static true still returns this nonempty custom payload rather than
plain revert. Real argument divisionzero after allocation returns panic0x12
before payload construction; zero and insufficient argument horizons are timeout.
No direct wrong-signature hash-noncollision control, general nested/reference/
calldata/slice/custom-error catch decoder, or actual target body emission is
claimed. The selector-only intrinsic observation keeps actual source ABI data;
canonical all-type/body/frame/layout transport remains open.

All693 prior precise axiom sets remain unchanged;26 new kernel-checked sets make
719. Registered76535 PASS51.336456357s, aggregate sampledRSS1286197248,
reported cgrouppeak623230976; actual Lean4.24.0/Lake5.0.0-src+797c613 and passing
lake build Solidity.KeySort2jobs retained. Original200000heartbeat failures in
broad contradiction search were fixed by targeting the explicit Nat100≠0 fact;
no proof/time budget increased. UTF8 literal kernel reduction follows the
existing ByteArray pattern, no native shortcut or trusted implementation.

The full corruption suite runs ALL40 ORIGINAL AST cases, mutations and expected
outcomes unchanged through the unchanged production checker. Only check's I/O
is streamed as the identical expanded JSON to/dev/stdin; persistent exact seed
SHA, type-sensitive delta/replay-byte equality, expanded SHA and raw output
preserve complete reproducibility without40redundant full JSON copies. The
initial generated-string syntax failure remains exit1 in its original log;
corrected replay executes all40 cases(positive+39rejections). No test/guard/case/
target omission. Both reviewers inspected this harness before execution; final
provenance includes harness/originaltest/checker/seed and everycompactfixture.
This is transient test input, not moving source/toolchain/cache onto tmpfs.

Every original G20,G21,G22.01-.05,G23 and bothBackfills stayPARTIAL. Actual source
fragments now exist and are used, but SourceSpec/canonicalV07/type/layout/ABI/
body/linkage/runtime-frame/bytecode/admission, reserved getter/ref/readonly/decoder
and general Source/world applications remain open. Mandatory full/Decision125,
literal-wrapper and rawglobaldocs/pins failures remain honest; no identical
retry or new scope/exclusion/premise approval. No source/profile/Fml.inTarget,
axiom, fuel/node/test/time/resource change, externalcompiler/EVM adequacy or
independent-exhaustion claim. Existing blocked goal unchanged; get_goal/LeanMCP
unavailable. Third24MiB storage forecast remains within original96MiB turn
forecast, same stoppedruntime/warmoutputs, cacheoff and12GiB/no-swap/CPU1/serial
Lean-j1/600s bounds. All old files/seals/failing logs are preserved.

Final binding719precisesets/71coreclosure PASS; ALL40 streamed corruption cases
(positive+39rejects), currentcustomwrapper9+24priorcertcorruptions and every
historical/currentfixture/profile/runtime suite PASS. Initial harness parser
FAIL1 remains separately recorded; generated-code raw string fix and exact
JSON replay checks PASS. Trust1055sources/246sites/0findings; strict491/61budget/
11refuted/0pending; layers172/0; orphans1040/0; ownedwhitespace0. Rawdocs task/
public1/1 with83equalfindings, rawpins1/1 with359equalnotes, separatePUBLIC NEW0
PASS andfrozen+11/+345 FAIL retained. Decision321/Suite260 dependency sources
remainunchanged; no identicalmandatoryretry. No new evidence discharges full/
default/literal-wrapper gates, SourceSpec or canonical source-to-Entry contracts.
Remaining ready G21 work includes general argument/encoding failure composition,
direct wrong-selector concrete controls and supported nested/reference/catch
applications; canonical signature/type/layout/source-world certificates stay
prerequisites. These three checkpoints do not exhaust the original assignment.


## G21 actual custom-error failures and supported nested/rethrow checkpoint (2026-10-31)

Owned `Solidity/Lowering/V08/SourceCustomErrorFailures.lean` proves the actual published execS
revertError argument-failure and encoding-failure boundaries independently.
The former retains reached St but discards private argument locals via EM.sub;
the latter executes actual encodeVals after successful arguments at outer L0.
Each law requires only the respective individual step equations, not a desired
whole lowering/preservation result. converted_tail_failure composes an actual
converted head with a failing tail. The populated controls directly instantiate
it: binary hash allocation succeeds, local true becomes false, then actual
divisionzero produces exact panic0x12 at the reached heap. Both pipelines and
static modes are quantified. Complete old ex/world/balances93/7/storage/transient/
journal3/events/logs/fnLocals, heap0 and reached heap1/next2 remain observable.

A small actual catalog declares Record(bool) and RecordError(bytes32,Record).
The actual typed struct constructor succeeds after the hash and local assignment,
allocating Record(false) at2 with full typed returned values and localsfalse.
The actual published encodeOne reference branch then returns exactly
.stuck "not ABI-encodable"; this is a REPRODUCED missing aggregate-encoder
prerequisite, not a dangling reference, EVM revert, approved exclusion or whole
SourceSpec failure-freedom proof. Complete state is retained: balances93/7,
persistent/transient true, code0/nonce1/journal3, old events/logs/fnLocals and all
three typed heap objects/next3. Wrong rollback and plain-revert controls fail.
No Source/decoder/encoder owner edits, duplicate payload emitter or profile cap.

The next supported G21 application is actual nested-block panic and canonical
Source.rethrow at the genuinely allocated binary byte object. General
rethrow_bytes derives exact unchanged-St execution from actual typed local and
present heap object premises at any positive horizon; zero horizon is exactly
timeout with no heap premise. The populated application forwards [0,255,128],
distinct from panic bytes; nested actual panic uses existing panicData_transport
to observe exact intrinsic encodePanic0x12. EM.attempt observes these exact halts
and reached complete states; it is NOT claimed as Solidity catch selection.
A concrete truncated-selector negative distinguishes actual length100 from99
without a hash noncollision hypothesis; distinct actual four-byte selector
hashes/general canonical signature representation remain separate obligations.

All719 prior exact standard axiom sets are unchanged;28 new checked sets make747.
Independent finder/skeptic requested a direct generic-prefix application; actual
converted_hash_head and changed_local_tail_failure now discharge it. Subsequent
read-only proof/script reviews found no semantic/ownership issues. Lean MCP and
get_goal are unavailable; bounded serial import checks are the fallback and the
existing blocked goal stays untouched. Production source/config/runtime/cache/
resource/target guards remain exact; new additive wrapper uses checked76535 prior
certificate plus the exact Audit prefix and10 prior source hashes. Its unit test
uses the SHA-bound committed8fb41 Audit, rejects different current content and
checks prior certificate/source corruptions. All original40 checker cases remain
byte-for-byte;4 new source mutations/omissions make44 streamed cases, unchanged
production checker outcomes and replayable seed+delta+expandedSHA evidence.

Initial32MiB storage forecast is preserved. Retained additional failed proof
attempts/raw Docker logs and the supported rethrow extension justified an
additive36MiB forecast before final check/export; neither forecast is an enforced
execution guard. Same stopped runtime, warm outputs, cacheoff, aggregate12GiB/
no-swap/CPU1 under16GiB parent, OS headroom, Lean-j1/LEAN_NUM_THREADS1 and600s/
all proof/fuel/node/TestSuite budgets unchanged. No deletion/new runtime/cache
relocation. Raw wrapper inventory/preflight lock/proof/summary-script failures
are retained separately from corrected passing gates; no failed exit is green.

Committed handoff scope remains PARTIAL for EVERY original group and backfill:
G20 canonical callable/getter/inherited/functionref/readonly/body applications;
G21 general nested/reference/calldata/slice/catch/canonical ABI and aggregate
encoding; G22.01 source external/self/frame, .02 source callback/reentrancy,
.03 source new/trynew/body, .04 canonical library/functionvalue/linkage, .05
source/world/runtime composition; G23 general hash/emit/transient/layout and
G16-G22 composition; BackfillA source frame/layout applications and BackfillB
canonical Source/V07 signature/ABI applications all remain open. Published
Source.Eval is consumed as real independent semantics. No compiler/solc/EVM/
bytecode/admission adequacy follows from these kernel component results.
Decision321 dependency source hashes are still unchanged, as are Suite260;
no supported distinct repair justifies repeating failed full/Decision600s.
All previous125, literal/default/full/executable-refresh holds, raw docs/pins1,
public-only NEW0 and frozen-base increases remain preserved. Ready independent
work is not exhausted: supported dynamic-byte/nested ABI source applications,
canonical signature-input evidence and remaining exact catch/body/frame
applications require further work under ownership constraints. Artifact handoff
records exact full committed head/base, every command/exit, reviews and seals.

Final focused110751 PASS57.041997522s, sampled aggregateRSS1264185344,
reported cgrouppeak608309248; exact747sets/72coreclosure and ALL44corruptioncases
(positive+43expectedrejections) PASS. Trust1057/246/0; strict491/61budget/11refuted/
0pending; layers172/0; orphans1042/0. Independent final staged finder/skeptic
ACCEPT/no findings after the populated generic-application correction. Rawdocs/
pins1 remain failures. A pre-staging bare owned filename produced one NEW missing
finding and the complete comparison correctly failed; full owned path/staged
registration fixed it, retaining raw47missing log separately. Finaldocs46missing/
37ambiguous andpins359notes exactly equal public baseline, separately PUBLIC NEW0;
frozen+11/+345 and mandatory125/default/full/literal holds unchanged. All prior
seals/raw logs persist; exact final head and compact additive artifacts are in
the checkpoint handoff. No goal identity/objective/status reset or completion.


## G21 actual ABI expression checkpoint (2026-10-31)

`Solidity/Lowering/V08/SourceAbi.lean` proves actual evalE.abiEncode composition
from individual evalArgs/encodeVals steps and actual result allocation at the
reached heap.next. Literal encode/encodePacked reads raw literal bytes directly,
allocating ONLY its result. Existing natWordBytes/pad32 and Error-payload byte
observations apply without a new length/admission bound. No intrinsic general
tuple encoder exists in the consumed interfaces; no emitter/decoder is added.

`Solidity/Lowering/V08/SourceAbiControls.lean` uses the complete old populated
machine: balances93/7, code0/nonce1, persistent/transient true, journal3, oldheap0,
events/logs/functionlocals. Empty/binary[0,255,128]/33-byte inputs retain all
fields and allocate object1/next2. Actual mixed arguments evaluate binary,
assignfalse/readfalse,33bytes,then real hash allocation1; result bytes allocate2/
next3 and callerlocalsfalse. Both pipelines/static modes/packing modes execute.
Standard320bytes and packed70bytes retain full outcomes; full offset words160/
224 versus reordered160/256 and actual wrong-order/packing/pointer/skippedhash/
locals controls discriminate real runs. Horizon6 retains localfalse then times
out BEFORE hash allocation; no source admission cutoff or rollback is inferred.

Primitive word and layout-prefix facts avoid repeated cryptographic reduction
under unchanged200000heartbeats. All747 prior exact sets unchanged;33 new checked
sets make780. Final143656 PASS139jobs55.816887555s; old failed attempts retained.
Independent finder/skeptic requested full offset-word and actual-run negatives;
these are added. A reported duplicate conjunct was withdrawn after identifying
overlapping read output. No observations/statements/premises/proof budgets weakened.

Space: old540MBreserve preserved. Native Git v4 index encoding retains identical
staged entries/debug metadata/cached diff and all source hashes, without global
configuration/cleanup. Evidence uses a checksummed directory, compact lossless
case records and explicit ordered original/owned patch series referencing old
sealed segments plus this checkpoint. All prior snapshots, seals, raw failures and caches are retained.
Initial18MiB forecast/revised21MiB forecasts are estimates, not enforced guards.
All44 old checker cases remain verbatim;4 new source-binding cases make48.

Every original G20,G21,G22.01-.05,G23 and BackfillA/B remains PARTIAL. Missing
canonical SourceSpec/V07/type/layout/ABI/body/linkage/runtime-frame/bytecode/
admission and reserved getter/ref/readonly/decoder applications stay explicit.
Aggregate encoder stuck and general nested/calldata/catch/signature gaps remain.
Mandatory Decision/full125 and literal/default/executable-refresh holds are not
waived or retried unchanged; raw docs/pins1 and frozen-base increases persist,
with public equality separately checked. Kernel components are not compiler/EVM
adequacy. Independent work is NOT exhausted; new checks require safe disk headroom.
Existing blocked goal untouched; get_goal/LeanMCP unavailable. Exact commit,
commands/exits, remaining queue, resources/reviews and indexed evidence appear
in the compact additive handoff; no whole-lane completion is claimed.


## G21 actual selector/signature prefix applications (2026-11-01)

The approved exact20 stopped-container maintenance returned20 nonforced204
removal responses, each reconciled404; all other objects, runtime, source and
seals remain. Actual free bytes rose540082176→4050046976, a measured3509964800
increase, not the logical VFS estimate. Source2963/seals26/member344 checks
passed before/after. The human approval and restored immutable baseline are
indexed in the additive approved-cleanup-20261101 artifact directory. The old
missing-baseline stop and all old receipts remain untouched. No goal change.

SourceAbi.selector_execute and signature_execute follow the actual published
evalE branches: all arguments, then selector conversion or signature-byte read,
then tail encoding, then result allocation at the final reached heap.next.
Every individual reached locals/St and actual exact bytes remain explicit.
SourceAbi.prefixed_arguments_failure retains the actual reached failure and
complete machine. The literal laws introduce no encoder/decoder or length cap.
The signature prefix observation consumes the existing fixed.Keccak pin.
These are source execution/component observation laws, not canonical SourceSpec,
V07, compiler-body/ABI/layout/runtime-frame/bytecode/linkage adequacy.

SourceAbiControls instantiates the laws on the existing populated machine and
actual local write/read/hash-allocation tail. Binary selector[0,255,128,1] and
empty signature hash prefix[197,210,70,1] produce324-byte payloads with complete
existing320-byte tail, all offset words and old heap0 retained. Mixed output
pointer2/next3 and localfalse are exact. The signature-memory variant allocates
an actual STRING object1, executes the tail/hash object2, reads string1 after
the tail at the reached heap, and returns a separate bytes object3/next4. Its
complete balances/code/nonce/persistent/transient/journal/heap/events/logs/
function-locals vector retains every old observation. Both pipelines/static
modes execute. Wrong prefix/pointer/skipped effects and actual reversed-order
runs discriminate; low horizon preserves localfalse before timeout, not revert.
No collision or hash-injectivity premise is used: the empty-prefix discriminator
uses the already checked Keccak vector.

Finder requested precise admission evidence: the published resolved ABI
constructor does not carry Typed.argsOK. The concrete selector/signature/string
memory fixtures now prove the existing argsOK predicate, and an overlong33-byte
selector retains its published typing rejection. The generic arbitrary-byte
resolved execution law is not an all-input source-admission theorem. Skeptic
confirmed the actual reached-state/allocation boundaries. Prefix list helpers
avoid accidental cryptographic reduction under the unchanged200000heartbeats;
no reduction, fuel, node, test, wall, CPU or memory budget is increased.

Focused bounded10390-96c6cb08 PASS139jobs/60.386816534s; actual Lean4.24.0 and
Lake5.0.0-src+797c613; KeySort PASS2jobs. Cgroup peak681512960 and sampled aggregate
RSS1240809472 bytes. Same checked runtime0fe0539b reused, cacheoff, CPU1,
Lean-j1/threads1,12GiB/no-swap under16GiB parent; no runtime/cache duplication.
All780 old exact standard axiom sets unchanged;33 checked additions make813.
Raw intermediate proof failures are retained. Production checker/corruption and
static validation results are in this checkpoint's additive handoff.

Proposed coordinator ledger localEvidence ONLY for existing feature IDs
abiEncodeWithSelector and abiEncodeWithSignature: these owned source component
laws/controls. No generated ledger, manifest status, global pins or other-owner
source is edited. All G20,G21,G22.01-.05,G23/BackfillA-B parents remain PARTIAL.
Canonical Source/V07/type/layout/ABI/body/linkage/runtime-frame/bytecode/admission,
nested aggregate/calldata/slice/catch/reserved-owner applications remain open.
Mandatory Decision/default/full/literal/executable-refresh holds and raw docs/
global-pin failures are not waived. No unchanged heavy retry or compiler/EVM
adequacy claim. Ready independent work is not claimed exhausted.


Validation follow-up: production813pins/73coremodules and ALL48 unchanged
production evidence cases pass. Runtime profile plus published/Keccak/emit/
callable/dispatch/custom-error/failure/ABI wrapper tests pass. Historical prefix
unit test initially FAIL1 because its old pinned-worktree positive was checked
under the current published-worktree root. Fixed UNIT ONLY: bind immutable
841312 before-record SHA e14ab26a13ede5931950da81dbd030dfde39ef536b115d3c5a9ddc6ee6fbd730,
use its original seed.repository context, explicitly reject the current context,
and retain all14 original corruptions. Production strict inspector is unchanged;
the raw failure is retained and the fixed16 mocked-call test passes. Independent
finder/skeptic confirmed this is fixture binding, not a guard relaxation.

Fresh trust/strict/layers/orphans/owned-whitespace PASS. Raw global docs FAIL1:
complete current/public83findings byte-identical (46missing plus37ambiguous),
frozen72findings adds11ambiguities. Raw global axiom inventory FAIL1:
current/public359notes identical, frozen14notes adds345. Separate public NEW0
comparisons pass; neither raw gate is green and frozen increases persist. Whole
raw outputs and complete lists/hashes are retained. Suite139309 remains the
prior actual262jobs PASS: all260dependency sources/config/log bindings refreshed
unchanged, no new Suite execution claimed. Fully warm Decision78278 remains
FAIL125:321dependency sources unchanged, no supported repair or unchanged retry.
Final/default/full/literal/executable-refresh boundaries remain unresolved.

All780prior exact sets and every old fixture remain. New source dependencies
stay within the already published closure. No Source/backend/global-manifest/
TrustAudit edits, hashes-as-injective premise, native shortcut or increased
budget. Proof/script reviews are read-only and do not start Lean. This checked
component does not finish any original parent or claim independent work exhausted.


## G23 selected transient execution/reset component (2026-11-01)

SourceTransient reads published Source.Eval/Machine/World only. transient_write
uses actual writeAt/transientRoot/static guard and existing journal apply;
transient_static_revert keeps exact empty revert and machine. Bool reads after
existing ExecState.endTx see the typed default. transient_undo restores complete
source state through actual undo_apply. endExecution updates only the supplied
execution component; it is NOT another source transaction interpreter, frame
admission, or a claim that transaction entry keeps source memory. The target
selected-path reset theorem uses existing World.resetTransient_storage? and
Storage.resetTransient_find, preserving uninstalled None and the actual init
lookup; no storage representation theorem is invented.

Controls in SourceAbiControls retain every old fixture. Actual scratch assignment
and a subsequent actual read share the source cell before endTx, then readfalse
after endTx; undo restores the actual opening snapshot. The opening uses existing
endTx on the populated source machine: funds93/7, code0/nonce1, savedtrue, heap0,
events/logs/fnLocals retained; journal0→1→0 and transientfalse→true→false are exact.
Static rejection happens AFTER a real RHS localfalse effect; no false rollback
or timeout/revert conflation. A small EXISTING intrinsic Contract catalog receives
a real create then7-paid Entry writing both bool roots and returning[0,255,128].
Actual target observations93/7/true/true become93/7/true/false after reset, with
same binary result. Wrong stale transient and wrong payload controls discriminate.
These are selected-cell components, not canonical Source/V07/body/world admission
or whole-world storage/layout equivalence.

Finder caught a serial-rebuild risk BEFORE any build: appending to the old high-
fanout SourceEnvironment dependency could stale independent downstream branches.
Drafts preserved, old file restored EXACT8bf37fe6, and new declarations moved to
owned SourceTransient leaf. New reviewed wrapper retains unchanged ABI command,
old source/config/runtime/cache/resource guards, derives exactly the four-module
cold chain SourceTransient→SourceAbiControls→Audit→PrefixControls and at most
one cold dependency per node, and proves every other135module source/output/
trace/hash/setup/ctime warm against successful10390. No new runtime. Its inert
positive plus4 stale/parallel/foreign/missing-chain negatives pass. Actual warm
JSON parses correctly across two code-generation layers. A caught newline escape
unit failure and focused proof failures are retained; no failed gate relabeled.

Final30988-47169f59 PASS140jobs/61.69171207s, cgrouppeak614019072 and sampled
aggregateRSS1268494336bytes; actual Lean4.24.0/Lake5.0.0-src+797c613 and KeySort
PASS2jobs. Same12GiB/no-swap/CPU1/serial-j1/cacheoff/600s/OSheadroom and proof/
fuel/node/TestSuite bounds. All813 prior exact standard sets unchanged;19 new
checked declarations make832. Production/checker/corruption/structural/reviews
and exact-head artifacts recorded in additive handoff. All48 prior adversarial
cases remain verbatim plus2 new source-file binding cases. No owner/source/model/
global ledger/pin/profile/exclusion edits. G23 and every other original parent
remain PARTIAL; selected observations do not close canonical source transient
layout/runtime-frame or G16-G22 premises. No independent-exhaustion claim.


Transient checkpoint final validation: production832exactpins/74coremodules PASS;
ALL50 production evidence cases PASS (48earlier byte-verbatim plus2newfile
mutations); every historical wrapper/runtime test and newactualcold-chain/final
JSON/profile tests PASS. Fresh trust1060sources246inventory0findings, strict/
layers/orphans/owned-whitespace PASS. Raw docs/globalpins EXIT1 retained; full
current/public byte equality remains separate NEW0, frozen+11doc/+345pin debt
unchanged. No Decision/default/full/literal retry or waived mandatory gate.
Finder/skeptic accepted proof semantics, selected-cell boundaries and revised
serial certificate. Exact19newaxiomsets and measured logs are in the handoff.


## Published099 ABI-entry application (2026-11-01)

Consumed public prerequisite `099bfbe185731c354b12a40f28ccf5d98534c779`,
retaining frozen ancestor `fb379ae20f10e2c92113453ddd9d40d8f2efbe09` and checked
V08 predecessor `7c3c8274eeafe908a1e96709d0491c02b306e03f`. The old absolute-path
checkout and seals are preserved. Incoming owners' implementations remain unchanged.
The approved same-VM application container is
`47c5808627ffeadf7d11884f8c37dd554eae2ed7bc5d55756781500b6ecf9a20`;
no further container was created, and no old runtime was replaced.

`SourceAbiEntryControls.binary_source_entry` connects actual independent
`Source.evalE` ABI allocation (both pipelines and static modes, full locals/St)
to the exact published `AbiEntry.eager` result and `eager_cref` application.
Empty, binary and 33-byte inputs have actual input sizes 68/100/132 including
the supplied selector. These concrete size proofs discharge the existing decoder
premise; they introduce no Source admission bound. Exact lazy reference `(68,3)`,
truncation, shifted-head and wrong-byte controls discriminate actual runs.
`observeResult_injective` and `observeBytes_injective` retain complete successes
and exact decoder failures; kernel computation reflects back to typed results.

`mixed_effects_and_entry` reuses actual Source argument execution: binary,
write-false, read-false, 33-byte value, then the fixed hash. It retains the whole
reached machine and links heap object 2 to the supplied decoder input.
`mixed_entry` observes every decoded argument's canonical bytes and preserves
run/revert/refusal branches; it is explicitly not a general injectivity theorem.
`mixed_second_reference` proves `(260,33)`. Wrong order and packed encoding are
actual negative controls. Every previous populated-state/vector theorem remains.
The published panic decoder now ignores trailing bytes; four new controls retain
canonical panic bytes, reject short/wrong-selector inputs and distinguish codes.

All 832 predecessor axiom sets are unchanged; 26 new standard-only sets bring
the inventory to 858. No axioms, sorry, native shortcuts, representation changes
or proof-budget increases were introduced. Direct reduction first failed with
recursion/Decidable errors; the observer reflection fixed it. A later combined
heap theorem hit the original 200000-heartbeat limit; small heap/input lemmas
fixed that without changing the limit. Raw failed outputs remain evidence.

The cold bounded closure failed125 at600s after106 completed target calls.
Measured source/config/toolchain-keyed output reuse justified subsequent checks;
final closure passed in80.582s, peak aggregate RSS2414825472bytes and cgroup
peak1958014976bytes. The enforced aggregate12GiB/no-swap/CPU1/serial Lean-j1,
cache-off, OS headroom and original600s guards were preserved. The original
805306368-byte admission estimate and540000000-byte reserve remain enforced.
A proposed smaller admission was auto-review rejected and was not executed.
Finder caught cumulative Docker log attribution before reuse; the runner now
binds the archived prefix and checks only each new suffix, preserving full logs.

All Work G20/G21/G22.01-.05/G23 and Backfill A/B parents remain PARTIAL.
G20 still needs canonical Source/V07 signature/argument/body/Entry application;
G21 still needs general nested/reference/slice/calldata and exact catch/frame
applications; G22 still needs actual Source external/self/callback/creation/
library/world composition; G23 still needs general effecting arguments and
canonical source-unit/transaction/environment/emit composition. Published ABI
entry and function-reference components are partial prerequisites, not those
missing bridges. Supplied-body intrinsic backfills are not Source execution.

Mandatory full/default/Decision/literal-wrapper/executable refresh remain open.
The new Decision closure is322 local modules (old321), with one added module
and eight changed sources; inspection found no demonstrated repair of the warm
Decision600s failure. No unsupported repeat was made. Historical failed125 and
raw global docs/pin exit1 records remain failures. Public/frozen comparisons and
scoped checks are distinct. Kernel component proofs are not pinned solc/EVM or
bytecode adequacy. The persistent blocked goal identity/objective is untouched.


## Allocated canonical rethrow application (2026-11-01)

Independent G21 work continues while Q-ANCESTRY-099 remains pending. No branch,
HEAD, ancestry, goal or runtime configuration changed. Before the overlay,
the exact staged tree63b18705af46bb692f5d388892c873fecf5ac6be, binary index,
index entries and92 owned source/blob identities were saved in the additive
rethrow evidence directory. The old7c checkout and all prior sealed packages
remain unchanged. The default prepared index remains its original snapshot.

The generic canonical rethrow and zero-horizon laws already existed in
`SourceCustomErrorFailures`; they are consumed, not restated as new progress.
New `SourceRethrow` composes actual SourceAbi packed-literal evaluation, getV,
its returned reference, and actual execS rethrow through existing EM.sub.
The fresh object's bytes are proved by Heap.alloc_get, so no whole execution
result or desired lowering equality is assumed. Complete caller locals and
reached St survive the exact revert, including the allocated object. Timeout
before allocation retains the original state; statement timeout after successful
allocation retains the new state. These are distinct actual execution paths.

Controls cover empty/binary/33-byte data, both pipelines and static modes,
a real assignment prefix retaining false rather than restoring true, old
object0 versus fresh object1, every existing populated field, exact payloads,
and wrong payload/state/local/pointer negatives. The supplied intrinsic existing
revertData constructor executes independently: empty bytes give plain revert,
nonempty bytes give revertWith. There is no new payload emitter, catch selection,
compiler-choice proof, memory-layout relation or inferred target rollback.

First literal-application closure:880 exact standard axiom sets, all858 prior sets unchanged
(including832 predecessor sets). The original858 pin file, native checker and
bounded runtime runner are byte-exact. New22 pins and an additive checker enforce
both their prior SHA bindings and every native guard, adding the new core root.
Raw failed attempts are retained: initial missing monadic reductions, control
abbreviation/reserved identifier, and duplicate declaration insertion; all were
fixed without changing statements or budgets. Final check passed54.959s with
peak aggregate RSS1298812928 and cgroup628375552bytes, confirmed stopped, all
sources/config and108 prior container records unchanged. Lean4.24.0/Lake5.0.0-src
and actual KeySort2-job output remain decisive runtime evidence.

No new container, cleanup, cache copy, budget/profile/exclusion change or goal
mutation occurred. All original Work G20-G23 and Backfill A/B remain partial.
Canonical SourceSpec/V07/type/layout/ABI/body/linkage/runtime-frame/bytecode/
admission and reserved-owner applications and mandatory full/default/Decision/
Suite/literal-wrapper/executable-refresh checks remain open. Kernel component
execution is distinct from pinned compiler/EVM adequacy. Integration-dependent
commit and committed handoff remain held by the existing ancestry question.


The same checkpoint additionally applies real effecting Source ABI arguments to
rethrow. `expression_rethrow` has only individual actual Source evaluation and
reached heap lookup premises; `mixed_complete` discharges them from checked
SourceAbi execution and allocation, rather than assuming whole preservation.
All three objects (old0/hash1/result2), next3, full local/state and every prior
vector field are retained. Exact packed70-byte data reaches the independently
supplied intrinsic revertWith; wrong320-byte canonical data is discriminated.
An actual horizon6 failure retains the argument local write and prevents both
hash/allocation and rethrow. There is still no compiler selection/catch claim.
Final extended closure passed57.032s,887 standard sets: all858 base and first22
sets unchanged,29 new sets total. Peak aggregate RSS1306865664, cgroup636301312
bytes. An additional missing pure reduction failure is preserved and fixed
without any budget change. A separate alternate index records the new overlay;
the original default staged tree63b and its binary identity remain preserved.


## Standard ABI rethrow application (2026-11-01)

Independent G21/Backfill work while existing Q-ANCESTRY-099 remains pending.
Default tree63b/index bytes and prior alternate tree51141/index bytes, all prior
97source/blob bindings and old sealed packages were verified/saved first. A third
index records this overlay; no commit/ref/ancestry/goal/runtime change occurred.

New SourceStandardRethrow consumes actual SourceAbi.literal_execution(false),
SourceRethrow.fromExpression/expression_rethrow and Heap.alloc_get. Populated
standard5-argument execution consumes SourceAbiControls.mixed_complete(false):
actual returned address2, complete320-byte payload, reached caller-false locals
and whole Source state. Old0/hash1/result2, allocator3 and all existing balances,
storage/transient/journal/heap/events/logs/fnLocals observations remain. Reversed
execution consumes its producer. Full32-byte words160/224 vs reversed256 are
transported from actual rethrow payloads. Actual packed/reversed/stale-pointer
runs differ by checked bytes/lengths/order, without hash/profile premises.
Empty/binary/33-byte standard literals yield64/96/128-byte payloads:empty input
is not raw empty revert. Exact allocation/argument/statement timeouts retain
untouched state/reached local effects/completed allocation respectively.

First run FAIL1 on two rewrite details; actual failed source bytes/raw log are
retained. Revised closure PASS55.396s,913 standard sets:all887 prior sets unchanged,
26new (7core/19controls). Peak RSS1293131776,cgroup619921408bytes; confirmed stopped,
source/config/108prior-container metadata unchanged. No proof/fuel/node/test/time/
resource-budget change/newaxiom/sorry/native shortcut. Original858/29pin files,
native/887checkers and runtime runner/config remain byte-exact. New SHA-bound
additive checker retains every native guard, adding26disjoint standard-only
scoped sets/new core root. Original81 case intents remain with new corruption
controls. Initial checker construction had a quoting failure, retained and fixed
without changing production guards. Same12GiB/no-swap,CPU1/serial-j1/cache-off,
600s,805306368admission/540000000reserve remain. All original queues and canonical
SourceSpec/V07/type/layout/ABI/body/linkage/frame/bytecode/admission/reserved-owner
applications remain partial; mandatory and raw-global failures are not waived.
Supplied intrinsic revertData is not compiler/catch/frame/ABI adequacy, nor target
world rollback. Goal and integration holds remain untouched.


## Continued G21 reference-signature rethrow (2026-11-01)

After sealing/reviewing the standard checkpoint, a further independent
application consumes actual selector/signature/memory-signature producers.
All previous indices/seals/102source bindings were verified/saved first. No
new primitive, decoder, emitter, interpreter or goal/ref/ancestry change.
The memory signature really allocates STRING1,hash-inputBYTES2,resultBYTES3,
allocator4. Actual returned pointer3 reaches canonical rethrow; complete Source
locals/world/heap/journal/transient/events/logs/fnLocals are retained. Literal
and memory signatures have identical324-byte payloads but different complete
machines; pointer/heap identities are not projected away. Literal-selector and
empty-signature prefixes differ by checked exact bytes, not a collision premise.
Stale pointer2 reads actual binary input, not output324. Argument horizon7
retains string allocation and localfalse before hash/result; statement0 retains
all allocations; expression0 none. Removing4prefix bytes is ONLY an observation
matching actual standard-rethrow body, never full-state equality. Independently
supplied intrinsic revertData is not compiler/catch/frame/rollback adequacy.

First check FAIL1 from reserved prefix identifier and combined-goal reduction;
source/raw retained. Renaming and a small byte-list lemma fixed it without
changing budgets. Final closure PASS57.462s,930standard sets:all913 prior exact
sets unchanged,17new. Peak RSS1261473792,cgroup593342464bytes, sources/config/
108prior-container records unchanged, runtime confirmed stopped. Same runtime,
12GiB/no-swap/CPU1/serial-j1/cacheoff/600s/805306368admission/540000000reserve.
New additive checker binds unchanged913checker/26pin bytes, retains the entire
prior native guard chain and adds17strict disjoint standard-only namespace pins.
Prior91case intents retained with8new negative controls. Four task-owned index
snapshots are distinguished; integration/Q/blockedgoal and all original queue/
mandatory/source-prerequisite holds remain. No new compiler/EVM test or whole
lowering/independent-exhaustion claim.

Finder/skeptic review confirmed guarded-import logic; skeptic identified possible
bytecode writes outside supplied environment. Import now temporarily suppresses
bytecode and restores caller state; an actual false-caller-flag/no-local-bytecode
positive probe exercises it. No existing cache file is removed or changed.


## Actual transient statement / ABI declaration / rethrow (2026-11-01)

Independent G21/G23/Backfill A-B application, Q-ANCESTRY-099 still held. Prior930
exact sets/99test intents/four indices/seals/source bindings verified/preserved;
separate fifth index only, no commit/ref/goal operations. Actual RItems executes
expr(setScratch), declInit(ABI literal), rethrow(here), with nps1 and explicit
bool→bytes-memory/bool frame. Actual enclosing execS block also executes it.
Individual steps are proved, no desired whole-execution premise/new interpreter/
emitter/decoder. Both pipelines/packed-standard/arbitrary literal bytes;
fuel+10(items)/fuel+11(block) are syntax horizons, not admission cutoffs.

Opening retains populated balances/persistent world/oldheap/events/logs/fnLocals,
uses published transaction end, then records OTHER-owner sender transient write
as caller prefix. Actual self assignment adds journal entry2. ABI returns ref1,
old0/result1/next2 and WHOLE reached Source.St retained. Outer EM error frame is
L0; explicit declaration result separately proves inner bool parameter/reference
locals. Full16-field vector/empty,binary,33-byte cases preserve exact bytes.
Actual self read, other-owner preexisting prefix read and persistent saved-path
read retain complete state. Static refusal BEFORE allocation; horizon5 timeout
retains self write only; zero untouched. Draft horizon6 was actually sufficient
to continue: failed claim/raw diagnostics retained and corrected honestly.

Raw rethrow retains self transient write. Explicit published enter-mark rollback
removes ONLY that journal operation, preserving sender caller prefix/journal1
and BOTH heap objects. Separate endExecution clears both owners/journal while
preserving wholeworld/heap/events/logs/fnLocals. Wrong automatic rollback and
binary payload negatives discriminate actual executions. No source halt→rollback,
compiler/catch/frame/bytecode or SourceSpec adequacy inference.

Check1FAIL1 on monadic/frame/nps rewrites and horizon6. Check2PASS18new sets, then
unused simp arguments removed. Actual enclosing block check3FAIL1 final pure-error
reduction; check4PASS55.921s,949exact standard sets(all930prior unchanged,19new),
no newmodule warnings. AggregateRSS1279332352,cgroup605085696bytes; source/config/
108priorcontainer records unchanged, stopped. Same12GiB/no-swap/CPU1/serial-j1/
threads1/cacheoff/600s and proof/fuel/node/test budgets. Forecast192→256→320MiB
revised BEFORE extra checks to disclose retained cumulative logs; original
805306368admission/540000000reserve unchanged. No newruntime/deletion.

SHA-bound additive checker preserves every prior930checker/pin/resource guard,
adds19strict disjoint standard-only scoped sets. All99priorcase intents with8new
negatives(107total), plus helper positives. Reviewer recommended bytecode probe
cover ALL imported checker cache files; implemented without touching old scripts.
Initial pin extractor omitted the empty-axiom print branch; diagnostic and failed
positive retained, grammar corrected to production grammar before generating pins.
Independent finder/skeptic source/script reviews found no remaining semantic or
guard issue. All G20/G21/G22.01-.05/G23 and BOTH backfills PARTIAL; canonical
SourceSpec/V07/type/layout/ABI/body/linkage/runtime-frame/bytecode/admission/
reserved-owner applications and mandatory gates remain open. No unchanged failed
Decision/full retry, no goal/reactivation/ancestry integration. Final gate/review
outcomes and exact commands in additive handoff.


## Continued mixed effecting ABI after transient prefix (2026-11-01)

After independent source/artifact reviews and sealing prior949/107 checkpoint,
continued original G21/G23/Backfill A-B application in separate sixth index.
Prior110sourcebindings/indices/seals preserved first. Actual evalArgs at WRITTEN
state performs literalbinary,localfalsewrite,localreadfalse,33-byte literal and
hash allocation1, not a fixed-populated equation applied at a changed world.
Existing typed encode_fixed_bytes32/digest laws discharge encoding at that reached
state; SourceAbi.execute yields ref2/localfalse and old0/hash1/result2/next3.
Actual resolved RItems expr(transient assignment),declInit(mixedABI),rethrowhere
executes at horizon20,nps1. Full17-field vector and WHOLE Source.St preserve
balances93/7, code0/nonce1, persistentsavedtrue, self transientfalse→true,
preexisting sendertrue, journal1→2, every allocated byte/object,events/logs/fnLocals.
Both pipelines and packed70/standard320 exact complete ordered data. Declaration
separately exposes ref2/falsebool; outer Source error frame remainsL0.

Static prefix refuses BEFORE argument effects. Actual argument6timeout retains
inner falsebool+written state before hash/allocation; item9timeout retains
written state but discards inner locals through published sub boundary.
Source rawhalt retains transient write. Explicit marked rollback preserves sender
prefix/journal1 and all3heapobjects. Separate transaction end preserves whole
world/heap/events/logs/fnLocals; actual self readtrue then end self/senderfalse.
Wrong original fixed-base snapshot(journal3 versus actual2) and reversedpayload
negatives discriminate reached input and exact argument order without hash or
profile premises. No new encoder/decoder/interpreter/payload emitter; no whole
execution preservation premise, compiler/catch/frame/bytecode or SourceSpec claim.

Check1FAIL1: ambiguous unqualified values rewrite and200000-heartbeat failure
from cases on a large payload equality. Qualified existing definition and used
existing revert/error constructor injectivity, no budget increase. Check2PASS
56.059386157s,963exact standard sets(all949prior unchanged,14new), no newmodule
warnings. AggregateRSS1294794752,cgroup624480256bytes; source/config/prior108
container records unchanged andstopped. Same existing runtime,12GiB/no-swap/CPU1/
Lean-j1/threads1/cacheoff/600s,805306368admission/540000000reserve, all original
proof/fuel/node/test budgets. Forecast256MiB based on warm closure/log/export
sizes recordedbeforewrites. No newruntime/cachecopy/cleanup/ref/goal operations.

SHA-bound checker preserves all949guards/pins and107priorcase intents; adds14
strict disjoint scopedstandardsets and8negative controls(115intents), plushelper
positives and fullchain bytecodefalsecallerprobe. Independent finder/skeptic
source/script reviews and finalartifact review recordedseparately. All original
Work/Backfill parents remainPARTIAL with canonical SourceSpec/V07/type/layout/ABI/
body/linkage/runtime-frame/bytecode/admission/reserved-owner and mandatory gates
open; rawfailures/publiccomparisons separate. Q-ANCESTRY-099 stillunanswered,
not resubmitted; original blockedgoal unchanged, no completion/exhaustion claim.


## Actual effecting emit at reached transient/caller state (2026-11-01)

Independent G23/Backfill application; Q-ANCESTRY-099/blockedgoal unchanged. All963
prior exactsets/115caseintents/114sourcebindings/sixindices/seals verified before
writes; separate seventhindex. One consistent EXISTING SourceEmitControls.E with
actual event/state declarations is reused. Opening uses published endExecution
then actual sender transient journal operation as callerprefix; actual typed
expr(setScratch) writes self before event. Actual evalConvArgs and encodeVals are
proved ATWRITTEN, not by applying an old fixed-populated equation to anotherinput.
Actual RItems assignment→emit→nil runs with nps1,horizonfuel+13, returnsfalsebool
locals and WHOLE reached Source.St. Sufficient syntaxhorizon is not an admission
cutoff. Hash binary object1/old0/next2,balances93/7,code0/nonce1,persistentsavedtrue,
selfscratchfalse→true,preexisting sendertrue,journal1→2,events/fnLocals retained;
complete16-field vector includes exact selector+fullordered3worddata logprepend
ANDoldlogs. No new encoder/decoder/interpreter/payload emitter or wholeexecution
preservation premise.

Both pipelines. Actual reordered localread-beforewrite produces hash,true,false
rather than hash,false,false; full actual event executions differ by complete
payload using existing byte-inequality/prefix-cancellation laws, no hash
noncollision/profile premise. Approved eraseLogs projection retains returnedfalse
locals,completeworld/transient/heap/events/fnLocals; erased result is NOT opening.
Raw machines with different logs are not identified. Direct static emit executes
actual arguments and encoding before emptyrevert, retaining hashheap/localstep
observations. Entire static sequence refuses FIRSTtransientwrite before event:
allocator1 versus directstatic2, distinct error-state boundary. Zero and actual
argument-timeout/item4 cases retain exact opening/written state.

Explicit enter-mark journal rollback removes ONLYselfoperation preserving sender
prefix/journal1 andheap. After normal emit it ALSO retains the newly prepended
SOURCElog; this is published execution-component rollback, NOT EVMlog/frame
adequacy. Directstatic rollback retainsoldlogs. Separate endExecution clears both
owners/journal and preservesworld/heap/events/logs/fnLocals; real endreads false.
Wrong automaticrollback and erasedopening controls discriminate actual runs.

Check1FAIL1: typedUInt8binary versus intrinsicListInt observer mismatch and
200000-heartbeat reduction of erasedtuple. Switched to existing exact integer
byte observer and consumed logged_erasure instead of forcing fullreduction;
no budget changes. Check2PASS26newsets with2unusedsimp warnings. Actualemit
constructor madeexplicit so itemproof consumes its eventstep; check3PASS58.5955s,
989exactstandardsets(all963prior unchanged,26new), no newmodulewarnings.
AggregateRSS1306808320,cgroup613330944bytes; source/config/prior108containers
unchanged,stopped. Same12GiB/no-swap/CPU1/serialLean-j1/threads1/cacheoff/600s and
original proof/fuel/node/test budgets,805306368admission/540000000reserve. Entire
320MiB forecast measuredbeforewrites; no cleanup/newruntime/cachecopy.

SHA-bound additive checker preserves all963priorguard/pinbytes and115caseintents,
26strictdisjointscopedstandardsets/8newnegatives(123intents), plushelperpositives
and fullchain bytecodefalsecallerprobe. Independent read-only finder/skeptic
source/script/artifact reviews and final outcomes recorded in additive handoff.
All WorkG20-G23 and BackfillA/B remainPARTIAL; canonical SourceSpec/V07/type/layout/
ABI/body/linkage/runtime-frame/bytecode/admission/reserved-owner applications and
mandatorydefault/Suite/full/literal/executablegates remainOPEN. Historical125,
rawglobaldocs/pins1/frozenwhitespace2 notwaived; publicequalityseparate. No goal
reactivation/reset/ref/commit/ancestry operation or universal exhaustion claim.


## Continued actual event argument panic at reached prefix (2026-11-01)

After independent reviews/sealing of emitcheckpoint, continued originalG21/G23/
Backfill application in separate eighthindex. Existing ONE SourceEmitControls.E
is reused; old118sourcebindings/seventhindex/seals preserved. Real Source
convertedarguments atWRITTEN execute hashbinary allocation1 then actual division0
panic, BEFORE encoding/staticguard/logprepend. Both pipelines/directstaticmodes.
Actual RItems uses the published transientexpr→failingemit sequence,nps1,horizon13,
consuming individually proved steps; no desiredwholeexecution premise. Inner
argumentlocals remaintrue (failure before localwrite), outererrorframeL0; complete
16-field vector balances/code/nonce/persistentsaved/transientself+sender/journal/
old0/hash1/next2/events/OLDlogs/fnLocals andWHOLE Source.St retained.

Exactsourcepanicbytes transport to existing Semantics.encodePanic0x12, and the
published intrinsic decodePanic observes code0x12 on ACTUAL producedbytes. This
is lossy byteobservation only, not Sourcecatchselection/ABI/compiler/body/frame/
bytecode/admission adequacy; RStmt atthispin has no suppliedtry/catchinterface.
No new decoder/encoder/error emitter/hashpremise. Empty/assertpayload and skipped
hashsnapshot negatives distinguish realfailure. Directstaticpanic still follows
hashprefix; entirestaticsequence rejectsFIRSTstore with emptyrevert beforeargs.
Zero timeout separate. Explicit markedjournalrollback preserves callerprefix/
heap/oldlogs; rawpanic doesNOTrollback. Transactionend separately resets both
owners/journal and preservesworld/heap/events/logs/fnLocals; actualreadsfalse.
ApprovederaseLogs observation retains sameexacterror and nonlogeffects.

FirstclosurePASS56.595432746s,1004exactstandardsets(all989prior unchanged,15new;
original963 also unchanged),no newmodulewarnings. AggregateRSS1301069824,
cgroup622845952bytes; source/config/prior108containers unchanged,stopped. Same
existing12GiB/no-swap/CPU1/serialLean-j1/threads1/cacheoff/600s,allproof/fuel/node/
testbudgets,805306368admission/540000000reserve. Entire256MiBforecast recorded
beforewrites withheadroom. No cleanup/newruntime/cachecopy/ref/goal operation.

SHA-bound checker preserves all989guards/pins/123caseintents;15strictdisjoint
scopedstandardsets plus8newnegativecontrols(131intents),helperpositives/fullchain
bytecodefalsecallerprobe. Independent read-only finder/skeptic source/script and
artifact reviews recordedseparately. All G20-G23/BOTHbackfills remainPARTIAL;
canonicalSourceSpec/V07/type/layout/ABI/body/linkage/runtimeframe/bytecode/admission/
reserved-owner andmandatorygates open. Historical125/rawdocs-pins1/frozenWS2
retained,publicequality separate. Q-ANCESTRY-099 unanswered/notresubmitted; blocked
goal identity/objective unchanged, no wholelane/independent-exhaustion claim.


## Valid dynamic-memory RawBytes emit at reached prefix (2026-11-01)

Independent originalG21/G23/Backfill application, separate ninthindex. All1004
prior exactsets/131caseintents/eightindices/122sourcebindings/seals preserved
beforewrites. SAME SourceEmitControls.E/bytesEvent and published transient/caller
opening/written used. Actual literal→bytesmemory implicit conversion allocates
freshobject1 via real evalConvArgs, values expose typedmemRef1; encodeVals reads
that REACHED object via bytesOfRV/heapBytes. Individual argument/encoder steps
proved, then actual execS and RItems transientexpr→RawBytes emit,nps1,fuel+13,
returnedboollocalsTRUE and WHOLE Source.St. No assumed wholeexecution relation,
newencoder/decoder/interpreter or sourcepayload/admissionbound. Arbitrarybytes
proof; empty,binary0/255/128,33-byteboundary instantiated.

Exactselector+entireSource.abiLayout[(true,bytes)] logprepend retainsoldtail.
Published SourceAbi.single_dynamic_bytes transports full offsetword32,lengthword
and entirepad32bytes with NO lengthpremise. Full16-field vector retains balances
93/7,code0/nonce1,persistentsavedtrue,selfscratchfalse→true,preexisting sendertrue,
journal1→2,old0bytes[0,255],fresh1content,next2,events/logs/fnLocals. Boundarydata
lengths64/96/128. Actualvalidstale0 emits oldtwo-bytepayload (not malformed);
freshbinary differs by FULLpayload; pointeridentity negative independently
refutes1=0 evenwhencontentcouldcoincide. Actual reversedbinary execution and
wronglengthword/padding perturbations discriminate fullpayloads without hash
noncollision. Deliberately malformed99 yields realencodingstuckbeforestatic,
not an admittedSourceSpec state or EVMrevert.

Directstatic VALID emit allocates/encodes before emptyrevert; whole staticprefix
refusesFIRSTstore beforeallocation. Zero anditem4 argumenttimeout retainexact
opening/written respectively. ApprovederaseLogs observation preservesreturned
locals/world/heap/nonlogfields. Explicitmarkedjournalrollback restoresonlyex,
retainscallerprefix/heap/newSOURCElog; transactionend separately clearsbothowners/
journal,preserveswholeworld/heap/events/logs/fnLocals,actualendreadsfalse. No
Sourcehalt→rollback, compilerselection/catch/body/frame/ABI-bytecode/admission or
externalEVM adequacy inferred; unsupportedaggregateencoding not invented.

Check1FAIL1 onlyidentitynegative rwframe versusstaticfalseframeupdate. Fixedby
specializing actualtypedproducer equality to exactframe-shaped leftside, without
changing itsstatement orbudgets. Check2PASS59.224314939s,1032exactstandardsets,
ALL1004prior unchanged/28new,no newmodulewarnings. AggregateRSS1292259328,
cgroup613130240bytes; same existingruntime/source/config/prior108containers
unchanged,stopped. Lean4.24.0/Lake5.0.0-src+797c613/KeySort2-jobPASS recorded.
Original12GiB/no-swap/CPU1/Lean-j1/threads1/cacheoff/600s/allproof-fuel-node-test
budgets and805306368heavyadmission/540000000reserve unchanged. Whole256MiBforecast
recordedbeforewrites, withinoriginal805MBallocation. Aftersecondbuild freespace
fallsBELOW nextheavybuildadmission; NO furtherbuild attempted. File-only checks/
metadata/export remainwithinrecordedwholeforecast andpreservereserve; no guard
lowering/cleanup/newruntime/cachecopy. Actualfloor/shortfall inadditiveevidence.

SHA-bound newchecker preservesall1004guards/pins/131caseintents,28strictdisjoint
scopedstandardsets plus8newnegatives(139intents),helperpositives/fullchain
bytecodefalsecallerprobe. Finder/skepticsource/script/artifactreviews recorded
separately. All WorkG20-G23/BothBackfills remainPARTIAL withcanonical SourceSpec/
V07/type/layout/ABI/body/linkage/runtimeframe/bytecode/admission/reserved-owner
andmandatorygates open. Historical125/rawdocs-pins1/frozenWS2 failures retained,
completepublicequality separate. Q-ANCESTRY-099 stillunanswered/notresubmitted;
goalunchangedblocked,no ref/commit/merge/push or wholelane/exhaustion claim.


## H1/H5 checked source-boundary delivery (2026-11-02)

H1 supersedes the former source-only storage allowance: the two extra frozen
checkouts' regenerable `.lake/build` directories were removed under the writer
lease. Sources, commits, current warm outputs and sealed handoffs remain.
Actual disk availability increased from 1246228480 to 4216299520 bytes. Page-cache
reclaim returned permission denied; measured RAM nonetheless exceeded the new
4 GiB reserve throughout. The aggregate 12 GiB/no-swap cap, CPU1, Lean `-j1`,
threads1, disabled optional artifact cache, 600-second wall and every proof,
fuel, node and TestSuite budget remain unchanged.

Nine historical source-only drafts now kernel-check in their concrete public099
application tree. The statement-preserving repairs add explicit intrinsic Bool/
Nat types, unfold the existing paid state, and consume its checked other-account
frame law. They do not change any expected observation or add premises. Actual
163-module H1Audit closure passes, including all old finite-prefix declarations:
1209 exact standard-only axiom sets, all 1032 predecessor sets unchanged, 177
new sets. Its complete theorem inventory agrees with actual `#print axioms`
output. Actual Lean 4.24.0 and Lake 5.0.0-src+797c613 plus passing two-job KeySort
output precede the closure. This is component evidence, not the mandatory full
build or compiler/EVM adequacy.

The checked clients cover event execution/end/reentry; owner-isolated nested
rollback/commit and later writes; exact static/timeout followed by explicit
caller rollback; actual reached nonzero, rejected, same-owner and zero transfers.
In particular zero distinct-owner transfer retains the complete world while
adding two journal entries; same-owner zero is complete ExecState identity.
Both pipelines, arbitrary complete event payloads and existing empty/binary/
33-byte controls remain. Raw halts never imply automatic rollback, and supplied
CallFrames never establish admitted external calls.

Independent finder and skeptic reviewed the actual proof repairs and evidence
checker. Confirmed checker defects were fixed: exact source/control/pin
inventories; actual runtime image, user, cwd, name, complete environment, mounts
and labels; framed log decoding and prefix/cumulative hashes; sample extrema,
600-second observations, cgroup peak and exact tool/target order. One positive
and 34 corruption controls pass. Layer/orphan/strict automatic and correctly
invoked NUL-inventory trust gates pass. Initial legacy-test invocations missing
required fixture arguments, plus incompatible historical root-specific fixtures,
remain recorded failures; no legacy guard was relaxed or historical seal edited.
Raw docs/global pins remain exit1. Complete public099 lists are equal (86 docs
findings, 410 pin notes); frozen comparisons still add 14 docs findings and 396
pin notes. Owned whitespace passes separately from historical incoming failures.

H5 resolves ancestry delivery: the owned checked099 patch is committed onto the
canonical 7c branch without merging histories. Its concrete validation prerequisite
is public099 `099bfbe185731c354b12a40f28ccf5d98534c779`; in particular canonical7c
lacks the published `Semantics/AbiEntry.lean` consumed by the adapter. Reserved
producer code is not copied into this patch. Coordinator integrates and performs
combined-tree gates. Published master observed this turn is
`469acaced9d0d24959d247365e685f687367eea5`; Source execution and native Decision
producer code are unchanged from099, so no supported repair justifies repeating
the fully-warm Decision timeout. Browser-only wasm GMP changes are not a native
repair. Historical full/Decision exit125 and current default/full/Suite/literal
wrapper/executable-refresh boundaries remain unresolved.

H10 transfers G22.01 typed source calls and G22.02 source callbacks to
compiler10/readonly-external. This worker does not start those clauses and will
consume exact coordinator-relayed checked packets. Existing intrinsic controls
remain evidence only. G20, G21, G22.03 creation, G22.04 library context, G22.05
world composition and G23 all remain partial; Backfill A/B have additional checked
components but remain partial at their actual source/target applications.
Canonical SourceSpec/V07/type/layout/ABI/body/heap/linkage/runtime-frame/bytecode/
admission and reserved-owner premises remain open. No whole-lane completion,
source-call/callback application or external solc/EVM adequacy is claimed. The
existing blocked goal identity/objective is untouched.


## H10 ABI handoff and G20 exact result reflection (2026-11-02)

The later human H10 update transfers G21 ABI/calldata and exception lowering to
V13. No new G21 work is started. Existing checked modules/pins/source packets are
available for coordinator exchange; their partial ABI/SourceSpec/decoder/frame
limitations remain. Retained work is G20,G22.03-.05,G23 and Backfill A/B;
G22.01/.02 remain with compiler10/readonly-external. This supersedes the earlier
same-day retained-G21 ownership paragraph, not its historical evidence.

New `CallableReflection.success_iff` reflects an observed successful intrinsic
call to the exact returned World and typed value under explicit result-observer
injectivity. It derives from actual World.call/observeEntry, not an assumed whole
execution relation. `tagged` retains both length and full bytes. Actual funded
installed-body clients retain93/7balances,saved3,scratch9 and exactbinaryreturn;
a same-body alternative decoder gives the same lossy length observation while
its complete bytes differ. Wrong double-payment observations are refuted. No
source signature/body/frame/linkage or ABI equivalence follows from injectivity.
Eight new precise standard axiom sets preserve all1209 old sets unchanged.

The first full new closure failed: the new import was incorrectly placed after
a module docstring. That import order was fixed without changing the proof or
statement. Simultaneously cumulative reused-container console exceeded the
32MiB API response cap (gate125/actual1). Failed record and rawpartial retained;
exact decimalUnixnanosecond StartedAt retrieval recovered the complete invocation
log. A prior RFC3339 API query returned500 and is retained. The reviewed collector
now requests ALL console since the actual engine start, binds its exact query,
previousfinish/start/finalruntime identity and framed bytes, and keeps the SAME
32MiB per-response limit. No logs, runtimes or evidence were deleted, no time/
proof/resource limit increased. A stale topological list then failed preflight125
before runtime selection; regeneration retained exactly the same164targets.
The corrected164module closure passes;1217exactsets,all1209old unchanged,41current
corruption controls including seven exact-window negatives. Historical mandatory
Decision/default/full holds are unaffected by this logging repair.

Artifact review identified a naming ambiguity: the first `original.patch` is the
single H5 commit on7c, not the entire frozen-base diff. Its immutable seal is
preserved. Additive `checkpoint-h1-delivery-addendum-20261102` provides the full
frozen-base patch and exact incremental/full/bundle scope descriptor. Incoming
published prerequisites in the full frozen diff are not all V08-owned changes.
Coordinator integrates, with actual concrete-tree combined gates still required.


Current099 Suite attempts now have concrete evidence: the cold run stopped at
TermLaws.Storage (161targets complete), and the same-key warm run stopped at
LeafShare (209complete). Both retain gate125/actual137 at600s, confirmedstop,
source/configunchanged, no reportedOOM and parentlifetimeOOMcounters0. Durable
completed-prefix manifests bind successful logsegments and actualolean hashes;
these do NOT pass the Suite or justify Decision/default retry. Latest owned
confirmation after those attempts is PASS164targets/1217exactsets, all1209old
unchanged;43corruption controls preserve owned-vs-Suite separation. Actual per-run
target snapshots are now retained, and graph import restores bytecode flags.

Further retained G22.03 source work is NOT exhausted: published
`Source.Semantics.deploy` (Semantics.lean:147), `construct` and the checked
`Source.SemanticsExamples.GAB` constructor-order producer provide a concrete
ready source-deployment application. Source.Eval's expression cases alone are
not the complete source-world execution interface. Next applications should
retain the full populated Source machine, code installation, explicit revert
rollback versus timeout, heap clearing and constructor pipeline order, then
relate only genuinely supplied intrinsic/frame/layout facts. No such new
application is claimed checked by this checkpoint. Canonical constructor/try-new/
SourceSpec/V07/bytecode adequacy and all mandatory final gates remain open.

## Master integration review (2026-11-02)

Head `a7c42a2d` (canonical `7c3c8274`, the checked public099 adapters
`c6d3aa15` and the G20 reflection commit) was merged onto master. A read-only
finder and skeptic found no trust hole, vacuous statement, orphan or layer
violation. Confirmed findings and their resolution:

- Nine `SourceTransient*` headers still said "UNVALIDATED DRAFT" although the
  default build kernel-checks them; the headers now say so.
- The skeptic's reading of the claims, recorded here instead of upgraded:
  `CallableReflection.success_iff` is an intrinsic `World.call` fact
  (injective `observeEntry`), not a Source relation; the Source modules are
  one-step unfolding equations over the published semantics with
  sub-executions as premises; no V08 module runs `Source.runTx`
  (`SourceTransient.endExecution` restates its end-of-transaction step); some
  expected ABI payloads are computed with the same `Source.abiLayout` helpers;
  Source fixtures and intrinsic entries are written to match, with no theorem
  linking them. The docs/README.md entry states this boundary.
- The `scripts/v08-*` validators and their `.test.py` files read VM-only
  paths (VM location `v08-*`) and are not wired into CI, so the
  `scripts/v08-*axiom-pins.json` pins are checked only in the lane VM;
  `scripts/AxiomAudit.lean` and `check-axiom-pins.mjs` (unchanged count) still
  cover the axiom whitelist. The 1,577 `#print axioms` lines are unguarded
  and pin nothing in the Lean build.
- Module-map rows were normalized; the stale counts at the top of this file
  are historical.

## World images, catalogue, creation and library frames

Integrated from the v08-world-lowering lane (2026-11-03).

- `WorldImage.lean`, `WorldReset.lean`: an account/session image (typed installed
  stores, funds, code roles) and its transaction-end reset transport, relative
  to `ResetInputs` (assumed, not proved) and an arbitrary `StoreRelation`.
- `WorldCatalogue.lean`, `WorldCatalogueTransport.lean`, `WorldImageAccess.lean`:
  `assemble` builds an initial `ContractWorld.World` from installed-code
  witnesses; `assembled_image` and `installed_store` (typed store lookup).
  The only concrete instance is the one-slot relation of `WorldResetControls`.
- `LibraryFrameTransport.lean`, `LibraryIntegerTransport.lean`,
  `WorldContextComposition.lean`: library calls hold for any world but cover a
  fixed observer entry (empty body, or one integer literal); static refusal; no
  second payment.
- `ConstructorScalarTransport.lean`, `ConstructorContinuations.lean`: a
  hand-written scalar `Cell` constructor fixture and `tryCreate` continuations;
  `admitted_construct` does not use its admission premises.
- `CreationPremises.lean`, `LibraryPremises.lean`: producer-premise consumers.
  Their `admission : P8a.Producer …` field makes them vacuous until
  P8-SPEC-LAW1 is resolved; `ssNew_body` supplies the constructor run as a
  producer duty.
- Callable transports (`IntegerCallable`, `PureArgumentCallable`,
  `TupleCallable`, `LocalCallableTransport`, `ScalarCallableTransport`,
  `SignedCallableControls`) and source session/deployment/transaction controls.

Open: proving `ResetInputs`, P8-SPEC-LAW1, the constructor body (`ssNew_body`),
library dispatch, a P1 V3 runtime-frame consumer (the lane's V2 consumer was not
merged). No `Producer` instance exists.

### World-image follow-ups (sched 2026-11-03)

- `WorldImageAccess.account_lookup` / `installed_lookup` keep the exact dependent
  store and the persistent/transient relation; populated before/reset clients
  cover both pipelines. These are image lookup facts, not body, admission or
  compiler adequacy.
- `WorldImageAccess.library_inputs` derives caller/library accounts and roles
  from source catalogue equations and `Image` witnesses; it proves no general
  Source library call.
- `WorldImage` now imports only its projection/source types (no
  `LibraryPremises`, no P8 admission interface). `TimeAligned` states the
  source-global/intrinsic-world clock equation, and
  `WorldImageAccess.timestamp_frame` runs `Source.evalE` on a supplied
  `Context.tx` frame. An image alone cannot discharge the clock obligation (a
  populated `atTime` world has the same image but a different timestamp).

Open: `ResetInputs` stays assumed; layout/reset producers, general library
execution, admission, unit transport and bytecode obligations.

