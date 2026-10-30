# V08: callable, ABI and world lowering

This lane is **in progress**, not complete. The entire frozen
G20–G23 assignment and both backfill items remain open. This checkpoint
recovers the pinned checkout, traces published evidence and adds independent
intrinsic adapters plus source/intrinsic byte observation proofs and inhabited
controls. It adds no axiom, exclusion or replacement source semantics.

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
checks are retained; the largest sampled RSS so far is 2399289344 bytes during
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

The owned modules are registered append-only. All 50 current named theorems
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

## Queue status after the independent proofs

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
