# V16 compiler correctness, transactions and specification transfer

Status: independent backfill extended through recovery checkpoints; full lane
blocked on remaining concrete prerequisites; published memory-call consumer added, final gates recorded below.
Base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v16-correctness-transfer`.
Repository: `/workspace/solidity-lean`.

No final G48–G51 contract is proved. No reserved implementation is authored or
repaired here. Published integration is recorded separately below; V16-authored
shared edits are append-only module/document registration.
The [G01 contracts](roadmap-g01-interfaces.md), [G03 ledger](roadmap-g03-ledger.md),
[G04 restrictions](roadmap-g04-restrictions.md) and
[scope decisions](../solidity-scope.md) remain binding; this lane does not change them.

## Work and backfill accounting

| Item | State and remaining obligation |
|---|---|
| G48 | Blocked: actual independent SourceSpec/admission/lowering instances and full-profile progress are not published; source handoff explicitly leaves SourceSpec open. No new premise is counted as discharged. |
| G49.01 | Partial: actual published memory-call result and populated-input specification/alias/allocator consumers are proved below. Total expression/statement/call/pass composition over the complete approved profile remains OPEN; no producer implementation is repaired here. |
| G49.02 | Blocked: final source lowering and integrated V12–V15 runtime byte/pinned-EVM prerequisites are required. No Bridge application added. |
| G49.03 | Open: full-profile coverage, failure preservation, resource progress, traces and non-vacuity. Toy controls below do not establish compiler coverage. |
| G50.01 | Blocked: actual V14/V15 constructor/creation/runtime-installation composition. |
| G50.02 | Blocked: actual deployment, call, rollback and reachable adversarial transaction composition. The decoded invariant below is only a conditional consequence. |
| G51.01 | Open: calculus rule consumers with exact SolKey correspondence and unchanged Fml.inTarget/verdicts. No reserved rule or closer repaired. |
| G51.02 | Blocked: concrete box/diamond/callback/loop/spec consumers of G49/G50, with matching SolKey correspondence. |
| Backfill A | Independent transaction/reachability induction, exact finite-prefix/certificate composition, history-premise adequacy and actual event/outcome/local-divergence controls are now implemented. Full-profile source/runtime applications remain blocked; see recovery evidence. |
| Backfill B | Actual constructor/G03/dependency/trust accounting and scoped box/diamond/spec consumers with success/exhaustion countercontrols are implemented. Concrete callback/loop/runtime/deployment specification transfer remains blocked. Accounting closes no compiler feature. |

Exact prerequisite evidence: [source-s05.md](source-s05.md), sections
"Well-formedness and progress interfaces" and "Handoff", explicitly leaves
SourceSpec, failure points and full progress open. Concrete fields needed include
independent Parses/Resolves/WellFormed/InProfile, recorded hash preimages,
compiler-independent stipend/failure readings and admission/lowering certificates.
These are requests to their existing owners, not assigned repairs in V16.
No unmerged branches were fetched, imported or cherry-picked.

All reserved Source/lowering/compiler-pass/storage/memory/copy components,
Backend/Scalar, Storage/Hash, Backend/Environment, Backend/Failure,
Backend/Creation, Opcode/Jumpdest/Assembler/Control/Checks/EvmVectors,
Precompiles/Stipend/FixedPoint, external EVM workers, calculus/closer and
frontend/generated-differential/SolKey/TestSuite owners remain read only.
V11→V12→V13→V14→V15→V16→V17 serial integration obligations remain open.
Component completion is distinct from parent closure. Proposed G03 reconciliation:
record these lemmas only as conditional backfill for G49.03, G50.02 and G51.02;
mark no feature or combination discharged.

## Theorems and exact premises

The new [transport module](../../Solidity/Roadmap/V16/Transport.lean) defines no
source, intrinsic or EVM semantics. All names below have prefix
`Solidity.Roadmap.V16`.

| Name | Premises and consequence |
|---|---|
| completed_stable | A consistent existing prefix family, an ordered pair of bounds and a completed source prefix; the larger prefix is equal. |
| completion_at_need | Actual Cert, pass domain, allowed target environment, source admissibility, Forward, Guard and completion; exact events/outcome and target admissibility at that certificate's supplied need bound. |
| event_at_need | Same certificate/domain/environment/resource/Forward/Guard premises and source event membership; target event membership at need. Completion is not required. |
| event_invariant | Actual Cert/domain/allowed environment, source event invariant at every admissible bound, target admissibility and target Guard; target event invariant. Source failure bounds remain included. |
| decoded_invariant | Full PublicCorrectness, source admission/well-formedness/profile, successful compilation, allowed target environment, admissible target resource and target Guard; an invariant over every admissible intrinsic reached-world list transports to successfully decoded target worlds. |

`decoded_invariant` assumes public correctness and therefore cannot establish
it. The supplied `Cert.need` may itself use choice; these lemmas introduce no
new choice, but final bound computability still needs a concrete audit.
The first four theorems have no axioms. `decoded_invariant` uses only
`propext` and `Quot.sound`. No new axioms, sorry, native_decide,
implemented_by or proof-budget increases are introduced.

[Checks](../../Solidity/Roadmap/V16/TransportControls.lean) reuse the existing G07 semantics
and actual identity certificate. Singleton-hash success and exact revert data
are inhabited; success/revert identification and revert-data erasure are refuted.
A loop at every non-exhausted bound has no completion, but an admissible
exhausted bound reverts. The negative control rejects promoting this to
unconditional divergence over all admissible bounds. The two-pass control checks
the actual composed certificate's need and success observation. These controls
are not external EVM tests or compiler constructor coverage.

## Runtime and validation

Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613 (Lean 4.24.0).
The clean checkout initially used branch `work`; the assigned branch was created
from the exact base under the repository writer lock. No unexpected work reset.

The VM has a 16 GiB cgroup limit and currently no swap. Both systemd scope
probes failed (no user bus and PID 1 is tail). Those raw failures are retained;
they are superseded for bounded execution by the managed Docker route:
`ubuntu:24.04`, digest
`sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`,
`--memory=12g --memory-swap=12g`, with observed memory.max=12884901888 and
memory.swap.max=0. Builds use LEAN_NUM_THREADS=1, Lean -j1 via a temporary
alternate TOML, no concurrent LSP/build, and the repository writer lock.
Remaining memory is available to the OS. One existing build/cache tree is reused.

RUNTIME_GATE_PASS: `lake -f lakefile.v16-runtime.toml build Solidity.KeySort`
passed: "Build completed successfully (2 jobs)." Cgroup peak: 25,186,304 bytes.
Transport focused/import closure passed (6 jobs), peak 311,463,936 bytes.
Initial controls check failed due to supplying both conjuncts of toy_forward
where Forward alone was expected; raw failure retained. The corrected controls
check passed (8 jobs), peak 114,647,040 bytes. Final post-pin/two-pass and renamed-module checks passed (8 jobs); the final
log is controls-renamed-final.log in the evidence directory. No per-file Lean MCP diagnostics tool was available;
focused serial Lake checks are used. Cgroup peaks are memory evidence, not
aggregate process RSS measurements. The final controls check sampled aggregate
process RSS every 50 ms: peak sampled RSS 283,764 KiB (including shared mapped
pages); final cgroup peak was 115,216,384 bytes. Whole-lane RSS validation
remains pending.
Disk probe before builds: about 30 GiB free on a 32 GiB overlay; no caches deleted.

Exact-base full doc-path checker fails with 46 missing references; raw output is
retained. The separate no-new-findings comparison is recorded in the handoff.
Layer check passed (174 core modules, none reach elaborators), orphan check
passed (998 reachable, zero orphaned), and staged diff whitespace check passed.
Full bounded run-lean, broader trust gates, external EVM tests and whole-lane validation
remain pending; no missing required gate is counted as passing.

## Independent review

Separate read-only finder and skeptic reviews inspected Transport's actual
statements and proofs without Lean servers/builds. Both found a documentation
overclaim about computability of arbitrary Cert.need. It was fixed to describe
the certificate-supplied bound and retain the concrete computability obligation.
Both found no mathematical mismatch in the five transport proofs and confirmed
they do not establish compiler coverage. Final follow-up finder and skeptic reviews found no new logical or ownership
defect in controls and append-only registration. They required the final
handoff/checksums and post-pin check evidence before any artifact claims.
The docs comparison subsequently found a new Checks basename ambiguity; renaming
the owned module to TransportControls fixed it without editing its existing
owner. Unresolved full-lane requirements stay open.

## Handoff

Evidence directory: `/workspace/scratch/v16-correctness-transfer-evidence`.
The external handoff records final base/head, exact command lines, raw failures,
review follow-ups, patch/bundle paths and SHA-256 checksums. This is a partial
reviewable checkpoint, not a completion of G48, G49, G50, G51 or either backfill.

## Recovery checkpoint 2: independent relational and lifetime induction

The auditor explicitly authorized continuing independent backfill after the
first partial checkpoint. Its artifacts and commit remain unchanged.
New Relational results compose actual Refines relations with identical middle
resource predicates and exact completed Prefix equality. composed_need states
the exact nested certificate bound; composed_completion retains actual Cert,
full middle-domain closure, Allowed, Admissible, Forward and Guard. No arbitrary
guarded transitivity, source simulation or computability premise is invented.

Transactions inducts over the existing intrinsic Lifetime.Trace and Reachable.
trace_transport retains the ordered mapped event list (arbitrary event maps
may erase information; exact observations need a concrete correspondence).
reachable_transport requires actual target constructor/step evidence.
reachable_invariant requires BACKWARD target initialization/step coverage plus
a source invariant and state-predicate reflection, quantifying every target step.
trace_invariant propagates an existing invariant through actual traces.
These are generic induction consequences, not deployment/runtime correctness.
The published intrinsic lifetime model is deterministic, not callback havoc.

TransactionControls inhabits actual deployT, Prog.run, successful commit,
revertWith [9] rollback and wait through the existing definitions. The rollback
run proves exact revert bytes separately: Lifetime.Event does not expose them.
An actual nonempty commit/rollback/wait trace exercises trace_transport with a
proved identity step relation; wrong ordered labels are refuted. Wrong revert
bytes are refuted through NEW completion_at_need. An invalid timestamp invariant
is refuted through NEW trace_invariant on the actual wait-bearing trace.
The local no-failure divergence witness uses exactly Admissible ∧ Forward for
G07's existing loop, and supplies an inhabited resource. Global failure bounds
are retained; the original unconditional-divergence negative control still holds.

Separate read-only finder and skeptic reviews found no proof mismatch. Finder
required branch/ancestry/status rereading AFTER acquiring the writer lock; fixed.
Both reviewers flagged that alternate-config injection only covers direct Lake
commands: the runner now rejects arbitrary scripts/direct Lean and requires
explicit -j1 for lake env lean. Docker limits are asserted before execution.
No new Lean diagnostic MCP tools were available. Focused/import-closure checks
passed for Relational, Transactions and TransactionControls; raw axiom outputs,
final structural/doc checks and measured memory are in the recovery evidence.
Only inherited AST unused-variable warnings were observed, without reserved edits.

The Backfill A transaction-induction and relational-composition obligations now
have independent generic results and actual controls. Event-bearing G01 session
controls, richer scoped spec consumers, machine accounting and full gates are
next; neither backfill nor any G48–G51 parent is marked complete here.

## Recovery checkpoints 3–4: scoped specification consumers and accounting

SessionControls reuses the actual published Source.PS and sessionFrom at its
explicit address, in an explicitly allowed environment. It proves completion
and two events; NEW composed_observation rejects erasure and wrong credit events,
and NEW composed_safety rejects an invalid empty-event invariant. No replacement
Lang or execution semantics is introduced. The existing sample uses toyFixed,
so this is not a pinned-Keccak/full-SourceSpec or full-profile witness. G07's toy
Lang emits no events; that exact missing definition prevents an event-bearing
G07 execution. SourceSpec remains unpublished, not repaired or assumed here.

Specifications supplies arbitrary-context typed box postconditions, diamond
success ONLY with explicit exclusion of the existing exhaustion alternative,
actual admitted commit from diamond/entry/payment evidence, and a consumer from
published function-box invariants through NEW backward reachability induction.
SpecificationControls supplies actual success/commit and exhaustion negatives;
its True/identity invariant application is explicitly a smoke test, not a
nontrivial application specification. Callback/loop and final runtime/deployment
consumers remain prerequisites; Fml.inTarget, rules, verdicts and SolKey maps
remain unchanged. HashHistory consumes the full approved HashPremise to obtain
tail and cross-preimage obligations. The singleton Bool counterexample refutes
joining independent local premises; it asserts no Keccak collision.

The metadata extractor under tests/roadmap-v16 queries actual Lean environment
inductive constructors, V16 theorem statements in the checked imported core
closure, direct type/body constants
and transitive collectAxioms results. ScopedAudit also prints actual axioms for
all 67 theorem declarations in that checkpoint-4 core-closure snapshot. The 295-family/1428-constructor universe is
all Solidity inductives in this checked import closure, not an asserted complete
Solidity source profile. Read-only G03 accounting includes all 175 features,
41 combinations, 98 symbolic combinations and eight G48–G51 checkpoints. Every
one of its 1750 leaf/parent obligations remains explicitly OPEN. No constructor
or feature is discharged by mentioning a generic theorem. Actual statements,
assumed PublicCorrectness, domain/certificate premises, per-run guards, need
computability and missing prerequisites stay visible. No global ledger/pin edit.

Independent finder and skeptic reviews found two accounting defects in the first
draft: old successful metadata could be relabeled with current revision hashes,
and the structural-only boundary string was unchecked. Both are fixed. The
locked runner now records execution-time BEFORE/AFTER exact head, complete Lean
source-tree digest, owned sources, extractor, ledger, toolchain, original config,
runner and accounting hashes; a changed or stale binding is rejected. The report
validates its full schema and exact boundary. Negative tests cover missing actual
constructors/combinations/statements, contradictory claims, wrong revisions,
changed trust outputs, assumed-correctness witnesses, erased prerequisites,
stale/unbound re-snapshots and altered full-profile prose. These are structural
checks supplementing kernel proofs, not a correctness proof or trust attestation.

Raw first proof failures are retained (a case-split equality mismatch and a
rewrite through opaque Prefix.Le; fixed with equality reflexivity and a direct
prefix-length argument). Scoped consumers and controls then passed focused/import
checks. The complete raw axiom audit passed with only the standard propext,
Classical.choice and Quot.sound set; no new axioms or proof budgets. All original
checkpoint artifacts remain intact. Each recovery checkpoint's command logs,
reviews, measurements, committed head and handoff live under
/workspace/scratch/v16-recovery-201ebab8.

The runner now supports the actual run-lean.sh full gate by an exported Bash lake
function via a task-owned BASH_ENV file. Every nested Lake call uses the same
alternate TOML, with explicit -j1 for all libraries and executables. Original
tracked configs stay unchanged; LEAN_NUM_THREADS=1, the asserted 12GiB/no-swap
Docker cap, OS headroom and writer lock remain enforced. Full-gate timeout is
5400 seconds, the existing G02 bound. RSS and actual Lean/compiler process counts
are sampled, not inferred from thread flags. The full gate outcome is pending
until its actual final log; no permission to relax any required gate is implied.

## Recovery checkpoint 5: loop consumers and substantive invariant witness

LoopControls proves preservation at actual TLoop finite iterations/successful
exits, inhabits a typed forever-loop fuel witness, refutes inference of divergence
from one pending horizon, and retains exact revertWith [9]. No loop rule,
semantics or resource profile is changed. NontrivialLifetime, under tests only,
uses NEW reachable_invariant with the published escrow safeInvariant and actual
paymentPossible reachability; a typed world with both flags true is excluded.
This replaces reliance on the earlier True/identity smoke test for substantive
invariant evidence, while retaining explicit identity-model scope: no backend
simulation or runtime deployment is claimed. Its four theorem statements and
axiom prints are audited separately from the core import-closure inventory.

Finder and skeptic found no proof/ownership defect. Finder requested recursive
owned-module discovery, full relative module names, and a nested-owned-file
negative control; fixed. The core inventory also verifies that every discovered
owned module is actually imported, and frozen G03 bytes match the exact base.
The test-only elaborator imports never enter core. The first loop check's two
redundant trailing tactics failed and were removed; raw failures are preserved.

The first cold full run on da76b8e831ddbf9d305b7971f95d530dd06ccac0 exhausted the
UNCHANGED 5400-second bound during default targets (last completed LedgerCut,
active existing Recursion example); exit 124 is a failed gate. TestSuite and
SolKey were not reached. No source error or memory stop was reported, but that
is not a passing full check. Raw output remains full-run-lean-first.log. Later
checks of the revised loop/import checkpoint reuse the single existing cache,
retain the same budget/cap and record their own actual outcomes; the cold failure
is never relabeled green. All final required gates remain open until observed.

Current checkpoint-5 accounting has 74 core-closure theorems and 25 passing
accounting controls. The four test-only escrow theorem audits remain separate.


## Recovery checkpoint 6: callback consumers

Skeptic correctly identified a remaining independently executable scoped callback
consumer; it did not require concrete V12–V15 runtime certificates. New consumers
use published holdsC/ValidT, ExecP and ExecF with their dependent heap extensions.
They preserve successful postconditions, exact halt values/modality reading and
panic exclusion, and reject program/frame invariant violations. Controls inhabit
an actual nil execution, reject a false postcondition through NEW transport, and
construct an actual zero-value transfer violating a false callback invariant.
This is scoped consumption, not a callback rule repair or runtime correspondence.
Selected transfer semantics, Fml.inTarget and SolKey correspondence are unchanged.

The checkpoint-5 full command also exited124 at the unchanged5400-second bound:
default991jobs passed; kernel TestSuite reached Derived20 but did not finish.
Raw full-run-lean-checkpoint5.log remains a FAILED full gate, not a success.
A revised-source final gate retains the same cap, timeout and shared cache.

Both callback reviews passed; they correctly distinguished nil success from
callback resumption. A strengthening now constructs an actual transferResume
under the existing true invariant, changing self balance from0 to1, and applies
NEW postcondition transport at that actual run with its modality still explicit.
This supplies intrinsic callback-resumption evidence, not reentrant bytecode or
external-world coverage. The first nil control proof failed because trivial did
not unfold the modality reading; the existing afterRunTR_ok lemma fixed it.


## Final recovery handoff: independent backfill completed, parent blocked

The revised callback source passed the actual run-lean.sh command under the
unchanged5400-second timeout, explicit-j1 serial policy and asserted12GiB/no-swap
Docker cap: default993jobs, kernel SolkeyTestSuite262jobs, then solkeycheck parsed
377taclets with131 read-bearing annotations and matching table; exit0. Earlier
cold/default and checkpoint5/TestSuite timeouts remain raw exit124 failures.
The final successful cgroup peak was5009735680bytes; sampled worker maxima and
all three gate resource histories are recorded in runtime-summary.json outside
the repository. No changed proof/fuel/node/TestSuite budgets and no new trust
shortcut. Lean4.24.0(commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b),
Lake5.0.0-src+797c613; the preserved KeySort gate completed successfully(2jobs).

The strict checker over explicitly concatenated raw TestSuite timing logs passed
its default300seconds/module:26 timed modules,491 automatic plus61 step-budget
proofs,0manual,11refuted,0pending. Complete TestSuite accounting passed using the
UNCHANGED repository-pinned migration fixture:564=552derived+11refuted+0pending
+0divergent+1excluded,2skip. The initial setup-checkout audit failed because that
layout lacks its sibling pin manifest; raw ENOENT and the separate pinned-fixture
pass are both retained, no fixture/pin/dependency upgrade performed.
Layers:184core/0inversions; orphans:1008reachable/0orphan/0notallowed;
trust:1023sources/246inventoried sites/0findings; noncircular:1256modules/0violations.
The raw full docs checker still exits1 with46missing paths plus37ambiguities.
Complete exact-base/current finding arrays match:zero new AND zero removed,
not a count-only waiver. diff whitespace check passes.

Final scoped inventory has305inductive families,1537constructors and91actual
V16 theorem/dependency/axiom entries (including generated proof auxiliaries).
The explicit ScopedAudit prints87 named consumer/control theorem axiom sets;
four test-only escrow statements/axiom sets remain separately checked. All use
only the standard propext/Classical.choice/Quot.sound allowance or no axioms.
All26 accounting controls pass. All1859constructor/G03/stage obligations remain
OPEN; laneComplete=false. These checks supplement, not replace, kernel proofs.
Fresh final committed-head metadata and checksums are generated after this
handoff is committed. Final gate's checked Lean-source digest must match that
final committed-head inventory; doc-only changes do not alter the Lean tree.

Separate read-only finder and skeptic reviews passed checkpoint6 and its actual
positive callback-resumption strengthening. They used no Lean server/builds.
Confirmed recovery findings and fixes are recorded above; final artifact reviews
are retained in the external evidence directory. Independent A/B, scoped loop,
callback, box/diamond/spec consumers and their controls are now implemented.
Historical statements that those backfills were unfinished describe their earlier
checkpoints, not the final recovery state. They do not imply full-profile closure.

Investigated remaining concrete dependency map (no reserved-owner repair):

* G48: source-s05 leaves SourceSpec state/evaluation preimage history, failure
  budgets, stipendFits and Horizon proofs open; independent frontend parse,
  resolve, WF/profile/progress, Admission.sound/complete and actual Lowering
  certificates remain prerequisites. G07 toy instances are not the full profile.
* G49.01: existing Evm compiler/pass APIs still expose Option/fragment-specific
  Input domains. Actual total approved-constructor Compilation certificates and
  integrated published V12–V15 adapters remain unavailable here.
* G49.02–03: actual Execution assemble/dom/agrees/cert, pinned byte/runtime EVM
  correspondence, approved full-history hashes, compiler coverage and computable
  resource bounds must be supplied without residual fragment admission. Generic
  composition or an assumed PublicCorrectness does not construct these fields.
* G50.01–02: actual source constructor/initcode/artifact/install correspondence,
  creates_table, address/nonce/payment/rollback/code deposit and StateExport
  decode_reach/decode_commutes are needed. Target adversarial/backward interaction
  coverage is not supplied by forward finite-trace transport or deterministic
  Lifetime invariants. Preserve full per-run hash histories across transactions.
* G51.01–02: final applications need those actual runtime/deployment results and
  matching SolKey callback/loop/function-spec consumers. Reserved rule/closer,
  TestSuite, verdict, Fml.inTarget and search-target work is untouched. Scoped
  callback/loop consumers are now present, not incorrectly listed as blocked.

Kernel evidence covers only the precise generic/scoped premises and actual
intrinsic controls named in the checked inventory, plus the separately checked
published escrow safety witness. There are no new concrete external EVM/compiler
or deployment differential tests, no full-profile SourceSpec witness, and no
concrete final G48–G51 theorem. The entire frozen assignment/goal stays BLOCKED;
no exclusion, premise, owner repair, fetch/cherry-pick, merge/push/PR is requested.
No human scope decision is needed to state these published dependency gaps.

Artifacts use absolute VM paths under /workspace/scratch/v16-recovery-201ebab8:
original.patch(full frozen-base diff), recovery.patch, v16.bundle, handoff.md,
handoff.json, gates.json, raw evidence, runtime-summary.json and SHA256SUMS.
The original f9d367860fcee1471de830611b1635851f71e3b7 evidence directory is preserved
and its checksum verification passed. Repository/branch/frozen base appear above;
full final committed head is recorded in the external exact-head handoff to avoid
self-referential commit hashes. Coordinator reconciliation should retain every
G48,G49.01,G49.02,G49.03,G50.01,G50.02,G51.01,G51.02 ledger obligation as OPEN.


## Published-prerequisite recovery 2de14d52

Explicit human recovery authorization permits fetching published master and
integrating91e94ab57305ca055127934fd9e68fe9ea5e6be3 into this isolated task branch.
Earlier no-fetch/no-merge statements describe the prior authorization period;
no unmerged branch, producer repair, default-branch merge or push is authorized.
The published merge preserves35df1dc09d5b47c9d3ef1f472a8049300f3b12b2 and all110
sealed artifacts unchanged. Both independent read-only integration reviewers
verified every reserved file equals published91 and every owned implementation
remains unchanged, with both sides of append-only registration preserved.
This integration itself establishes no new consumer theorem or build success.
New bounded checks and artifact evidence use a fresh directory:
/workspace/scratch/v16-published-2de14d52. The existing source/toolchain cache and
all original raw failures remain intact. Full final import validation is pending.


### Actual published compiler/specification consumer

MemoryCallConsumer consumes Compiler.Compilation.memoryCalls and the actual
Memory.Calls.Program.sound, not a hypothesized preservation oracle. Its eight
named theorems are memory_call_result, memory_call_rep_iff, memory_call_success,
memory_call_spec, memory_call_failure, memory_call_alias, memory_call_small_frame
and memory_call_cursor. The exact printed statements, dependencies and axioms
are retained in fresh revision-bound metadata. Input preserves Memory.StateRepr,
b+requiredFrame≤frame and the reached AllocationInput. Successful output retains
its exact source Out, target run with residual PC0, complete protected stack,
StateRepr, BaseExtends and GrowsAllocator. Source box/specification and actual
success remain explicit premises, inhabited in the controls.

The broad public Agrees alternatives for panic/payment/divergence are not
silently removed. The selected producer's stronger GrowingResult has represented
success or exact empty revert; memory_call_failure proves that actual failure
class, rather than mapping arbitrary panic, divergence or revert data to it.
Source failure-byte observations remain distinct from the word-machine halt.
The actual payload-bearing source call retains [0xde,0xad] and its public
word-compiler refusal. No G01 event list, byte-EVM success or Osaka/resource claim.

Test-only MemoryCallControls reuses the published callerOwnership program and
compiled certificate through references to their existing private constants.
The fixture elaborator emits only mkConst of the expected pinned declaration;
it supplies no new semantics or trusted proof. The core never imports Lean,
Syntax.Splice, the fixture adapter or producer examples. A missing private
constant fails closed; the audit checks exact published producer bytes/revision.
No duplicate contract/function/call implementation is introduced.

The instantiated whole-program baseline checks shared mutation17, escaped
local33, separately rebound parameter44, later allocation11 and marker42;
protected stack77 and untouched sentinel99 retain their order. Actual target
words are checked in their published address order. Wrong output/alias/cursor,
undersized frame, exhausted allocation, failure class and revert data controls
reject their respective false observations. The actual frame bound for this
whole-program certificate is12; the negative uses11. The escaped object's
header is cell260 and its first element cell261. Earlier incorrect test
expectations are retained as raw failures, not weakened producer contracts.

The stronger populated witness structurally cuts the EXISTING intrinsic program
after its first3statements. This is typed syntax selection, not a new AST or
execution relation. The published Calls.compile prefix certificate constructs a
real machine run, caller context2, heap1 and allocator256→258. The remaining
actual calls are compiled through public Compiler.compile with a proved exact
prefix-fragment equality. Their real Input is derived from prefix soundness,
private frame bound and reached capacity; it is not assumed.

populated_spec applies NEW memory_call_spec to that actual populated input,
actual successful suffix source run and nontrivial marker42 source box.
populated_alias_escape applies NEW success/alias transport: the pre-existing
caller reference0 retains its base address (a NONVACUOUS BaseExtends instance),
shared alias cells agree, returned callee-local reference3 is represented,
protected stack77 survives, and exact reached cost10 advances258→268. The prefix
cost is2; the whole-program reached cost12. populated_mutation proves the real
caller value5→17, escaped33 and separate rebound44 from the reused executions.
The prefix is certified using the published internal Calls.compile API; only the
remainingCalls result is claimed to be the public compiler's output.

Both independent read-only finder/skeptic reviews passed the consumer, populated
controls, private-constant adapter and accounting. They used no Lean/server/build
or tests. Initial source failures are retained: namespace and keyword mistakes,
quoted private-name inspection, inferred Option.get heartbeat exhaustion,
dependent signature/equality/expected-value mistakes, and typed structural-cut
motives. No sorry, axiom, native_decide, implemented_by or budget increase remains.

The first deep populated-input check exited137 at the enforced12GiB cap. Its raw
log and peak remain populated-input-second.log. Before changing declaration
sharing, the producer history914181a1 and its documented irreducible-certificate
performance convention were inspected. Explicit intrinsic contexts and shared
irreducible certificates then checked successfully at unchanged budgets. No
reserved performance repair, no cache deletion and no repeated unchanged failed
heavy operation. Focused successful logs retain actual RSS/cgroup measurements.

### Accounting and remaining validation boundary

Fresh core metadata now includes the actual Compiler.Compilation.memoryCalls
constructor:99V16 theorem entries and2207explicit OPEN constructor/G03/stage
obligations. No previously open obligation is promoted to closed. The separate
controls closure records113actual theorem entries, including49named test
controls and generated proof auxiliaries. Both closure boundaries are explicit.
All new consumer/control axiom outputs use only the standard allowance or none.
The existing26accounting tests and new17memory-call audit tests pass. The first
read-only-sandbox attempt at the existing temporary-file tests failed because
no writable temporary directory was available; the separately logged permitted
run passed, without changing tests or their assertions.

roadmap-v16-memory-call-audit.py binds producer91e94ab57305ca055127934fd9e68fe9ea5e6be3,
its three exact producer files, current head/Lean tree, actual constructor,
compiler/certificate origins, populated statements/dependencies/axioms and
OPEN stage/constructor status. Negative controls reject wrong revision/head,
producer bytes, missing emitter/constructor/statement, assumed PublicCorrectness,
erased premises, fabricated events, altered trust and false closure. This is
structural accounting supplementing kernel proofs, not coverage discharge.

Applicable layers/orphans/trust/noncircular checks passed. The new full
run-lean confirmation subsequently PASSED as recorded below.
All earlier exit124 failures and the sealed35df checkpoint remain immutable.
The optional external source-reference script's pinned soljson is present with
its expected SHA256, but ethereumjs VM/common/util and ethers are not installed
in current resolution paths. No dependency upgrade/install is authorized here;
no external EVM run is claimed. This does not replace the pinned EVM/runtime
bridge prerequisites or make source reference tests kernel proofs.

The exact-frozen-base documentation gate currently FAILS with48missing paths
and37ambiguities (85complete findings), versus46+37 at the frozen base. Both new
findings originate verbatim in the published inline-assembly plan, line106:
its planned Solidity/Yul/Syntax.lean and Solidity/Frontend/SolcJson/Yul.lean do
not exist. The raw checker exit1 and complete set comparison are retained.
No-green waiver: even though the difference is published upstream, exact-base
no-new findings has NOT passed. The plan remains reserved/read-only. Requested
owner-side documentation patch: label those future paths as planned text that
is not an existing-module citation, or publish the actual owned modules; no
placeholder module or checker exclusion is introduced by V16.

G48 SourceSpec/admission/lowering and full-profile progress remain unavailable.
G49.01 now has this actual ordinary-memory-call application; complete constructor
and feature-combination composition remains open. G49.02–03 still require pinned
byte/runtime EVM transport and full coverage/failure/progress without residual
fragment domains. Recursive/external execution, Osaka/resources, creation/runtime
installation, rollback/adversarial StateExport and final matching SolKey/G51
applications remain owner prerequisites. This is a useful concrete scoped backend
specification consequence, not full source/compiler/deployment correctness. The
original blocked goal is preserved; recovery does not reset or reactivate it.


### Published recovery committed handoff section

The mandatory new full run-lean gate PASSED:996default jobs,262kernel
SolkeyTestSuite jobs,377parsed taclets/131read-bearing/131covered annotations,
exit0. The same12GiB/no-swap wrapper sampled at most1Lean worker and0compiler
workers; full-gate cgroup peak5383692288bytes, sampled aggregate RSS3260928KiB.
No proof, stack, node, fuel, TestSuite or5400-second full timeout increase.
The prior populated cap failure137 and both earlier full failures124 remain
separate failed evidence. Final source digest is compared against the passing
full gate after committing this handoff; the entire assignment is NOT complete.

Strict automation passed at the original300seconds/module bound:26actual timing
rows for unchanged TestSuite sources,491automatic+61step-budget proofs,0manual,
11refuted,0pending. Complete pinned TestSuite audit passed:564=552derived+11refuted
+0pending+0divergent+1excluded;2skip. Source file equality versus sealed35df is
recorded explicitly for reused timing rows, alongside the current full kernel
check. Layers185core/0inversions; orphans1011reachable/0orphaned/0notallowed;
trust1026sources/246inventoried sites/0findings; noncircular1260modules/0violations.
The raw documentation gate and exact-frozen-base no-new-findings gate still
FAIL on the two published planned Yul-path citations described above. Those
required gates are not relabeled green; this recovery checkpoint is PARTIAL
with implementation/proofs checked and that owner-side validation blocker open.

Coordinator-only ledger reconciliation proposal (no global ledger edit): attach
scoped evidence for feature IDs functions, internalCalls, memoryLocation,
memoryAliasing, newMemory and assignment. Attach empty/payload failure/refusal
controls under revertStatement, revertBuiltin and revertPayloads. The relevant
existing G03 combinations are17(mixed core/memory programs) and32(calls with
storage/memory reference arguments and tuple returns). These large combinations
remain OPEN: this witness covers neither all storage references/tuple returns,
nor recursive/external execution, all operators or all approved feature mixes.
R09 and every other remaining restriction/profile exclusion is not globally
removed. All2207current constructor/G03/stage obligations remain OPEN, including
Compiler.Compilation.memoryCalls; its consumer is scoped evidence, not coverage.

Integration commit7630134a6287c34d88f739f37a67fdade5769366 preserves sealed prior
head35df1dc09d5b47c9d3ef1f472a8049300f3b12b2 and published prerequisite91e94ab57305ca055127934fd9e68fe9ea5e6be3.
All V16-authored changes after that merge are confined to the new consumer,
owned tests/audit/document and append-only registration. Published upstream
history is distinguished from V16-authored edits in the patch/bundle handoff.
Final committed head, exact theorem statements/axioms, actual commands/outcomes,
raw failures, complete doc finding arrays/provenance, reviewed ownership,
checksums and absolute paths are exported under /workspace/scratch/v16-published-2de14d52.
The original sealed artifact directories remain unchanged. Final artifact
finder/skeptic reviews are recorded there separately from source reviews.
No push, default-branch merge, reserved-owner repair, new goal or goal reset.


## Diamond recovery after sealed21c9: scoped compiler/specification consumers

The original blocked goal and frozen scope remain binding. No goal reset,
reactivation, source delivery or G48–G51 completion is claimed. Prior21c9,
published91e94ab57305ca055127934fd9e68fe9ea5e6be3, all76new/110prior/30original
sealed artifacts and raw124/137failures are preserved. Evidence for this recovery
uses the separate /workspace/scratch/v16-diamond-recovery directory.

The five NEW MemoryCallConsumer consequences are memory_call_not_exhausted,
memory_call_capacity, memory_call_diamond, memory_call_diamond_iff and
memory_call_diamond_cursor. The first derives non-exhaustion from the actual
memoryCalls certificate's exact failure classification; it is not an extra
assumption. The capacity lemma obtains the bound at the actual entry cursor
from AllocationInput (or cost0 and Fin's bound), equating represented cursors
through their shared machine cell. It does not assume a desired capacity result.

memory_call_diamond consumes only the actual compiler memoryCalls path, full
Input and unchanged Spec.sat diamond to derive exact source success, target
success at PC0, complete stack-tail preservation, StateRepr, BaseExtends,
GrowsAllocator with actual reached cost and the source postcondition. It accepts
no source-success, notExhausted or desired-target-run premise. The scoped iff
relates that approved diamond reading to the complete actual source/target/post
witness under the same genuine path/Input. The cursor consequence also derives
capacity internally, retaining only its necessary positive-base and actual
entry-allocator premises. No Spec.sat/calculus/closer/semantics/producer change.

Ten NEW controls reuse the sealed populated caller/suffix and exact producer
fixtures: remaining_diamond, whole_diamond, populated_diamond,
diamond_complete_observations, failure_diamond_rejected,
diamond_false_post_rejected, diamond_does_not_supply_frame,
diamond_does_not_supply_capacity, general_diamond_not_success and
exhausted_case_not_admitted. Actual suffix Input is still CONSTRUCTED by the
existing certified prefix. NEW diamond transport supplies its successful runs
and postcondition, preserving marker42, non-vacuous old-reference address,
shared aliases, returned callee-local escape, stack77 and cursor268. The full
existing source-array and target-word vectors, including untouched entries and
sentinel99 in their original order, are rewritten through the NEW run witnesses;
no cells/events are selectively dropped or fabricated.

The existing callee's exact empty revert has genuine Input but rejects even a
true-post diamond through NEW transport. A false marker post is rejected too.
True source diamonds still do not supply missing frame or allocator admission.
The existing SpecificationControls recBase exhausted diamond is reused unchanged:
it is genuinely true and has no successful run. That exhausted entry cannot
inhabit this finite memoryCalls path's Input. This is an incompatibility derived
from the existing certificate, not a new source exclusion or exhaustion reading.
Recursive/external and full-profile coverage/progress remain OPEN prerequisites.

Both independent read-only proof/control reviewers found no proof or ownership
defect. The first focused run failed on a dependent existential binder's syntax;
it was fixed and the raw exit1 retained. Subsequent core and actual populated
control checks passed. No heartbeat/fuel/node/stack/test/time increase, axiom,
sorry, native_decide or implemented_by shortcut was introduced. Existing
explicit-context/irreducible certificate sharing and the same cache are reused.
No Lean MCP diagnostics tool is available; the permitted serial capped CLI
fallback supplies per-file checks. Actual Lean4.24.0(commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b)
and Lake5.0.0-src+797c613 are retained; fresh KeySort passed2jobs under12GiB/no-swap.

### Exact premise and dependency accounting

Test-only metadata now exports each declaration's actual bounded head telescope,
proposition status, full closed binder Expr representation, printed type and
constants. Bounded extraction does not unfold a negative RESULT into a fictitious
extra premise. The reviewed owned diamond-premises.json pins all complete rows
for the five new lemmas. It is versioned structural accounting supplementing
kernel proofs, not a semantic trust attestation or a new axiom.

Independent finder and skeptic reviews confirmed a first-draft audit gap:
binder names/Prop flags/constant membership would accept Input∧desiredTarget or
diamond∧sourceSuccess inside the SAME binder. Complete expression/type-row pins
now reject those strengthenings, changed arguments with identical constant sets,
hidden oracle parameters and assumed capacity/source/target/exhaustion premises.
The same-name conjunction and helper corruption controls directly exercise the
validator rather than only mutating a final report schema. Both reviewers cleared
the fixes. No conditional preservation premise is silently counted as constructed.

Metadata retains ALL imported V16 facts, including unrelated decoded_invariant
with its explicit PublicCorrectness premise. Because reusing the genuine
exhausted control imports that older theorem, the no-PublicCorrectness check now
walks the actual memory-call consumer/control dependency closure rather than
rejecting an unrelated imported conditional law. All public/private owned
helper declarations are captured via privateToUserName; a missing reached owned
node fails closed. Core/private aliases containing PublicCorrectness are rejected.
The unrelated conditional theorem remains visible outside that proof closure
and in global OPEN accounting. This is not a waiver for an actual consumer.

Fresh core accounting has107actual theorem entries, now including private owned
helpers; the controls closure has175theorem entries and173reached proof/helper
nodes. All2207constructor/G03/stage obligations remain OPEN. All26legacy and
35extended audit tests pass, including exact same-binder/type, hidden-oracle,
input replacement, missing/private helper and unrelated-conditional-retention
controls. Existing scoped axiom checks and actual metadata use only the standard
propext/Classical.choice/Quot.sound allowance or none.

Mandatory proportionate checks subsequently passed as recorded below. The exact-frozen-base documentation
failure85vs83, including the two reserved planned Yul citations, remains binding;
those citations are neither edited nor waived. Final committed head, theorem
premises/axioms, raw gates, separate read-only reviews, patches/bundle and checksums
will be exported in this recovery's separate evidence directory.


### Diamond checkpoint committed handoff

Full run-lean PASSED996default jobs/262kernel jobs/377taclets with131annotations
matched, exit0. Peak4115083264bytes under the unchanged12GiB/no-swap cap;
maxLean1/maxCompiler0, sampled aggregate RSS2348808KiB. Strict automation passed
at300seconds/module for26retained timing rows from unchanged TestSuite sources;
491automatic+61step-budget,0manual,11refuted,0pending. Complete pinned TestSuite
passed564=552derived+11refuted+1excluded,0pending,2skip. Layers185/0inversions;
orphans1011/0orphan/0notallowed; trust1026sources/246sites/0findings;
noncircular1260modules/0violations. The required raw docs and exact-frozen-base
no-new-findings gates still FAIL85vs83 on the same two published reserved planned
Yul citations; no new V16 citation finding, no waiver or reserved repair.

Separate read-only finder/skeptic reviews passed proof and control milestones.
They found and cleared the same-binder audit-strengthening gap after complete
closed-expression/type pins and direct adversarial tests were added. All public
and private reached owned helpers are included; missing metadata fails closed.
Final core metadata107includes private helpers, control closure175and reached
proof/helper closure173;26legacy+35extended audit tests pass. These are scoped
proof/accounting results, not complete compiler coverage or a source delivery.

All original G48–G51 stages and2207constructor/feature obligations remain OPEN.
SourceSpec/admission/lowering/full-profile progress, complete backend feature
composition, recursive/external execution, byte-EVM/Osaka/resources, deployment,
rollback/adversarial StateExport and final matching SolKey applications remain
unresolved. This checkpoint implements the investigated diamond consumer while
remaining PARTIAL because required documentation validation fails.

One further independently executable ORIGINAL G51.02 consequence is the box
consumer retaining the genuine empty-revert alternative; a box cannot generally
yield success because it accepts that failure even with a false postcondition.
It can be consumed into a success/post-or-exact-revert witness without a separate
source-success premise. That assigned scoped backfill is taken only after this
checkpoint's gates, reviews, commit and handoff, without altering box semantics.
Exact committed head and immutable artifacts are recorded externally under
/workspace/scratch/v16-diamond-recovery; the blocked goal is not reset/reactivated.
