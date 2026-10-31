# V16 compiler correctness, transactions and specification transfer

Status: independent backfill extended through recovery checkpoints; full lane
blocked on unpublished concrete prerequisites; scoped final validation passed.
Base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v16-correctness-transfer`.
Repository: `/workspace/solidity-lean`.

No final G48–G51 contract is proved. No existing reserved implementation is
changed. The only shared changes are append-only module/document registration.
The [G01 contracts](roadmap-g01-interfaces.md), [G03 ledger](roadmap-g03-ledger.md),
[G04 restrictions](roadmap-g04-restrictions.md) and
[scope decisions](../solidity-scope.md) remain binding and unchanged.

## Work and backfill accounting

| Item | State and remaining obligation |
|---|---|
| G48 | Blocked: actual independent SourceSpec/admission/lowering instances and full-profile progress are not published; source handoff explicitly leaves SourceSpec open. No new premise is counted as discharged. |
| G49.01 | Open: compose actual expression/statement/call/pass certificates over every approved intrinsic constructor, without residual fragments. No backend implementation changed here. |
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
