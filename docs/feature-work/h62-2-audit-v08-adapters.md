# H62 item 2 — v08-adapters audit, ongoing

Owner: `solidity-h62-2-20261106/audit-v08-adapters`.
Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h62-2-20261106/audit-v08-adapters`.
Frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Original rendered prompt SHA256: `5cacd891e4eb0f7c11882c5370c149cf789d69a846d5ca83b10b7c6fd650a2b6`.
Previous checkpoint: `1b7eb0c5f8251efbaaf3b7e692d0f50d1ba53fb5`.
The original persistent goal is retained unfinished; get_goal is unavailable.
No second goal, reset, push, merge, PR, pre-gate, deployment or systemd-run.

## Coordinator answers applied

The latest coordinator answer says v4.35.0 applies ONLY to the toolchain-migration
batch. This lane uses the frozen master's installed v4.24.0. The previous
MIG-STRING-001 question is resolved by that scope correction, without editing
Solidity/SortCheck/Parser.lean. Earlier v4.35 logs/install artifacts remain historical off-git data;
they are not used or accepted by current validation. No further install/overlay.
The tracked lean-toolchain and all frozen sources remain unchanged.

H69 (human, 2026-11-06): "for theorems whose hypotheses are contradictory on
purpose (negative controls, separation lemmas, refutations), a checked Lean proof
that the hypotheses cannot hold together IS the audit result for that theorem.
Ordinary interface theorems still need a joint-satisfiability witness. Change no
statement. Classify each such theorem explicitly in your audit report (name, why
intentional, the impossibility proof) and continue."
AUD-REFUTATION-001 is resolved by the checked classification below. Questions: none.

## Original checkpoint status

| Checkpoint | Status | Remaining work |
|---|---|---|
| 1. Every frozen interface signature and owner | partial | 881 mapped files, 7,949 lexical theorem candidates; 26 source-signature ambiguities. All-kind kernel census now covers two modules, including proof fields, predicate definitions, universes and definition values. Remaining modules and producer ownership still need reconciliation. |
| 2. Every ordinary joint witness / H69 impossibility | partial | Six ordinary source-theorem targets jointly witnessed; one intentional refutation audited; four additional proof fields witnessed through two coherent per-input carriers. Global SourceSpec producers remain unwitnessed. |
| 3. Supported compiler success and negative controls | partial | Actual dynamic local-require compiler succeeds for true input, reverts for false input; both reject-all and always-revert candidates fail its scoped public contract. Global success, charged gas and fork boundaries remain pending. |
| 4. Witness and statement-fidelity census | partial | Thirteen source theorems accounted exactly once in two limited acceptances. 7,936 lexical theorem candidates remain, plus further non-keyword interfaces and generated declarations awaiting classification. Full-root gates remain pending. |

This checkpoint is not completion of the four-checkpoint / 8–10h queue. The
fresh-thread handoff follows four useful work items: correct lane prerequisite;
H69 resource witnesses and census; scoped success/carrier proofs; reviewed
acceptance/cache hardening. Resume the same VM, goal and branch, not a replacement.

## Scope and setup provenance

Initial clean checkout was work at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.
Fetched the intended remote/base, verified ancestry, and created this branch at
the exact base without reset/discard. The earlier export records full ancestry.
All current changes are in the sole assigned tests/scripts paths and this doc.
No Solidity, Bridge, generated root, central map, pin, lakefile or original
interface was edited. Writer lock protects writes/checks; no owner edit request
is needed for these exclusively owned additive files. Existing originals remain
read only, and no H55-G49 proof work is duplicated.

Actual versions: Lean `4.24.0`, Release commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake `5.0.0-src+797c613`.
Installed archive observed SHA256:
`b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`.
Fresh KeySort/AST/annotations/parser/checker compiled, and the actual checker
reported `parsed 377 taclets, 131 read-bearing, table covers 131` and `OK`.

Heavy work remains serial, LEAN_NUM_THREADS=1 and explicit -j1, one CPU,
600s per-file wall cap, no host swap, hard 12 GiB per-child ADDRESS-SPACE cap,
and monitored 4 GiB available OS reserve. This is not an aggregate RSS-cgroup
claim. Lean MCP is unavailable. No proof/heartbeat/resource budget was raised.

## Resource theorem family and H69

`witness-ledger.json` stores original signatures, signature hashes, exact imported
kernel type hashes, classifications and proof links. The all-kind census retains
20 kernel declarations: 12 theorem constants, one predicate, seven other
implementations. Eleven theorem declarations occur in the original source;
`noFailures.eq_1` is separately recorded as a generated equation.

All original names below have prefix `Solidity.Source.FailureResources`.

| Statement | Audit result |
|---|---|
| Bound.le_trans | trans_joint supplies BOTH inequalities on one a/b/c triple |
| Bound.withFailures_mono | replacement_joint supplies one shared r/s, p and extension |
| dropped_not_noFail | refusal_joint supplies exact p/i dropped equality |
| frame_not_noFail | SAME refusal_joint schedule supplies exact p/k/cut equality |
| Bound.not_le_of_points_ne | schedule_change_joint supplies unequal schedules |
| no_horizon_retraction | Intentional diagonal refutation; no_retraction_joint_impossible proves the exact extract/replace/rightInverse hypotheses cannot coexist (H69). The original docstring explicitly explains why a bare horizon cannot retract all failure plans. Statement unchanged. |
| Bound.le_refl, Bound.failures_with, Bound.horizon_with, noFailures_noFail, noFail_iff | Exact elaborated telescopes have no propositional premise binder. Resource/schedule data types are inhabited by the fixture; no hidden global Producer structure is present. |

`nofail_predicate_witness` separately proves the actual NoFail predicate inhabited
by a schedule with balance 37. This does not inhabit a SourceSpec producer.
All seven new resource helper theorems have guarded empty axiom reports.
The original noFail_iff retains its existing standard classical axiom set; no
original pin was changed. Seven other data/implementation declarations remain
explicitly retained in metadata rather than silently disappearing.

## Supported compiler and coherent carrier proofs

`LocalGuardSuccess.lean` imports the unchanged LocalGuardSelectionControls.
Its Contract requires compilation AND exact whole-machine execution for every
Boolean input: true succeeds preserving the populated machine, false reverts.
`actual_contract` proves it for the real checked local-require compiler.
`rejectAll_not_contract` and `alwaysRevert_not_contract` refute the named trivial
candidates by the mandatory true-success case. No selected-code or successful-run
premise is assumed by the contract. Both actual Source pipelines execute the
same populated fixture; saved stack word 77 and full machine are preserved.
The original zero-horizon, literal/assert/message refusal controls also compiled.

`selected_correct_joint` supplies the original selection equality, complete
local relation and StateRepr simultaneously on one shared value and machine.
`views_joint` inhabits BOTH whole dependent carrier records, including their
indices, context/type equalities and transported expression equalities:

- LocalGuardSelection.View: contexts, same, index.
- LocalGuardSelection.BoolLocalView: type, same, index.

These are PER-INPUT indexed carriers. They are not globally quantified P8a,
SourceSpec, dispatch, body-lowering or world-correctness producers.
The six local helpers pin only the inherited standard axioms
`[propext, Classical.choice, Quot.sound]`; no new axiom/sorry/native shortcut.

The exact local kernel census retains 56 declarations. Thirteen primary source
items are reviewed: two source theorems, four proof fields, two carriers, two
data projections and three implementation definitions. Forty-three generated
support declarations remain explicitly pending interface classification.
Here the four proof getters are kernel theorem constants despite their source
field syntax; predicate definitions still require all-kind enumeration. The
exporter uses original declaration-kind metadata, not deprecated isTheorem.
Human producer ownership is separate from defining-module provenance.

Proof boundary: this is the existing instruction interpreter and actual Source
execS at horizon 7. The `0` in `.ok machine 0` is pending jump count, not gas.
No paid-call transition, charged gas, fork adequacy, deployment or whole-program
frontend admission is established by these fixtures. Those obligations remain.

## Census, acceptance, negative controls and timings

The lexical scanner verifies every scanned source blob against the base,
expands map shorthand and retains all keyword-theorem candidates. It explicitly
reports complete_interface_inventory=false. Source theorem counts alone do NOT
cover proof fields or predicate contracts (e.g. P8 FrozenInterface fields and
RuntimeFrameInterfaceV1.ReturnClaim). The all-kind exporters retain exact kernel
names/types, universe parameters, original kinds, field/projection metadata,
axioms and definition values. Ordinary proof correspondence is reviewed; scripts
reconcile evidence and cannot independently prove statement equivalence.

Current evidence root: `/workspace/h62-audit-v08-adapters-evidence`.

| Gate / actual command family | Outcome / decisive evidence |
|---|---|
| bounded_prerequisite.py, default fresh v4.24 mode | PASS; prerequisite-424/results.json contains exact commands, exits, versions and timings; CHECKER_RUN.log has 377/131/131 and OK. |
| bounded_prerequisite.py --audit-module .../LocalGuardSuccess.lean, fresh closure | PASS; local-guard-final-424 records all 158 exits0, source stability and production artifact hashes. |
| Same fixture after coherent carrier addition | PASS; local-guard-carriers-424 records 157 verified reused imports and one fresh leaf, 1.805s. Reused times are explicitly zero and not new checking evidence. |
| Resource and two all-kind metadata fixtures | PASS; resource-predicate-424, resource-declarations-final-424, local-declarations-final-424. Exact commands/source hashes are saved in each results/source manifest. |
| accept_witnesses.py and accept_local_guard.py | PASS, LIMITED; resource-acceptance-final.json and local-acceptance-final.json. Neither passes the overall audit. |
| census.py + check_census.py + independent regeneration | PASS, lexical tooling only; census-v424-h69 and census-repeat-v424 are byte-identical; equation/type-match/comment/character/name/path regressions pass. |
| node scripts/check-layers.mjs | PASS; layers-v424.log |
| bash scripts/coord-tools/register.sh --check | PASS; register-check-v424.log; no registration applied |
| bash scripts/coord-tools/fragments.sh --check | PASS; fragments-check-v424.log; no map/root edit |
| Failed proof record, failed-run cache, corrupted cache | Expected REJECTION; reject-failed-proof-v424.log, reject-failed-cache-v424.log, reject-corrupt-cache-v424.log; no false accepted output |
| Full affected-root run-lean.sh, all 881 module witnesses, charged gas/fork acceptance | PENDING; no full-audit acceptance or RUNTIME_GATE_PASS |

The runner now requires a completed source-stable successful prior run, exact
versions/source hashes, and artifact SHA256 checked before/after copy. It rejects
partial or undigested legacy runs. The initial optional-reuse review finding is
fixed; final artifacts use only hardened certificates or fresh compilation.

Paired original-import timings: 157 identical frozen source inputs, same v4.24.0,
-j1/CPU/resource bounds, isolated empty Lean outputs in each run. Before 748.370s;
after 705.174s; delta -5.772%, below the >10% slowdown stop threshold. Scope is
original import checking only. The baseline leaf had an audit namespace error,
so it is not a passing fixture gate. OS page cache was not flushed. 155 output
olean files were byte-identical; Evm.Signed and Evm.Exp differed in serialization
while their sources and successful checking remained unchanged. No full-root
performance conclusion is claimed. Details: paired-frozen-timing.json.

Retained failed diagnostics are separate from accepted runs: the first local
audit omitted an open namespace; one metadata revision lacked an explicit field
type. Both were corrected within owned files and rechecked. Error-generated
sorryAx placeholders were never accepted. Source has zero new sorry/axiom,
no native_decide and no raised heartbeat budget.

## Remaining owner ticket and work

PREMISE-P8-001 remains an ordinary-interface witness dependency. CreationPremises
and LibraryPremises require DeclarationGraphAdmission.Producer.base.failures.
The Nat-encoding impossibility theorem requires explicit encode/decode/roundtrip;
it does NOT establish arbitrary-S Inputs empty. H69 does not reclassify these
ordinary consumers as negative controls. No intended full producer is supplied.
Owners: CR/P8a and VY5 resource (H16), V08; V17/V07 constructor and G42.04/P4 library
producers; H55-G49 coordination retained. Resource owner evidence includes H16's
single-writer decision; the older snapshot also records CR history and isolated
migration overlays, which do not transfer live ownership. Local guard producer
ownership still needs coordinator confirmation.

Affected CreationPremises statements: meaning_origin, actual_source, reached_body,
creation, installed, try_success, runtime_success, settlement_failure, try_failure.
Affected LibraryPremises statements: source_caller, source_library,
no_second_payment, delegated, library_account_preserved, source_roles_separate.
Each remains individually uncovered. Options remain producer delivery of the
intended coherent model or an owner-authored frozen repair proposal with blocker
retained; no statement or new premise has been substituted.

No relay.sh exists in this checkout/workspace. The exact owner ticket is prepared
here for coordinator retrieval; no relay transmission or owner approval claimed.
Continue full all-declaration census and ownership reconciliation, original joint
witnesses, success/negative controls for remaining supported families, observable
charged gas/fork boundaries, full validation and reviews. Use only assigned
backfill; never take another producer's files or duplicate H55 work.

## Reviews, registration and export handoff

Finder and skeptic independently reviewed read-only, without Lean/server use.
Confirmed fixes include source equation-boundary capture, match-type ambiguity,
frozen provenance, carrier versus field satisfiability, theorem-only inventory
limits, metadata field typing, wrong census-run substitution, and cache stability
plus artifact verification. Final review text is saved in reviews-v424-h69.json.
Full goal completion remains unclaimed.

Registration proposals are in the owned tests registration-fragment.md; no
central registration or import promotion is applied. Metaprograms importing Lean
must remain outside the dependency-free core.

Export after commit to `/workspace/h62-audit-v08-adapters-export/continuation-v424-h69`:
original.patch, checkpoint.bundle, handoff.md, evidence.tar.gz, evidence-files.sha256,
checksums.sha256 and export.json with full committed head/base and hashes. Previous
checkpoint exports are preserved. The current full head is recorded in export.json
rather than introducing a self-referential commit hash into this document.

## H70 continuation — frozen proof-field/predicate census

Starting head: 373ead4dc06fb853201a0ac80d1127379121c83b. Same base/branch,
master v4.24.0 and all original limits retained. No original interface edited.
The full goal and all four checkpoints remain unfinished.

H70 routes PREMISE-P8-001 to
`solidity-v12-v17-20261031/v16-correctness-transfer`.
Current-owner delivery is pending for
`claudecloud/moved2-20261105/vy5-composition` and
`claudecloud/moved3-20261105/v07-lowering`.
Host relay journals determine delivery acceptance; this worker has no such
acceptance evidence. Routing is not owner agreement or producer validation.
Wait remains V16/current Claude P8 producer on
DeclarationGraphAdmission.Producer.base.failures for CreationPremises,
LibraryPremises and global SourceSpec joint witnesses. This routing update
supersedes earlier destination hints, without transferring ownership.

Two additive exporters now inventory their unchanged defining modules:

| Module | Declarations | Proof fields | Predicate definitions | Carriers |
|---|---:|---:|---:|---:|
| Solidity.Lowering.P8.FrozenInterface | 157 | 14 | 0 | 8 |
| Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV1 | 137 | 24 | 7 | 7 |

All 294 records remain PENDING, including theorem/generated/support declarations.
No new witness, impossibility classification or global carrier inhabitant is
claimed. Existing coverage remains 13 source theorems plus four additional
coherent proof fields; the broader inventory is still incomplete.

Raw types, universes, original kinds, definition values and carrier-field names
are retained. Field roles derive from structure field metadata, not name guesses
or theorem-keyword scanning. Defining module is not producer ownership.
The inventory includes P8 FailureProjection/SourceRealization/Producer obligations
and runtime ReturnClaim/BareRevertClaim/RealizableEntry and Pending carriers.

Commands and gates: bounded_prerequisite.py --audit-module with
P8StatementCensus.lean and RuntimeFrameStatementCensus.lean; exact per-file Lean
commands, versions, exits, digests and timings are in h70-p8-census/results.json
and h70-runtime-census/results.json under the existing evidence root. Both runs
passed with final source-stability manifests; verified reuse is labelled.
h70_inventory.py --repo /workspace/solidity-lean --evidence
/workspace/h62-audit-v08-adapters-evidence --out
/workspace/h62-audit-v08-adapters-evidence/h70-inventory.json passes inventory-only
reconciliation. No full-root/runtime/performance gate pass is added.

Independent finder and skeptic reviewed read-only without Lean/server or edits.
They confirmed correct defining-module targets and no satisfiability/delivery
inference; final review evidence is h70-reviews.json. Export under
/workspace/h62-audit-v08-adapters-export/h70 includes the original base-to-head
patch, handoff, bundle, inventory archive and SHA256 manifest. Continue the
remaining all-kind census while the ordinary global producer witnesses wait.

## H82 authorized stop and successor handoff

Implementation STOPPED by explicit retirement; concurrent H70 continue wording
is superseded. Successor: solidity-v07-v11-20261030/v08-world-lowering.
All original obligations remain unfinished. Committed retirement/ files preserve
the complete original assignment content (normalized owner JSON), original queues,
881-file scope manifest and every open item/wait. No proof implementation added.
No H71 push permission is available; no push. PAUSED cannot be set: exposed goal
API supports complete|blocked only; no false substitute transition attempted.
See retirement-handoff.md and preserved goal-pause-unavailable.json. No automatic
implementation continuation is authorized. Final stopped/head acknowledgement
accompanies cumulative authenticated exports; successor owns integration.

## Successor acceptance guard hardening (2026-11-06)

The exact acknowledged final source `b2bd56aa33352d2a0ab3049259e6aeeae0ddbdca`
was integrated after frozen assignment/queue/scope SHA256 verification and the
coordinator's final-stop receipt. External historical gates were not revalidated.

`accept_witnesses.py`, `accept_local_guard.py` and `h70_inventory.py` used Python
assertions for acceptance predicates. Optimized Python removes assertions. All
44 predicate expressions are now explicit `require` checks with identical AST
conditions; rejection raises `ValueError`, and CLI rejection remains nonzero.
Only literals and already-bound paths are message arguments, so eager message
evaluation adds no I/O. Three tests pass in normal and optimized Python: exact
44-predicate conservation, synthetic captured-run corruption rejection, and
false-condition rejection. Version, exit, STOP, swap, cap, reserve and source-hash
corruptions are rejected. These fixtures are fake metadata, never proof evidence.

Independent finder and skeptic reviewed read-only without Lean/server/builds;
no confirmed findings remain in this limited change. Their review stresses that
other scripts, including `reconcile.py`, still use assertions. This is not a
claim that the entire audit pipeline is optimization-safe. No real historical
acceptance run, kernel type, witness, H69 classification, axiom footprint,
resource enforcement or full-family timing is established by these tests.
All ordinary joint witnesses, intentional-refutation distinctions, semantic
census, supported compiler/failure/gas/fork coverage and final gates remain open.

### Successor metadata refusal backfill

After adopting published master `71c5963f3`, the unchanged acceptance predicates are exercised against an empty run, a matching version with the wrong toolchain commit, and mixed successful/failed or stopped records in both orders. Synthetic metadata tests remain separate from joint premise witnesses and kernel proof acceptance. No acceptance predicate, Lean statement, budget or trust requirement changes.

### Focused resource reacceptance after master adoption

Published master `706e36825` was adopted before validation. The approved activated per-file route checks the unchanged resource witnesses and exact kernel census serially. Source snapshots before and after both runs match. The unchanged acceptance script accepts five joint witnesses, one intentional H69 impossibility, five premise-free source statements and the generated equation for the byte-unchanged `Source.FailureResources` module. The intentional impossibility is not an ordinary joint witness, and the inhabited resource NoFail predicate is not a global SourceSpec producer.

The unchanged whole-area census fails at `Solidity/Backend/CalldataPackets/RawAddress/Controls.lean` because that mapped source differs from its frozen baseline. This failure is retained; focused resource reconciliation does not waive it, narrow the full audit, or establish complete statement fidelity. Full kernel-family/gas/fork/SourceSpec coverage and final gates remain open. The runs enforce a hard 12 GiB child address-space limit with sampled aggregate RSS/reserve guards; no hard aggregate cgroup-cap claim is made.

The small `resource-reacceptance-manifest.json` records paths, sizes and SHA256 values for off-Git evidence and the H1 cleanup receipt. Cleanup removed only three independently reviewed inactive generated SolkeyCheck binaries, reclaiming 517738496 bytes and leaving 2292506624 free immediately afterward. Source, sibling hashes/traces, logs, bundles, seals, protected caches and current build outputs were preserved.

### RawAddress correspondence check and independent local-guard reacceptance

The requested RawAddress comparison from the frozen baseline to `e8247d9277190b71488387dac594e82b2b191942` has exactly one hunk: it appends `Source.FailureExecution.Cursor.empty` to the anonymous initial Source.St value. It is not a mapFree argument or binder. The current file equals that integration version, but no baseline was changed: the exact hunk was reported as Q-WORLD-AUDIT-DRIFT-CURSOR, following the coordinator instruction to report any non-mapFree change. Census predicates and exclusions are unchanged.

Independent focused checks now pass for the byte-unchanged `LocalGuardSelection` source. `LocalGuardSuccess` and its exact kernel census pass through the approved per-file route with stable source snapshots; the unchanged local acceptance predicate reconciles success and failure, rejects both reject-all and always-revert compilers, and checks the coherent carriers and thirteen primary declarations. Witness checking took 265.747 seconds including cold imports; kernel census took 12.807 seconds. These are observed focused checks, not matched performance acceptance. There is no charged gas or fork parameter here; no gas/fork, full pipeline, global SourceSpec or whole-area audit completion follows.

After both gates stopped, a separately reviewed inactive generated SolkeyCheck binary was removed under H1. Its distinct hash and exact path remain in the off-Git receipt; source, sibling hash/trace and all other evidence were preserved. Free space then measured 2177425408 bytes. The small `local-guard-reacceptance-manifest.json` binds the focused results, unchanged full-audit disposition and cleanup receipt.
