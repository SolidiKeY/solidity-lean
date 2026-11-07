# H62 item 2: read-only-call empty-statement audit

Status: **blocked by mandatory performance stop; original goal unfinished**. The current frozen-file comparison exceeded the 10% stop threshold; no new proof work or remeasurement follows. Semantic/proof progress below is retained as a reviewable checkpoint, not completion. H69 assigns the two
unreachable frozen dispatch cuts to RO as **pending RO v2**: a reachable
versioned interface, explicit migration and consumer re-proofs. Their frozen
refutations remain evidence; they are neither erased nor counted as witnesses.
The separate compiler-success theorem is a pending deliverable of V13
(`v12-v17/v13-abi-world`) for G42, with V15/P10 observation dependencies. It
must prove success for that owner's compiler on the stated supported inputs;
no frozen interface statement changes. The prior scope questions and Q-CALLBACK-INTENT are resolved; RO confirmed intentional no-callback specialization controls. H70 supplies the exact H69 rule: checked joint-impossibility proofs are the audit result for intentional negative controls/separation/refutations; ordinary interfaces still need joint witnesses. RO, V13 and V15 have accepted the ticket relays. Lean proof work remains on mandatory performance hold; independent offline audit backfill continues under H82.
Worker edits preserve frozen hypotheses, exclusions, observations, budgets and axioms. Upstream readonly adoption removes three private helpers; all three remain explicitly counted and current frozen-tree fidelity fails, as recorded below.

Current post-rebase gates: **frozen-tree fidelity FAIL, central fragment check FAIL, global documentation paths FAIL**. Historical passing rows below refer to their archived trees. Layer and registration checks pass; kernel revalidation is pending.

Assigned branch: `codex/solidity-h62-2-20261106/audit-readonly-calls`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Actual repository: `/workspace/solidity-lean`.
The initially clean `work` branch at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`
was preserved. The missing base was fetched, verified ancestral to published
origin/master, and the assigned branch created at that exact base. No push,
merge, PR, pre-gate, deployment, or replacement goal was performed.

## Checkpoint accounting

| Checkpoint | Result |
|---|---|
| 1. Frozen inventory and owners | Original-base type/identity census: 129 files, 792 elaborated theorem types, all 33 private names resolved, owners retained. Current upstream has three private removals; current kernel fidelity is pending. Semantic global-vs-input feasibility continues with the witness queue. |
| 2. Simultaneous witnesses | Partial: 27 joint clients; 45 checked intentional impossibility results under H69; 256 statements with no top-level input hypotheses; two pending RO v2; 462 other entries pending. |
| 3. Success/totality and negative controls | Partial, owner deliverable pending: Source success/failure/timeout and both-pipeline gas refusal checked; reject-all and nonempty target-revert controls checked. General compiler success and executable gas/fork adequacy remain unproved. |
| 4. Fidelity census and uncovered owners | Partial: every named source declaration accounted exactly once, 32 explicit outcomes bound to signature hashes; all 792 bind to elaborated type hashes; remaining entries retain pending status and owners. Full all-witness acceptance and final integration gates have not passed. |

The census intentionally includes controls and helpers with no explicit hypotheses. It makes no silent interface-theorem exclusion. The new generated Lean query imports every unchanged mapped interface, checks exact theorem and owning-module identity, exports raw elaborated Expr plus readable type and actual binders, and resolves all private names. There are 339 syntactically binder-free types under nonreducing inspection. None is discharged by that fact. The semantic continuation now inspects reducing telescopes and proof axioms for all 339; only the narrow, reviewed classifications below advance their audit accounting. Binder proposition/record shape alone never establishes feasibility.

## Kernel evidence and boundaries

`ImpossibleDispatch.lean` imports the unchanged dispatch interface. Its two
refutations need only subsets of the exact original premises. For
`dispatch_getter_empty_succ`, empty input contradicts the getter's nonempty
predicate. For `dispatch_special_empty_succ`, empty input cannot match a
four-byte `Glob.selector`. Adding or inhabiting `At G n` cannot repair either
contradiction. This is a global conjunction impossibility, not merely a failed
search at a particular input.

`AlwaysRevert.lean` constructs a real fetched CALL at PC 3, followed by target
REVERT, alongside the actual successful Source invocation. The exact original
`fetched`, `declared_return`, and `decoded` consumers accept this nonempty
client. Their statements remain true conditional transport lemmas; they do not
establish target success. Elementary producer-selected observation equalities
in the negative fixture are not a validated P10 relation or a producer
implementation. A second control inhabits the global records with empty
`Step`/`Fetched` relations and proves per-input feasibility impossible.

`SupportedCalls.lean` supplies all `Callbacks.returned` hypotheses together at
one concrete invocation and proves an actual decoded uint success. It retains
malformed bytes as caller failure, zero Source horizon as timeout, and refusal
of `gasleft` in both pipelines. Source horizon is not EVM gas. The current
payment-only EVM lacks gas and calldata, and neither its machine nor Source
`Glob` supplies a fork selector: no invented fork parameter or fork-adequacy
proof was introduced. General supported-program compiler totality remains an
owner obligation.

All five audit proof files passed separate bounded Lean checks. JointClients.lean adds twelve exact applications covering callback frame/suffix/determinism/target uniqueness, raw-phase capture/storage, typed source storage/resume, raw uniqueness, depth refusal and inherited-static value refusal. Their printed axiom
sets contain only `propext`, `Classical.choice`, and `Quot.sound`; no added
`axiom`, `sorry`, `native_decide`, trust shortcut, or raised heartbeat limit.
Failed intermediate attempts are retained separately and are not certificates.
No H55 producer proof was duplicated. P1 producer ownership remains V12 and
H55-G49 where applicable, even though these consumer files belong to V13.

## Owner escalations

Each affected original declaration appears once below. The structured tickets
are saved in `tests/h62/item2/audit-readonly-calls/owner-tickets.json`. H70 confirms accepted relays to RO, V13 and V15. The host-only relay.sh is not a worker installation task. Coordinator answers now resolve both historical questions; the owner deliverables remain pending. No original-file write permission is implied.

ESCALATE: Solidity.Lowering.Readonly.SourceHistory.dispatch_getter_empty_succ — RO; proof-impossible-final.log/getter_empty_infeasible proves empty input contradicts selected getter. Options: owner versions a reachable dispatch partition; or preserve frozen statement and retain the witness blocker.
ESCALATE: Solidity.Lowering.Readonly.SourceHistory.dispatch_special_empty_succ — RO; proof-impossible-final.log/function_empty_infeasible proves empty input cannot match a four-byte function selector. Options: owner versions a reachable dispatch partition; or preserve frozen statement and retain the witness blocker.
ESCALATE: Solidity.Backend.WorldCalls.ExternalCalls.fetched — V13/P10; proof-always-revert-controls.log/accepted_fetched accepts nonempty fetched target REVERT with Source success. Options: add independent compiler success/totality; version producer coverage and fixed outcome correspondence; or retain conditional consumer and blocked public adequacy.
ESCALATE: Solidity.Backend.WorldCalls.ExternalCalls.declared_return — V13/P10; proof-always-revert-controls.log/accepted_declared_return accepts the same target failure. Options: add independent compiler success/totality; version producer coverage and fixed outcome correspondence; or retain conditional consumer and blocked public adequacy.
ESCALATE: Solidity.Backend.WorldCalls.ExternalCalls.decoded — V13/P10; proof-always-revert-controls.log/accepted_decoded yields actual Source decoding success despite target REVERT. Options: add independent compiler success/totality; version producer coverage and fixed outcome correspondence; or retain conditional consumer and blocked public adequacy.

## Reproduction and gates

Scripts are under `scripts/h62/item2/audit-readonly-calls/`; Lean fixtures and
small coverage/owner-ticket inputs are under the corresponding tests directory.
Bulk generated inventory and logs are off Git at
`/workspace/h62-audit-readonly-calls/evidence/`, with a checksum manifest in the
artifact root. The final handoff records committed head and patch hashes.

The runner acquires the repository writer lock, sets `LEAN_NUM_THREADS=1`,
adds package `-j1` through an off-Git alternate TOML, and requires explicit
`-j1` for direct Lean. It uses the existing 16 GiB VM cgroup, 12 GiB per-child
address-space bounds, aggregate/headroom monitoring and a 4 GiB reserve; host
swap is disabled. It never calls systemd-run. Only one heavy Lean process is
allowed. Process-group cleanup retains the lock until owned descendants drain.

Toolchain: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake
`5.0.0-src+797c613`. The v4.35 official pin is verified among the coordinator
inputs and applies to migration lanes; this additive item-2 audit remains on
the frozen v4.24 tree. No Lean MCP tools were exposed; bounded CLI diagnostics
were used. Absence of get_goal was explicitly declared nonblocking by the
coordinator; the original goal was neither recreated nor reset.

| Command (from repository root) | Outcome / decisive evidence |
|---|---|
| bounded runner: `lake exe solkeycheck --key "$SOLKEY_RULES"` plus actual Lean/Lake versions | Pass, prerequisite-retry.log: 377 taclets, 131 read-bearing, table covers 131; annotations match. |
| bounded runner: `lake build Solidity.Backend.WorldCalls.ExternalControls Solidity.Lowering.Readonly.SourceReadBuiltinControls Solidity.Lowering.Readonly.SourceDispatchEffects` | Pass, witness-imports-resume.json: 220 jobs, 713.547 s, peak aggregate RSS 1,782,915,072 bytes. Prior owned build paused to repair runner; its -15 exit was not counted as pass. |
| bounded runner: `lake env lean -j1 --tstack=131072 tests/h62/item2/audit-readonly-calls/ImpossibleDispatch.lean` | Pass, proof-impossible-final.log/json, 1.004 s. |
| bounded runner: same direct Lean flags on `AlwaysRevert.lean` | Pass, proof-always-revert-controls.log/json, 2.006 s. |
| bounded runner: same direct Lean flags on `SupportedCalls.lean` | Pass, proof-supported.log/json, 2.006 s. |
| `PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-readonly-calls/test_census.py` | Pass, test-census.log: five acceptance tests, including frozen-header and unmapped-core mutation rejection. |
| `python3 scripts/h62/item2/audit-readonly-calls/test_bounded.py /workspace/h62-audit-readonly-calls/evidence` | Pass, test-bounded-final.log: timeout and zero-exit parent controls rejected; no live descendant. These intentional negative gates are expected to fail, not passing runtime gates. |
| census generator with `--coverage tests/h62/item2/audit-readonly-calls/coverage.json` | Pass: 129 modules, 792 declarations, with elaborated census: with current semantic stage: 24 joint / 3 target-failure joint / 45 intentional impossibility / 256 no-top-level-input / 2 RO v2 / 462 pending. |
| bounded runner: `python3 scripts/h62/item2/audit-readonly-calls/measure.py --output /workspace/h62-audit-readonly-calls/continuation-semantic/evidence/timing-after-samples.json --compare /workspace/h62-audit-readonly-calls/continuation-semantic/evidence/timing-before-samples.json` | **FAIL, exit 1: +80.254967%; mandatory stop enforced**, timing-after.json and performance-stop-context.json. |
| `./run-lean.sh` and full all-witness acceptance | Pending, not RUNTIME_GATE_PASS. No full completion claim while frozen witness obligations are impossible. |

Before/after timing samples repeat the same unchanged frozen Premises file,
with identical command/cache/toolchain/resource settings; they measure local
checking repeatability, not a clean full-build migration comparison. Additive
fixtures do not enter the generated library roots. The final timing capsule
records the delta and stops if checking slows by more than ten percent.
The measured median was 1.027801 s before and 1.021473 s after: -0.615656%.
Both capsules used five samples and the identical source hash; no slowdown stop
was triggered. This is a local frozen-file check, not a whole-build speed claim.

Structural checks passed: 857 core modules, none reaching elaborators or checked
parser adapters; generated roots and fragments match; documentation paths
resolve. Existing ambiguous basename citations are warnings, not missing paths.

## Independent reviews and handoff

Read-only finder and skeptic agents separately checked inventory, feasibility,
statement fidelity and resource controls. Neither ran Lean, used a Lean server,
or wrote fixes. Findings fixed: frozen-byte checks, private source/kernel-name
distinction, explicit pending lexical limitations, separate producer ownership,
whole-process-group cleanup, explicit gate status, direct `-j1`, reserve
preflight, and lock retention until descendant drain. The finder identified the
two impossible cuts; the skeptic proposed and reviewed the nonempty target
failure. Final review evidence is exported separately.

Remaining obligations: 462 ordinary semantic/witness entries and two RO-v2 migrations; remaining semantic global-vs-input feasibility classifications; RO v2 publication/migration and consumer re-proofs for the two cuts; independently fixed compiler success/totality,
P10 observation, gas/fork boundary; full repository final gate and all-statement
acceptance. Save/relay these typed blockers, preserve the exact original goal,
VM and branch, and resume only under authorized owner scope. This handoff is
not completion of the four-checkpoint assignment or the 8–10 hour work queue.

## Coordinator continuation decisions

Verbatim answers are retained in the scoped coordinator-decisions.json. H69
selects versioned reachable RO interfaces, explicit migration and consumer
re-proofs; the two original declarations remain listed as pending RO v2. The
compiler-success requirement is assigned to V13 as a separate theorem for its
compiler, with V15/P10 producer coordination. Frozen signatures stay untouched.
H70 supplies the exact H69 rule: for intentional negative controls/separation/refutations, a checked joint-impossibility proof IS the audit result; ordinary interfaces still need joint witnesses; no statement changes. The previous clarification request is resolved. Relays to all three owner sessions are accepted.

## H69/H70 continuation evidence

Continuation artifacts are under /workspace/h62-audit-readonly-calls/continuation-h69/. The earlier root-level handoff/report describes the historical pre-H69 checkpoint and must not be used as current decision state. The current report and handoff are refreshed after this checkpoint commit.

The full mapped-surface build passed 341 jobs in 488.577 s, peak aggregate RSS 1,126,240,256 bytes. The elaborated query passed for all 792 declarations in 173.865 s, peak RSS 1,082,789,888 bytes, with no budget increase. JointClients.lean passed in 3.510 s with only the standard three axiom dependencies. These are affected-area validations; full run-lean.sh remains a final-goal gate.

The export collector requires successful bounded-gate status, exact query/log hashes, command, toolchain file and actual Lean/Lake binary/version identity. It validates all kernel names, source-signature hashes, owning modules, raw type hashes and exact membership. It rejects complete-looking output followed by Lean errors. Five source-census tests and twelve export acceptance tests pass, including missing/duplicate declarations, wrong private/kernel/module identity, failed gate, late error and stale query/log/binary receipts. This external metadata validation does not prove joint hypotheses.

The earlier H69/H70 questions were resolved. RO has resolved Q-CALLBACK-INTENT as intentional no-callback controls; owner items remain pending RO v2 and V13 compiler success with V15/P10 fixed outcomes. After the performance stop is resolved, resume remaining ordinary entries without modifying frozen interfaces.

Review correction: syntactic binder-free metadata never removes a witness obligation. Full exported records, including binder arrays, are reparsed from their successful hash-bound Lean log at census ingestion. Mutation tests reject binder-array tampering and separately exercise private kernel identity. At the pre-semantic checkpoint, all 339 syntactically binder-free rows remained pending. Their current accounting is derived only from the separately verified reducing/axiom inspection, not the empty syntactic binder array.

Continuation checking-repeatability capsule: five samples of the identical unchanged Premises file measured median 1.149105 s before and 1.093362 s after, delta -4.850972%. No >10% slowdown stop was triggered. This is not a whole-build migration performance claim.

## Semantic continuation after published-master preflight

Before selecting the new work item, git fetch origin master completed and history/code were inspected at 5f7bb1441566aaad64a34436904afc61de762fd2. The frozen read-only surface has no upstream changes and the audit tooling is not published there, so the duplicate-work rebase condition does not apply. A second fetch/code inspection preceded the hidden-input witness batch. No existing producer implementation was redone.

The generated reducing query checks the original exact types/names and uses forallTelescopeReducing plus collectAxioms under unchanged budgets. It passed all 339 selected declarations in 110.737 s with peak aggregate RSS 1,123,995,648 bytes. Every collected proof axiom set is a subset of propext, Classical.choice and Quot.sound. The original raw Expr remains pinned to the exact 792-type export. Canonical receipt/query/log/toolchain verification is repeated at semantic ingestion. Binder, axiom and inspection fields cannot be modified independently of the checked log.

The reviewed partition of these 339 is 256 rigid logical results with no top-level input hypotheses (211 Eq, 38 And, seven Exists), 42 deliberate Not/Ne control/separation/refutation results with one refused proposition leading to False, and 41 initially unresolved predicate/alias cases. The 256 label is deliberately narrow: it does not certify compiler success, nested semantic guards, representation feasibility or actual admitted executions. The 42 original checked proofs are H69 results, not newly created proof aliases or positive witnesses; their exact identities and frozen type/signature hashes are pinned in semantic-policy.json. Unreviewed negatives remain pending.

HiddenClients.lean then supplies eleven ordinary joint clients for four Effect predicates, six SameStorage predicates and receiver injectivity, using populated existing source states and actual addresses. It also proves three callback-choice conjunctions impossible. All fourteen helpers passed in 4.012 s, peak RSS 915,017,728 bytes, with only standard proof axioms. RO later confirmed these three callback controls are intentional no-callback specializations; their checked impossibility is accepted under H69, never as positive witnesses.

Current exact accounting: 792 = 27 joint clients + 45 checked intentional impossibility results + 256 no-top-level-input statements + two pending RO v2 + 462 other pending entries. Global record inhabitance is never substituted for per-input feasibility. Five original census, twelve exact-export and seven semantic mutation/acceptance tests pass. Tests reject altered semantic binder/axiom arrays, wrong type pins, nonstandard axiom policies, unreviewed negative acceptance and premature discharge of named predicates.

### Q-CALLBACK-INTENT — resolved; historical routing and question

The three fixed-strategy CallbackHistories declarations below have globally impossible callback-choice premises, despite their inhabited global certificates. The checked subset refutations establish impossibility of each full admitted-child conjunction. V13 owns these controls; RO owns the underlying source-history interface. Requests and exact paths are in the scoped owner-tickets.json. The coordinator confirms routing this decision to RO: wait {lane: solidity-compiler10-20261028/readonly-external, item: Q-CALLBACK-INTENT}. At that routing checkpoint the owner decision remained pending. RO has since confirmed intentional no-callback specialization controls; checked impossibility is now the audit result.

Question: are these intentional no-callback separation controls, eligible for the checked-impossibility result under H69, or ordinary producer obligations that must await reachable versions/fixtures? Options: classify as intentional separation and accept the checked impossibility, never as a positive witness; or retain ordinary pending status until owners supply reachable versions/fixtures. No recommendation or frozen-interface edit is implied.

ESCALATE: Solidity.Backend.WorldCalls.ClosedSourceControls.closed_callbacks — V13/RO; HiddenClients.closed_children_joint_impossible and continuation-semantic/evidence/hidden-clients.log prove the fixed answer strategy cannot satisfy the callback choice. Options: owner confirms intentional H69 no-callback separation; or owner supplies a reachable version/fixture and consumers re-prove.
ESCALATE: Solidity.Backend.WorldCalls.UnknownSourceControls.children — V13/RO; HiddenClients.unknown_children_joint_impossible and continuation-semantic/evidence/hidden-clients.log prove its fixed answer strategy cannot satisfy the callback choice. Options: owner confirms intentional H69 no-callback separation; or owner supplies a reachable version/fixture and consumers re-prove.
ESCALATE: Solidity.Backend.WorldCalls.UnknownRevertControls.children — V13/RO; HiddenClients.revert_children_joint_impossible and continuation-semantic/evidence/hidden-clients.log prove its credit/answer strategy cannot satisfy the callback choice. Options: owner confirms intentional H69 no-callback separation; or owner supplies a reachable version/fixture and consumers re-prove.

Semantic continuation bulk evidence is off Git under /workspace/h62-audit-readonly-calls/continuation-semantic/evidence/. Its handoff/report supersede earlier status summaries while retaining earlier sealed artifacts as historical. Full run-lean.sh, remaining ordinary witness work, RO v2 publication/migration, V13 separate compiler success with V15/P10 fixed outcomes and final all-statement acceptance remain unfinished.

## Mandatory performance stop

The semantic-continuation comparison failed with median 1.042592 s before and 1.879323 s after, delta +80.254967% (threshold +10%). The benchmark process exited 1 with SLOWDOWN_STOP. New proof work and further measurements stopped immediately. The source hash, command, Lean/Lake binaries and recorded resource flags match; no cause is established and no code-regression claim is made. No threshold override or repeat-to-green is requested.

Evidence: /workspace/h62-audit-readonly-calls/continuation-semantic/evidence/timing-before-samples.json, timing-after-samples.json, timing-after.json and performance-stop-context.json. The shell pipeline stopped before structural checks; those read-only non-Lean checks may be completed solely to prepare this blocked checkpoint. Full run-lean.sh and final witness acceptance remain pending. There are still 462 ordinary entries that may be worked after the performance stop is resolved; this report does not claim they all require missing producers. RO-v2/compiler-success dependencies remain separately pending; Q-CALLBACK-INTENT is resolved below.

Historical coordinator routing follow-up: Q-CALLBACK-INTENT was an RO-owner wait, not an unanswered human scope question. Published master was fetched and inspected at 0b2a648b32335f35ff323ff468f75907e926fc13; its new coordination tooling supplies no audit proofs or performance-stop resolution. The mandatory timing stop remains binding; no Lean, benchmark or new proof work was resumed. The 462 ordinary entries remain queued independently of producer waits.

Routing follow-up reviews: independent read-only inventory_finder and inventory_skeptic found no issues. Both confirmed the exact RO wait, unresolved classification, unchanged frozen originals, binding timing stop and 462 independently queued entries; neither ran Lean, benchmarks or writes.

## H82 continuation and resolved callback intent

RO has confirmed that ClosedSourceControls.closed_callbacks, UnknownSourceControls.children and UnknownRevertControls.children are intentional no-callback specialization controls. Their already checked callback-choice impossibility proofs now count as H69 audit results, never as positive callback witnesses. Q-CALLBACK-INTENT is resolved; its wait is removed. Earlier pending-intent and routing entries above are historical. Frozen statements and proof files are unchanged.

Current accounting supersedes earlier totals: 792 = 27 joint clients + 45 checked intentional impossibility results + 256 no-top-level-input statements + two pending RO v2 + 462 ordinary pending entries. Three additional results are explicit HiddenClients subset refutations; the 42 identity-pinned direct Not/Ne results in semantic-policy.json remain distinct. No semantic-policy shape was relaxed.

Current producer waits are claudecloud/move6-20261106/ro-v2 for reachable dispatch publication/migration and claudecloud/move6-20261106/v13-abi for actual compiler success with V15/P10 fixed outcomes. The mandatory performance hold is retained; independent offline evidence work continues under H82 without Lean or unchanged timing reruns. H82 removes statement-preserving exact-file permission blockers, but frozen semantics, Claude-owned source boundaries and retirement barriers remain binding.

## H82 consolidation intake and independent backfill

This VM accepts the successor cleanup assignment on the original goal. No retiree stop was requested and no retiree scope was edited or merged. Intake details and exact source-VM artifact requests are in tests/h62/item2/audit-readonly-calls/h82-member-intake.json. Three reported heads were fetched from published branches (proof-guards, shared-fixtures, duplication-scanner); proof-cleanup and readonly-bind branches were not advertised. Published snapshots do not satisfy final-handoff, frozen-assignment/scope-byte or stopped-acknowledgement barriers. All five member tasks therefore retain typed handoff waits. No member task has been executed from a guessed or shortened scope.

Independent offline timing backfill: analyze_timing.py validates the sample JSON against its unique receipt-hashed log record, recomputes medians/delta, checks source-command and toolchain/resource identities, rejects falsely passing receipts, requires canonical measurement/baseline arguments and rejects resource-guard stop markers. Nine timing mutation/control tests pass, alongside the existing 24 census/export/semantic controls. The saved failure remains +80.25496653564336%; the first two versus last three failed-run sample medians differ, but per-sample CPU/throttling, cache and concurrent-workload data are missing. Cause remains unestablished. This tool executes no Lean or benchmark, clears no hold and proves no theorem. Receipt hashes establish consistency of saved artifacts, not independent attestation of their origin.

H82 does not authorize rerunning a known timing STOP unchanged. Producer proof files, frozen interfaces, proof budgets, axioms and the 42 semantic-policy identity pins remain unchanged. Bulk current census, offline diagnostics and checks are under /workspace/h62-audit-readonly-calls/h82-consolidation/evidence/; historical failed timing receipts remain intact in continuation-semantic/evidence/.

H82 checkpoint review corrections: finder required updating primary current totals and obligations to remove the resolved callback wait. Skeptic found that unrelated receipt commands and resource-guard stop markers were accepted; canonical command/baseline binding and guard-stop rejection plus two mutation tests now address both findings. No failed timing evidence or proof statement was changed.

Final H82 checkpoint reviews: both independent read-only reviewers confirmed the fixes, current 792-statement accounting, unchanged proof/policy bytes, retained hold and unsatisfied retirement barriers. Nine timing tests, the prior 24 census/export/semantic tests, current census regeneration, diff check and full documentation path check pass. No Lean or benchmark ran in this continuation.

## H82 final-head receipt — pause barrier satisfied

The coordinator confirms final reports and paused goals for all five retiring members. This satisfies their stopped/goal-paused acknowledgement requirement; earlier missing-acknowledgement entries above are historical. No further pause acknowledgement is requested.

Final heads: duplication-scanner cbb1a40647401ea21551dc2070f5256248aa0835; proof-cleanup fb0defdca5c5fe9baa7fd8c1e1271a91d255e1c9; proof-guards a64e6db04cb73214fe33ab62b14318d564cff776; shared-fixtures e86fd8bb49ec55d608aa061b569272f45e497fa1; readonly-bind 55bb870a494fa176f13103ad4e1f72cc6870c764. Four published branch heads match and their commit objects were fetched. Proof-cleanup remains unadvertised and its commit absent locally.

No member merged or resumed. All five byte-exact original prompts remain unavailable locally, and exact scope manifests are unverified. The receipt itself records unavailable prompts and several missing or reconstructed scopes. The shared-fixtures committed reconstruction explicitly disclaims being the frozen prompt and labels its candidate paths a superset. Source-VM bundle/checksum paths and expected hashes are recorded in h82-member-intake.json for coordinator transfer; they are not accessible VM artifacts. Coordinator pause verification does not verify artifact bytes or gates. Integration and member implementation await those mandatory inputs; no reconstructed scope is substituted.

Current master was fetched and inspected; readonly source-history/world-call producers show no new deliverable resolving this audit's RO-v2/compiler-success waits. The existing performance hold remains unchanged. No Lean, benchmark rerun, member edit/merge, Claude-owned source edit/message, push or goal recreation occurred. Own census remains 792 = 27 joint + 45 intentional impossibility + 256 no-top-level-input + 2 RO v2 + 462 pending. No additional independent executable item is available under the retained hold and frozen-assignment barrier.

Final-head receipt reviews: independent read-only finder and skeptic found no issues. Both confirmed five satisfied pause acknowledgements, four locally matched final commits, missing proof-cleanup commit, no integrations or artifact-verification overclaim, and narrowed current waits. Neither used Lean or wrote files. Intake consistency, git diff check and full documentation path check passed (115 preexisting ambiguities, all references resolve).

## H82b initial scoped merges — historical before upstream adoption

The delivered package /workspace/h82-handoffs/h82b-20261106T180909Z matches the coordinator's archive, manifest and SHA256SUMS hashes; all 557 manifest entries verify. Original assignment payloads and the cleanup scope are authenticated by H82b, resolving prior metadata waits. Payload hashes are retained separately from historical rendered-envelope digests; no equality between those distinct representations is claimed. All five final head/report/pause records match.

Three eligible tool/doc/test member heads are now merged: duplication-scanner cbb1a40647401ea21551dc2070f5256248aa0835, proof-guards a64e6db04cb73214fe33ab62b14318d564cff776, and shared-fixtures e86fd8bb49ec55d608aa061b569272f45e497fa1. Earlier zero-merge and missing-metadata summaries are historical. These integrations preserve inherited incomplete gates and are not proof passes. Proof-cleanup final SHA fetch fails not our ref; its bundle is still needed.

Readonly-bind 55bb870a494fa176f13103ad4e1f72cc6870c764 remains unmerged: it edits CapturePhases, CaptureFailures and EnvironmentCredit outside the delivered live-exclusive production scope, and deletes their three private run_bind declarations counted in the original frozen 792 census. Public-header preservation alone cannot erase those entries. Retain its final head pending an explicit scope and frozen-entry preservation/migration disposition; do not silently rebaseline to 789. No Claude-owned source edit or message was made.

Independent scanner backfill fixed selected symlink identity/omission, passed 35 tests and a matched -8.997937% scanner pair with whole-report fidelity. The original Lean timing STOP remains failed and unchanged; no Lean or known-STOP benchmark was rerun. Own theorem accounting remains 792 = 27 joint + 45 intentional impossibility + 256 no-top-level-input + 2 RO v2 + 462 pending. No RUNTIME_GATE_PASS. Current intake ledger supersedes historical member waits above.

## Current H82b state after upstream adoption

Published master 5f14596531efea2be64f1a5e7a83afa5e151e865 already contained exact readonly-bind head 55bb870a494fa176f13103ad4e1f72cc6870c764. Following the coordinator instruction, rebase --rebase-merges origin/master completed cleanly. All four available original final member heads remain ancestors. No worker edit to Claude-owned production source was made; upstream adoption supersedes the earlier readonly-bind unmerged/scope wait. The pre-rebase checkpoint is retained at refs/h62-backups/pre-upstream-h82b and in exported history. Proof-cleanup final Git object is the only unresolved member integration object; its exact SHA fetch returned not our ref.

The original 792 obligations are retained, including Solidity.Lowering.Readonly.CapturePhases.run_bind, Solidity.Lowering.Readonly.CaptureFailures.run_bind and Solidity.Lowering.Readonly.EnvironmentCredit.run_bind. fidelity_delta.py diagnoses 789 retained lexical headers and three absent upstream private helpers; all three remain pending with original signatures and owner. No 789-entry rebaseline, replacement theorem assumption or inferred kernel equivalence is accepted. Both the diagnostic and unchanged strict census exit 1; the strict gate reports FROZEN_DRIFT in CaptureFailures. Current kernel/type/import fidelity and checked mappings remain pending. Four mutation controls verify missing private retention, implicit-context drift, renamed declarations and duplicate identities.

The scanner's final error-aware selector passes 40 tests. The last pre-rebase matched pair was 113.311471s to 107.120424s (-5.463742%); all report fields match except the scanner hash. Input hashes and membership are identical. These measurements do not cover the post-rebase corpus. Finder and skeptic confirmed the final selection fixes and fidelity diagnostic without Lean, benchmarks or writes; provenance is bound to current head/module/generator hashes in the export receipt. Three inherited shared-fixture ledger tests also pass.

No Lean or known-STOP benchmark ran; the original +80.254967% Lean hold remains unresolved. Compiler success still belongs to V13 with V15/P10 fixed outcomes; RO v2 dispatch migration remains pending. Scanner signature/dependency binding and live ownership, H55 production work and full acceptance remain incomplete. No RUNTIME_GATE_PASS. This is a fresh-thread handoff after intake/integration and independent implementation checkpoints; continue the same VM/branch/goal through the coordinator, never create a replacement goal or count this checkpoint as full completion.

Current structural checks: layers report 857 core modules with zero forbidden elaborator/parser reachability; registration check passes. Central fragments fail because upstream docs/README.md retains the V17 validation row absent from its fragments. Global documentation paths fail on four upstream references: StringApiWitness.original-unproved.lean in h62-6-migrate-theory, PanicBytes.lean in packet-panic H71-CANDIDATE, and two GenericMapped.lean references in generic-structuredflow registration. These files are unchanged from adopted master and outside this live scope; no generated central file or other-chain document was rewritten. Exact failures and producer handoff requests are preserved.

Tool identity only: Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake 5.0.0-src+797c613. No new KeySort or Lean proof gate was run; version commands are not proof passes. The committed h82b-evidence.json pins off-Git bulk outputs and their committed generators. Final finder/skeptic reviews confirmed the scanner fixes, all four integrated head ancestries, preserved 792 accounting and explicit failure boundaries. The fidelity receipt binds current module and generator hashes; no current kernel mapping is inferred.

## H70 continuation: causal fixture linkage and allocation census

Three further checkpoints are committed: authenticated blob-level allocation provenance, live source/signature fixture rebuilding consumed by the scanner, and complete selected-input ownership coverage with foreign allocation exclusions. The final 71 controls pass. The accepted gate runs seven isolated bounded compiler steps, rebuilding unchanged pinned fixtures and linking five source rows. It observes 1,559 bundled module artifacts and 4,677 companion-file states, keeps the raw five-record protocol unbound, and retains every candidate refusal. It is local execution evidence under the documented compiler/executor/concurrency limits, not remote attestation or a general Solidity signature proof. No stopped Source/Premises workload was run.

At committed snapshot d34af6bfe0b50ff9a9ff3ced979a390c78d97df6 the allocation census accounts for 15,596 files and all 15,509 selected source inputs, including nested Git trees. Of these, 8,070 untracked/ignored inputs remain review-only; 3,015 paths have authenticated foreign-chain read-only hints. No unowned opportunity is established. Member/checkpoint blobs, not historical added-path labels alone, support cleanup provenance; clean later drift is owner-review. Foreign live scope bytes are authenticated, migration-only scope is ignored, and no other-chain grant or stale producer routing is inferred.

Finder and skeptic found missing staged-copy pin comparison, insufficient active resource/descendant checks and post-member blob drift. All were fixed and exercised by real controls. They confirmed final coverage/refusal boundaries without tests, Lean, benchmarks or writes. Root verified that no production or Lean source, root, module map, toolchain, statement, premise, exclusion, trust set or proof budget changed in this continuation. Lean/Lake identity, layers and registration checks pass; current model/kernel/full-goal acceptance does not follow.

All 792 original obligations remain, including the three pending private run_bind mappings, with the original +80.254966536% timing STOP retained. The RO-v2 and V13 compiler-success requests remain staged for current Claude owners. Proof-cleanup's exact final Git artifact is still absent; no recovery or retired-goal wake is claimed. H86 evidence regeneration is limited to new, explicitly scoped fixture packets, never a rebaseline of old statements or missing raw evidence. Accepted evidence, hashes and remaining queues are in /workspace/h62-audit-readonly-calls/scanner-binding/. General declaration/kernel/dependency coverage and current global ownership remain unfinished. The committed binding-evidence.json pins the off-Git artifacts and generator identities.

## Frozen obligation and declared dependency ledger

The additive `scripts/h62/item2/audit-readonly-calls/obligation_dependencies.py`
joins the pinned historical census with an explicitly identified header snapshot.
All 792 original records retain their complete frozen signatures, owner tags and
witness statuses. All 129 mapped modules remain, including two with zero named
theorems. Current lexical comparison reports 789 retained headers and three
removed private helpers; these removals stay pending. Historical owners do not
establish current write ownership, and retained headers do not certify current
kernel types or definition meaning.

The join exposed and fixed a header-report collision: the optional dependency
`path` overwrote the target filename. New reports use a separate `target` field;
older reports cannot support per-target conclusions and are rejected by the
ledger. A fresh compiler header capture records 25 declared paths to the held
module and 104 no-path results. It parses inert source strings; no inventoried
project imports or bodies execute. Neither result clears the timing hold.

The ledger accounts for 50 pending ordinary statements with declared paths and
409 with no declared path, plus the three absent private helpers. These are
historical header classifications, not permission to compile or proof results.
All 462 ordinary witnesses, two RO-v2 items and owner compiler-success obligations
remain open. The 256 no-top-level-hypothesis rows establish no nested feasibility.

131 scanner tests, nine ledger controls and eight live header controls passed.
Independent read-only finder and skeptic reviews fixed held-target provenance,
inconsistent unknown statuses and zero-theorem module validation. Final reviews
found no remaining issue. No Lean proof statement, definition, budget or axiom
changed. Bulk records and reproduction evidence are kept at
`/workspace/h62-audit-readonly-calls/obligation-dependencies/` on the original VM;
the committed evidence record pins generator and artifact hashes. The prior
+80.254966536% Lean timing STOP remains. No runtime gate pass is claimed.


## H121 reachable-dispatch takeover and additive audit

H121 transfers RO V2 dispatch and consumer migration to this lane and freezes the
former Claude lane. Merged current master 254c60df6, then exact published head
2ed5f7ceb9a4204e4a1590b2eb9ca88fa8547601. The RO producer is no longer an external
wait. V13 actual compiler success and exact retired proof-cleanup object recovery
remain external dependencies. Original scope, all792 obligations and the original
+80.254966536% Premises STOP are unchanged.

A fresh bounded serial build of `SourceDispatchInterfaceV2Controls.lean` passed
in524.886s, peak aggregate RSS1644761088bytes, with4GiB available reserve and no
swap. Its declared90-module project closure excludes the held Premises module.
All three full branch conjunctions have simultaneous witnesses; both frozen V1
empty-selected cases remain checked impossibilities. V1 SourceDispatchEffects
and SourceAllHistories are byte-identical to the original base.

The additive `dispatch_v2_audit.py` preserves the complete pinned original census
and separately inventories all nine theorems in the two new V2 interface modules.
Their exact kernel names, modules and full types export and verify under the
unchanged budgets. Three explicit input-proof cases map to full joint clients;
six no-named-input-proof-binder rows imply no nested feasibility or adequacy.
The new `tests/h62/item2/audit-readonly-calls/StaticCallWitness.lean` gives all inputs and the actual static condition
at one tuple, then applies the unchanged storage theorem. Both checked theorem
axiom sets are exactly propext, Classical.choice and Quot.sound. Source-call
success, gas/fork boundaries and compiler adequacy are not concluded.

The four migrated consumers retain all28 original theorem headers, variable
contexts and visibility. Their compiled/timing comparison has not passed: a
sparse-library attempt failed package lookup; the complete-library baseline then
failed before V2 at `RawAt` reduction. Diagnostic output with all arguments shows
cached RawAt's old `callAddr` application alongside the current evaluator's added
RuntimePlan parameter. Q-H121-CACHE was sent through coord-ask (receipt
20261107T034608Z) for disposition of the dependency refresh under the standing
STOP. No held Premises compile or unchanged benchmark rerun was performed.
Cached imports are not source-binding or a full dependency recertification.

36 applicable Python controls pass, including omission, duplicate, version/module,
all792 retention and arbitrary-baseline header/context refusal cases. The initial
blanket discovery failed because it included a command-line resource harness and
two strict frozen-tree suites; this is retained as failed evidence. The strict
FROZEN_DRIFT gate is not bypassed or weakened. A development fixture escaping
error and both consumer failures are also retained, without a passing timing
claim. The warned prior shared-ledger refactor passed its separate matched +0.95%
comparison and189 scanner controls (project-accounting checkpoint810a59743).

Independent read-only finder/skeptic reviews confirmed the branch and migration
fidelity. Fixed findings: funded/entered qualification in the producer docstring,
and staged header/context comparison before any future consumer benchmark.
Neither reviewer executed code or used a Lean server. OracleAgrees supplies the
reply and returndata_any ignores the source outcome; these remain oracle buffer
laws, never source-world correspondence. Full original/inherited queues, consumer
validation, G42.02 source-callee linkage, owner compiler success and final gates
remain unfinished. Actual tools: Lean4.24.0/797c613; Lake5.0.0-src+797c613. Fresh
bounded KeySort prerequisites passed in the preceding committed project captures.
No new axiom, sorry, native_decide, statement weakening or proof-budget change;
no RUNTIME_GATE_PASS or master publication. Evidence is retained under
`/workspace/h62-audit-readonly-calls/ro-v2-intake/` on this VM.


### Q-H121-CACHE resolved; current consumers checked

Coordinator gh#78 chose A: one serial bounded current-tree dependency rebuild
through Premises, after the cache refetch, with no statement/premise/exclusion/
budget change, no before/after rebaseline and no runtime-pass claim. The
historical +80.254966536% STOP remains. The preceding pending-question account
is historical; no cache-refresh authorization is inferred beyond this answer.

Three cache setup attempts stopped at the same reserve guard: initially RAM-backed
/tmp extraction, then disk-backed file-cache pressure during extraction/copying.
All failed logs remain. The downloaded release SHA256 is
9279b7031dc5ee77ad2e7424ad7936172dc26e9da0d3a453e7e7c7d27a40d722,
from master4f0a2d6abe3a920d8c5a20c8c06d373a1014824d. After rechecking that checksum,
private interrupted artifact copies were replaced by hardlinks to the verified
complete pack and its unchanged installer resumed. It installed19782 artifacts
(6674078133bytes),6594 module entries, without relaxing any memory bound. These
cache labels and counts are setup evidence, not proofs.

The one approved current-tree build of ClosedSourceFrame, ClosedSourceConsumers,
ClosedSourceControls and SourceExpressionConsumer passed:237 jobs,7.042s wall,
885620736bytes peak aggregate RSS. No paired benchmark was rerun and these
observations establish no speed baseline. Selected old objects, including the
old RawAt-related object and current evaluator, were copied before refresh for
diagnosis; that snapshot is not a complete dependency pack or source-binding proof.

Current coverage labels the two frozen V1 cases as refuted with checked versioned
migration, separately from intentional negative controls and positive witnesses.
All792 original records remain; neither impossible V1 statement receives a
positive witness. New V2 interfaces and the four migrated consumers are checked;
the source-world OracleAgrees gap, V13 compiler success,462 ordinary witnesses,
three private mappings, broader original/inherited queues and final full gates
remain unfinished. The original strict frozen-tree gate remains failed on drift.

The transferred producer model and input-byte controls also build successfully
(236 jobs,17.597s,938057728bytes peak RSS), reusing the refreshed dependency
objects. This checks their stated model laws only: the source outcome remains
unused by returndata_any and no source-world oracle link is inferred. No new
Premises timing comparison or runtime-pass claim was made.


## Coordinator review follow-up and new master (2026-11-07)

Rebased the current fixture-validation checkpoint onto coordinator master
`d93f6839c613468610ea488356b174cd183e3772`. Every one of its80 compiled source
inputs and all driver/tool pins remained byte-identical after the rebase;
`capture-current-closure/evidence/rebase-and-case-join.json` records that check.
The byte/source-name join links the prior25-declaration ledger's16 mappings
(12 distinct fixture names) to the actual current38-declaration axiom probe.
This does not restore the three removed private identities, certify historical
raw type equivalence or promote all792 audit obligations to acceptance.

StaticCallWitness's module comment now explicitly states that its existential
establishes only the static-mode flag equation, with requested=true. The separate
client applies the existing storage law. All code from its namespace onward is
byte-identical; no theorem statement or proof changed. The consumer checker
rejects an empty MIGRATED list before parsing arguments, writing output or
invoking Lean; its new refusal control passed with the four existing tests.
The paired timing checker itself was not executed.

`tests/h62/item2/audit-readonly-calls/ro-v2-intake.sha256` commits the exact SHA256
of the off-Git current-consumer receipt and its raw log. Both original coverage
rows now cite this manifest; their statuses and original V1 refutations remain
unchanged. The manifest pins old evidence, not a new proof or a portable runtime
gate. Both files verified; the raw receipt SHA256 is
93a0617fe8a68cb6516003687abcc96f9f6761d6aaeba75e2a1ab2b65ec74f52.
The wording typo All28 was corrected. Five consumer controls and five existing
V2 audit controls passed. Independent read-only finder and skeptic found no
remaining issue in these review fixes; neither executed Lean or wrote files.
The documentation gate now passes on the new master: all references resolve,
with139 pre-existing ambiguities. The prior two-reference v17 wait is resolved.

The historical Premises +80.254966536% STOP and full original acceptance remain
open. H121 compiler-success/G42.04 adequacy still belongs to
solidity-compiler10-20261028/memory-reference-structs; our full RO source/callee
outcome and physical-frame producer remains unfinished. The historical exact
proof-cleanup object remains UNVERIFIABLE without original recovered bytes.


## Frozen callback witness fidelity and coverage (2026-11-07)

Two original interface rows now have checked joint witnesses against the exact
assigned base c6f550e281a7e5affa9a99bc2cdaed556dec00e4:
Solidity.Lowering.Readonly.EnvironmentSteps.refused and
Solidity.Lowering.Readonly.EnvironmentCredit.callback_credit_failed. The first
has depth and static-value cases; the second has one admitted credit-overflow
case. These are three joint cases for two statements, not three new obligations.
The unchanged additive CallbackBoundaryControls module supplies actual choice/
guard and instance/credit equations together, and clients check the resulting
source runs. No statement, premise, definition, exclusion or budget was repaired.

`scripts/h62/item1/readonly-bind/check_original_callback.py` reads the original
Git blobs and freshly compiles the complete57-module unheld callback closure in
an isolated library with pinned SDK root and no current project-cache fallback.
It then checks all eight witness theorems and exports both original public
interface types using the existing metadata helper's kind/module/name checks.
Their raw type digests match the prior792-declaration export. All eight new
axiom sets contain only propext,Classical.choice and Quot.sound. SDK modules
remain toolchain inputs, not independently source-certified dependencies.

Review fixed two analogous digest-retention gaps: the authenticated census
artifact digest and Git-base toolchain digest are retained before compilation,
then verified at final sealing rather than adopted from a later read. Five
external refusal controls passed. The final sealed gate passed in376.049s with
1675214848bytes aggregate peak RSS. Earlier390.981s and382.576s observations are
retained separately; they are not matched speed comparisons or a rebaseline.
Actual tools remain Lean4.24.0/Lake5.0.0-src+797c613,-j1,12GiB cap,4GiB reserve,
no swap. Original KeySort compiled successfully within the frozen closure.
The held Premises module is rejected before dependency compilation.

An owned detached C6 checkout was used only for the strict source census.
All129 module hashes and all792 declaration identities, source headers, variable
contexts and visibilities match the authenticated original inventory. Only the
callback closure/two interfaces received new kernel validation. Other790 semantic
records retain their previous evidence; the current three deleted private IDs
are not restored by historical objects.

Coverage now contains26 joint-witness rows plus3 target-failure joint rows.
The retained full ledger has45 intentional impossibility rows,256 no-top-level
input-hypothesis rows,2 frozen-V1-refuted/versioned-migration rows and460 pending
ordinary rows:792 total. These are bookkeeping categories, not a whole-goal
completion claim. The source-only census separately reports758 pending because
it does not rerun the retained semantic classification; it is not a replacement
for that full ledger. Exactly two witness statuses changed from the previous
current coverage view, with all other790 rows retained.

`tests/h62/item1/readonly-bind/original-callback.sha256` pins the frozen receipt,
types, raw probe log, inventory, outer bounded receipt and coverage/fidelity
reports. Raw bulk evidence remains off Git under
`/workspace/h62-audit-readonly-calls/original-callback/`.
Independent read-only finder and skeptic confirmed the fixes and final two-row
integration; neither executed Lean or wrote files. The current callback checker
also now derives its PASS counts from observed records; five controls and its
current kernel check passed. Exact older helper bytes are preserved with the
frozen validation provenance. Rebased onto coordinator master a10b60f23315.
No Lean theorem/proof changed in this checkpoint; no new axioms/sorry/native_decide.
All remaining original/inherited queues, full acceptance, broader binding/live
ownership and RO source/callee plus physical-frame adequacy remain open. The
historical +80.254966536% Premises STOP is unchanged; no RUNTIME_GATE_PASS.


## Known, unknown and failed credit joint witnesses (2026-11-07)

Three additional original interfaces now have explicit simultaneous input
witnesses: EnvironmentCredit.known, EnvironmentCredit.unknown and
EnvironmentCredit.failed. CreditJointControls checks choice, post-record instance
lookup and actual successful/failed credit at the same state sequence; the
unknown case supplies its two hypotheses without inventing a credit equation.
Clients apply the unchanged laws and verify success bytes[7], skipped unknown
credit or overflow halt. Further observations check the model's permitted static
balance credit with storage preservation and the unknown case's unchanged
execution state. Eight supplementary theorems cover three original obligations.
No compiler/EVM/gas/fork, constructor reachability or whole-world claim follows.

The new checker admits only the exact executed frozen/current parent receipts.
Frozen mode rechecks all57 Git-base source/snapshot hashes and58 parent objects;
current mode checks its77-module source graph and80 objects. Parent logs, trusted
compiler/toolchain input pins, SDK root and the new source/object/probe/logs are
checked before and after. Authenticated parent and original792 artifact digests
are retained, never resampled after authentication. This is checked dependency
artifact reuse, not a fresh rebuild or independent SDK source certification.

The frozen gate passed in5.028s at796049408bytes peak aggregate RSS; the separate
current gate passed in4.524s at795627520bytes. Each checked eight theorem axiom
sets (only propext, Classical.choice, Quot.sound) and exported the three original
interface types with module/name/kind checks. Frozen and current results remain
separate: equal source or type hashes would not prove model-definition equality.
Their balance representations differ; a kernel-checked closed calculation proves
the same balance equality in both models, without changing the statement.
Initial representation-specific proof failures are retained separately.

Six external refusal controls passed for parent profile/byte binding, frozen
source/object/log mutation and missing objects, flat extra-module aliases,
forged census data, unauthorized/missing/duplicate axioms and retained digest
substitution. Five existing census tests passed. Independent read-only finder
and skeptic confirmed the final proofs and exactly three-row integration; neither
executed Lean or wrote files. Nine raw evidence pins are committed in
`tests/h62/item1/readonly-bind/credit-joints.sha256`.

All792 rows remain accounted once. The retained semantic ledger now has29 joint,
3 target-failure joint,45 impossibility,256 no-top-level-input,2 frozen-V1-refuted
migration and457 pending ordinary rows. Exactly three records changed; other789
retain prior evidence and all three current private-ID gaps remain. The strict
original source census separately reports755 pending because it does not replay
the retained semantic classification; it is not a replacement for that ledger.
The whole original/inherited assignment is unfinished. Historical Premises
+80.254966536%STOP remains; no held workload rerun, rebaseline or runtime pass.
Actual tools remain Lean4.24.0/Lake5.0.0-src+797c613 with -j1,12GiB cap,4GiB
reserve,no swap; passing KeySort evidence is retained in the admitted parents.
No original statement, definition, premise, exclusion, axiom or budget changed;
no new sorry/native_decide. Evidence and handoff are under
`/workspace/h62-audit-readonly-calls/credit-joints/`.


## Joint actual capture-failure inputs (2026-11-07)

Four original CaptureFailures laws now have closed simultaneous witnesses:
target_failed, value_failed, arguments_failed and code_rejected. The conjunctions
include the declaration signature, integer validity when required, every actual
phase run and the rejection guard. The code-rejection witness evaluates arguments
from before to after; encoding, lookup and rejection all use after. Its client
preserves the local mutation while adding no callee events. The three timeout
clients preserve timeout and their exact state. Nine supplementary theorems
discharge four original input-feasibility obligations, with no compiler-success,
EVM, gas/fork, constructor-reachability or physical-frame adequacy claim.

The existing credit checker now selects one fixed suite; its default credit path
is preserved. Frozen capture checking reconstructs the exact C6 import graph,
compiles 11 missing unheld modules and copies 54 reused objects into one private
namespace after checking authenticated source/object pins. All 58 parent objects
are verified before and after. A first sparse-root attempt failed because Lean
selected a partial namespace; finder and skeptic independently identified that
issue. The corrected complete namespace retains copied object hashes. An
explicit intrinsic Vals address type fixed an elaboration ambiguity; neither
failure is reported as a pass. No historical held Premises workload was run.

Final frozen checking passed in 21.101 seconds at 818544640 bytes peak aggregate
RSS; separate current checking passed in 8.079 seconds at 797831168 bytes, reusing
its authenticated 80-object parent. Default credit checking passed in 4.527
seconds at 791777280 bytes. These are bounded gate measurements, not a matched
before/after build comparison or a release of the +80.254966536% STOP. The nine
capture axiom sets contain only propext, Classical.choice and Quot.sound. Actual
tools are Lean 4.24.0 / Lake 5.0.0-src+797c613; passing KeySort prerequisite
remains in the admitted parent evidence. All checks ran serially with -j1,
12 GiB cap, 4 GiB reserve and no swap. Artifact reuse is not a fresh closure
rebuild or independent SDK source certification; frozen/current model definitions
are not asserted equal.

Eight external refusal controls and five census tests pass. Independent read-only
finder and skeptic confirmed the fixed namespace and exactly four-row coverage
addition; neither executed Lean or wrote files. All 792 original rows remain:
33 joint, 3 target-failure joint, 45 checked impossibility, 256 no-top-level-input,
2 frozen-V1-refuted migration and 453 ordinary pending. The other 788 records
retain prior evidence; three current private identities remain unmatched. The
strict original source census separately reports 751 pending because it does
not replay the full semantic classification. Ten raw evidence hashes are in
`tests/h62/item1/readonly-bind/capture-joints.sha256`.

Raw gates, sources, objects, failed attempts, census and handoff are under
`/workspace/h62-audit-readonly-calls/capture-joints/`. No original statement,
dependent definition, premise, exclusion, axiom or budget changed; no new
sorry/native_decide. Full original/inherited acceptance and RO G42.02 execution
plus source/callee and physical-frame correspondence remain open. No runtime
pass, goal completion, publication or master merge is claimed.


## Complete encoding and composition inputs (2026-11-07)

Rebased the clean assigned branch onto master
80c156bf13d1900acf9cdae1556496ee3473e0cd. Its intervening changes did not
supply these witnesses or alter the relevant readonly sources. The authenticated
current parent still matches its complete source/import graph after the rebase.

Two more original laws have simultaneous witnesses: CaptureFailures.encoding_failed
and CapturePhases.compose. The encoding conjunction includes signature, integer
bounds and all four actual phase runs. Its typed array argument points to an
allocated heap object, and the encoder actually reports not ABI-encodable. The
composition conjunction includes signature, integer bounds, all five phase runs
and admission: receiver/value start at before, arguments mutate before to after,
and encoding/lookup/admission use after. The unchanged law produces CapturedAt;
its client resumes at after with the original receiver rather than the assigned
local address. Seven supplementary theorems cover two original obligations.
Capture success is not callee success or an owner's compiler-success theorem.

The existing fixed-suite checker now compiles the unchanged allocated-array
helper separately in its isolated library. Its source, staged source, object and
logs are sealed, and imports must belong to the authenticated project closure or
trusted SDK; held, unverified and foreign dependencies are refused. The default
credit suite remains unchanged. Frozen validation still compiles 11 missing
unheld original modules and copies 54 authenticated reused objects into one
private namespace; 58 parent objects are verified. Current validation reuses
its independently source-bound 80-object parent. No equality of frozen/current
model definitions or independent SDK source certification follows from reuse.

The final frozen gate passed in 22.618 seconds at 811257856 bytes peak aggregate
RSS; current passed in 5.540 seconds at 799129600 bytes. Default credit regression
passed in 5.029 seconds at 792158208 bytes. These are bounded individual checks,
not a matched before/after speed comparison or a performance STOP release.
The initial frozen pass preceded a state-sequence comment correction; the final
frozen/current gates check the corrected bytes. Finder and skeptic both requested
that comment correction and otherwise found no defect. Final independent reviews
also confirm the two-row coverage addition; neither reviewer executed Lean or
wrote files. Ten external refusal controls and five census tests passed.

All seven new axiom sets contain only propext, Classical.choice and Quot.sound.
Actual tools are Lean 4.24.0 and Lake 5.0.0-src+797c613, serial -j1 with 12 GiB
cap, 4 GiB reserve and no swap; passing KeySort remains in admitted parent
evidence. No original statement, dependent definition, premise, exclusion, axiom
or budget changed; no new sorry/native_decide. No held Premises workload ran.

All 792 original obligations remain: 35 joint, 3 target-failure joint,
45 intentional impossibility, 256 no-top-level-input, 2 refuted-V1 migration
and 451 ordinary pending. Exactly two records changed; the other 790 retain
prior evidence. All three current private identity gaps remain. Strict original
source accounting covers 129 modules/792 names with 749 source-only pending;
it does not replace the fuller semantic ledger. Ten raw evidence pins are in
`tests/h62/item1/readonly-bind/capture-composition.sha256`. Raw gates, helper
provenance and the handoff are under
`/workspace/h62-audit-readonly-calls/capture-composition/`.

Whole original/inherited acceptance, broader binding/live ownership, actual
compiler success and full RO G42.02 source/callee execution plus physical-frame
correspondence remain unfinished. Historical +80.254966536% Premises STOP remains;
no runtime pass, goal completion or master publication is claimed.


## Executed native reply adapter (2026-11-07)

The H121 producer investigation found that MachineV2 CALLIN still reads reply
and accepts oracles; SourceCallProducerV2.returndata_any does not relate a source
callee to executed code. A new additive ExecutionReplies helper makes a narrower
piece explicit: prepare the target child receiver/caller/value header and exact
input memory window, run an explicit native code image, and derive reply/status
from the existing OutV2.exit observation. No source outcome or desired bytes are
arguments of attach. Actual success/revert payloads are retained; fault and
pending execution produce no adapter. Funded and poor CALLIN cases are both
accounted for, with caller memory/storage preservation proved at callInStep.
Native echo/revert images and fault/pending controls distinguish outcomes.

This precomputes a target execution reply and configures the frozen machine's
oracle for one selected call. It does not replace CALLIN with recursive callee
execution. Its reply is input-specific, while accepts(address,value) has no input
parameter, so acceptance affects every input at that pair. The adapter is for
single-input use. Child final state is discarded; no world code selection,
callee state commit, emitted caller program, Source-to-core compiler, nested-call,
gas/fork, heap/allocator P1 or full G42.02 adequacy follows. The existing native
frame proof is only caller memory/storage at callInStep. These limits leave our
full RO source/callee execution and physical-frame producer unfinished.

Final validation freshly compiled all 16 project dependencies (including
KeySort) and the helper in a private library, without shared project cache
fallback or any held Premises import. The exact current source/import graph,
staged sources, objects, tool inputs and logs are sealed before success. Eleven
theorem axiom sets contain only propext, Classical.choice and Quot.sound. The
final-reused gate passed in 69.847 seconds at 828407808 bytes peak aggregate RSS.
Actual Lean 4.24.0 / Lake 5.0.0-src+797c613; explicit -j1, 12 GiB cap, 4 GiB
reserve, no swap. Initial elaboration/proof failures and earlier successful
pre-reuse checks are retained separately, not substituted for this final gate.

Self-review replaced a duplicate outcome classifier with existing OutV2.exit.
Five paired warm-cache runs from the same source path, dependency library,
compiler and flags measured 0.978159551 seconds before and 0.943724352 after
(medians, -3.520407%); median peak RSS was 571092992 and 570155008 bytes.
This native-adapter measurement does not rebaseline or clear the historical
Premises +80.254966536% STOP. The first timing utility missed staged-file and
final-log checks; finder and skeptic independently found the gap. The corrected
utility verifies actual staged bytes before/after each compiler run, seals all
logs, pins instrumentation, and checks the exact current dependency graph. Its
library receipt is caller-supplied: byte binding is not build authentication or
SDK source certification. Only the corrected sealed measurement is pinned as
final timing evidence; earlier timing is historical. Five external controls
include staged-file/log substitution and unauthorized/incomplete proof evidence.

Independent read-only finder and skeptic confirmed the target-only scope and
reviewed the integrity fixes; neither executed Lean/tests or wrote files.
Nine raw pins are in
`tests/h62/item2/audit-readonly-calls/execution-replies.sha256`; evidence and
handoff are under `/workspace/h62-audit-readonly-calls/execution-replies/`.
No original obligation is discharged by this adapter. Coverage remains
byte-identical: all 792 rows, 451 ordinary pending, three private-identity gaps,
and all previous witness/refutation classifications remain. No frozen statement,
dependent definition, premise, exclusion, axiom or budget changed; no new
sorry/native_decide. Full original/inherited acceptance, owner compiler success,
our full H121 producer and runtime gates remain unfinished. No runtime pass or
master publication is claimed.


Post-rebase validation on coordinator master 658d1b1d14c68a031c137f576764ec7e9e7a6359
found one inherited documentation failure: the Claude-origin compatibility
module `Solidity/Yul/Compilation/P20InterfaceV2Controls.lean` cites the absent
file tests/h62/item2/audit-v09-passes/P20InterfaceV2Controls.lean. Ticket
RO-DOC-P20-REF routes this exact docstring repair to the live Yul/original vy3
owner through the coordinator. That source remains read-only here. The global
documentation gate is failing, not waived; native source/object bindings and
proof results remain unchanged. Original/inherited full acceptance is pending.


## Native caller execution with the checked void-call frame (2026-11-07)

On coordinator master 902e87762e5c3fb863bc3a592892f2dc09dfa979, additive audit
modules ExecutionCall and CheckedExecutionCall connect the earlier native reply
adapter to the actual stores/pushes/CALLIN/POP caller image. Generic proofs keep
the caller stack/storage, the written input window and every memory word outside
that window; funded and poor cases remain separate. The caller prefix returns
normally even for child revert; its journal retains the actual child flag and
raw bytes. It remains a precomputed, single-input adapter for frozen CALLIN.

The checked composition uses the existing Mutation.compileCall-selected void
family and classifies its actual typed-core Stmt.run outcome. It keeps the entire
InterfaceV1.Returned certificate, including representation, stack, base extension,
allocator growth, cursor and older words, alongside actual native child execution.
No desired source outcome or target-run premise replaces that proof. Existing
compiler-selected success and write-before-OOB bare-revert fixtures supply both
branches. Entry.capacity survives the stack-only preparation lemma.

This is typed-core compiler/frame composition, not resolved Source callee
selection or Source/world adequacy. Generic physical Entry is required AFTER
input preparation; only empty byte input has concrete entry-preserving fixtures.
There is no ABI bytes-to-typed-arguments theorem, arbitrary-input preparation
frame, child state commit, world/code selection, nested-call, gas/fork or general
P1/G42.02 result. No approved Source profile is introduced. The original compiler
success/G42.04 producer remains memory-reference-structs work. These helpers are
unregistered audit modules under the tests directory, not a published core API.

The final sealed check passed in 708.784 seconds at 1666904064 bytes peak
aggregate RSS: 214 fresh project dependencies, 17 authenticated native parent
objects, two new modules, 17 theorem axiom sets and five canonical module identity
controls. The dependency union contains 230 project modules, plus three audit
helpers. The current source/import graph, staged bytes, objects, tools and logs
are verified before success. No held Premises import is allowed; a new negative
control rejects such drift. The authenticated parent includes the passing bounded
KeySort prerequisite. Actual Lean 4.24.0 / Lake 5.0.0-src+797c613, explicit -j1,
12 GiB virtual-memory cap, 4 GiB reserve, no swap. Only propext, Classical.choice
and Quot.sound occur in the 17 axiom sets. Eight external refusal/inventory
controls pass; they are tooling tests, not proofs of original audit coverage.

Failed attempts remain in the evidence: resource stop; deliberate module-root
correction; TermSize thread-creation failure; global async=false triggering
Evm/Correct's unchanged 11000-heartbeat limit; and two local elaboration errors.
The last two proof errors were fixed without changing statements. A bounded
TermSize diagnostic passed with async=false, reducing peak virtual memory from
about 10.9 GiB (44 observed threads) to about 2.8 GiB (five threads). The first
thread diagnostic had a log/data filename collision and lost its detailed
samples; the corrected diagnostic uses distinct files. Final scheduling disables
asynchronous elaboration ONLY for TermSize; all proof budgets remain unchanged.
This additive check is not a before/after rebaseline and does not clear the
historical Premises +80.254966536% STOP.

Read-only finder and skeptic found no further defect after the log/root fixes,
held-module fence and proof repairs; neither used Lean/server/tests or wrote
files. Final kernel evidence is separate from those source reviews. Raw evidence,
failed attempts and handoff are under
/workspace/h62-audit-readonly-calls/execution-call/; portable content pins are in
`tests/h62/item2/audit-readonly-calls/execution-call.sha256`. Internal receipt
paths remain VM-specific; no independent off-VM acceptance is claimed.

All 792 original obligations and coverage classifications remain byte-identical:
35 joint, three target-failure joint, 45 intentional impossibility, 256 without
top-level input hypotheses, two refuted-V1 migration cases and 451 ordinary
pending. Three current private-identity gaps remain. This checkpoint discharges
ZERO original rows, changes no frozen statement/definition/premise/exclusion or
budget and adds no sorry, axiom or native_decide. New fixture delta: two audit
modules, 339 Lean lines; zero production modules changed. Full inherited work,
Source-selected compiler/world binding and scope-complete acceptance remain open.
No RUNTIME_GATE_PASS, goal completion or master publication is claimed.

RO-DOC-P20-REF now has an owner repair at
c9cf710a8459581006150a462b69ae8c4f0d13e0. It is not on this master; the repository
documentation gate remains failing until adoption and recheck. The exact retired
proof-cleanup object fb0defdca5c5fe9baa7fd8c1e1271a91d255e1c9 remains unavailable;
its historical acceptance stays UNVERIFIABLE, without rebaselining or revival.


## Fresh original-obligation dependency census (2026-11-07)

After fetching master 32d810f1dae86d884f9799b0444af959dd291bda, the previous
native/frame checkpoint rebased from e4d0e8e1dba10ac26a8cb15065c92fd794facd39
to e96d96705245031cdf16c33a3db9ee047685c001. Its saved proof evidence remains
at its original source revision; this census adds no current-tree proof claim.

The new current_dependencies driver joins all 792 original statements in all
129 original modules to a FRESH compiler-parsed declared-header capture. Existing
SDK-only header tooling treats tracked core source as inert strings: no
inventoried project import/body executes, including held Premises. All 6663
captured core nodes parsed successfully; eight real header controls passed.
Separate-package/test/unregistered paths outside the configured core roots are
not promoted to coverage. Dynamic references and body elaboration remain unknown.

The driver verifies the reviewed historical ledger's exact source signatures,
variable context and visibility against original c6f550e Git blobs and the frozen
module map. It retains every original row, historical owner and reviewed status.
For each original module it fingerprints the complete observed declared source
closure: full source hashes, module identity, header hashes, exact import flags,
resolutions and observed SDK artifact digests. Cycles terminate; unresolved and
missing sources remain explicit. A complete declared observation says nothing
about whether a dependency cycle compiles or whether the bodies are adequate.
Committed changed/added dependency paths are compared against original Git blobs;
127 of 129 original module closures contain such byte changes. These include
proof/comments/import changes; they are not semantic weakening findings.

Final observations: 770 lexical headers retained, 19 header/context drift, three
absent private declarations. Those exact private identities remain
CaptureFailures.run_bind, CapturePhases.run_bind and EnvironmentCredit.run_bind;
their historical RO owner is retained, never silently mapped to shared Hoare
helpers. Twenty-five original modules have declared paths to held Premises;
104 have no declared path. Neither result grants compilation permission or
clears the historical +80.254966536% timing STOP. All rows retain pending current
kernel fidelity and unverified live ownership. No exact current type/body
correspondence, global premise inhabitance or joint witness follows.

Nine external controls pass, including unchanged signature/changed dependency
body, private omission, cycles, SDK digest/import-flag drift, missing/unresolved
inputs, forged paths, duplicate nodes and zero-theorem modules. Independent
read-only finder and skeptic found the same child-receipt provenance gap: the
first driver sampled the receipt file's hash after capture rather than deriving
it from the successful returned receipt. The fix authenticates exact serialized
live-result bytes before reading the file and rechecks that digest after
accounting; a new substitution/failed-child control covers it. Both reviewers
confirmed the fix without executing Lean/tests/server or writing files.

The final fresh capture passed after that fix. The earlier pre-fix result is
historical only; its ledger output is byte-identical to the final same-head
capture, which supports deterministic observation, not acceptance of the old
receipt chain. Current source/head/configuration, tools, source closures, child
receipts, process logs and observed SDK artifacts are checked before success.
The actual inert-header parser command took 9.657428673 seconds at 635973632 bytes
peak aggregate RSS, exit 0. Lean 4.24.0, explicit -j1 --tstack=131072,
LEAN_NUM_THREADS=1, capped memory with 4 GiB reserve and no swap; no proof budget
change. No KeySort/runtime/full-proof gate is inferred from metadata parsing.

Raw captures/receipts, the lossless ledger, refusal controls and reviews are under
/workspace/h62-audit-readonly-calls/current-dependencies/. Content pins are in
`tests/h62/item2/audit-readonly-calls/current-dependencies.sha256`. The committed
driver is the deterministic generator; bulk records remain off Git. Receipt
paths are VM-specific; content verification is not independent SDK certification.

All original classifications remain: 35 joint, three target-failure joint,
45 intentional impossibility, 256 without top-level input hypotheses, two V1
refutation/migration cases and 451 ordinary pending. ZERO original obligations
are discharged here, and coverage.json remains unchanged. No Lean declaration,
frozen statement/definition/premise/exclusion, axiom or budget changed. All
original/inherited proof acceptance, owner/compiler-success work, nineteen
current lexical drifts, three private gaps and the full H121 Source/world/native
frame producer remain unfinished. No RUNTIME_GATE_PASS, goal completion or push.

Next independent work: use this explicit census to inspect the nineteen current
header/context changes and their original statements, preserve the three private
identities, and continue supported joint witness/refutation work on independently
checkable inputs. Declared no-path is not a release of any timing hold. Live
ownership still requires current authoritative evidence. Historical proof-cleanup
fb0defdc remains UNVERIFIABLE; P20 owner repair still awaits integration/recheck.


## Exact signature-drift review (2026-11-07)

Fetched/rebased onto master 48ff6a2ebd9a6531a288c0d203c682c4075be25b before
this item. The saved capture records its actual full source head separately;
no prior native or witness proof is recertified by this source-only review.

The new signature_drift driver preserves all 792 original identities and emits
full original/current signatures, variable context, visibility, historical kernel
name/owner, and unified diffs for every changed or absent declaration. Exact
observed-pair pins classify the known 22 cases without rewriting statements or
normalizing the frozen gate: eleven `.balance.val` to `.balance` observations,
one Word-to-Monetary.Balance parameter change, seven added E.mapFree parameters,
and three absent private run_bind declarations. Unrecorded pairs, residual
premise/context changes, or later mutations remain unreviewed drift. A same-text
pattern elsewhere is not enough. Hoare.run_bind is not a replacement identity.

Pinned coordinator decision input 5e4335f38abb74a8864863577b04363980659e6b92a4a9835e8a0efa5bd833dd
records H19's exact unbounded monetary representation and H60's Source typing
repair. Those explain upstream evolution; they do not establish H57 statement
transport, approve an added audit premise/exclusion, or prove correspondence.
Monetary.Balance is Nat, so the domain change is not treated as a mere projection
rename. Source Types/Typing/Machine/Monetary and the BalancesFit writer inventory
are captured as read-only definition context. In particular the structural
unbounded History.balance step is not automatically covered by Word range facts.
No semantic weakening/equivalence verdict follows from lexical transformation.

All 19 changed statements retain pending frozen/current transport and kernel
fidelity; all three private identities remain absent and pending. A saved owner
request asks the coordinator/H16 Source producers for exact versioned statement
and consumer-proof references. H19/H60 decisions already authorize their model
work; this is an evidence request, not a new human scope/permission question.
No Source or original theorem file was edited.

Seven external controls pass: extra premise/context stays visible even when a
pair hash is altered, unrecorded patterns stay unreviewed, private aliases cannot
close absence, original/duplicate/foreign identities are checked, raw diffs are
retained, and observation pin parsing/hashing shares one byte buffer. Finder
found a split snapshot between the initial pins-file hash and later parsed
bytes. The one-buffer fix derives saved bytes, parser input and retained digest
from the same read; both read-only finder and skeptic confirmed it. Neither ran
Lean/server/tests or wrote files. The pre-fix final/ capture is historical only;
sealed/ is the corrected accepted source capture. No Lean executed in this item.

Raw dossiers, captured current source/definition bytes, decision context, Git
history, reviews and owner request are under
/workspace/h62-audit-readonly-calls/signature-drift/. Pins are in
`tests/h62/item2/audit-readonly-calls/signature-drift.sha256`; the committed
driver regenerates the bulk dossier. All 792 rows remain: 770 lexical headers
retained, 19 drift, three private absences. Historical 451 ordinary pending and
all other witness/refutation classifications remain unchanged; ZERO original
obligations are discharged. Live ownership is unverified, not inferred from
Git author history. No Lean declaration, frozen statement/definition/premise,
exclusion, axiom, sorry/native_decide or proof budget changed. Full original and
inherited acceptance, joint witnesses, H121 Source/world/native-frame adequacy,
compiler success and runtime gates remain open; historical Premises
+80.254966536% STOP remains. No runtime pass, goal completion or publication.


## Ten frozen/current EffectRules joint witnesses (2026-11-07)

The same additive EffectRuleWitnesses client now proves joint inputs and applies
all ten original EffectRules statements: of_same_ex, bind, sub, attempt, parent,
pure, halt, st, locals and setLocals. The concrete Env, typed Bool locals and
Source state are inhabited terms. Effect premises are proved for ALL locals and
states; bind supplies the entire universally quantified Unit continuation, using
the same first/next computations as the final application. This establishes
premise satisfiability with original theorem applications, not compiler adequacy.

The computations are actual Source EM primitives: emitting two ordered events,
emitting then reverting with exact bytes, catching that failure while retaining
the reached event, and changing locals. Four observation theorems distinguish
events/locals from the journaled world tracked by Effect. EM.sub returns its
inner locals alongside the value; the observation records that pair. This is
not a deployed callback, ABI/body compiler bridge, general P1/G42.02 contract,
gas/fork proof or compiler-success theorem. No supported-program exclusion or
new premise is introduced. The module remains an unregistered additive audit
fixture under tests; no production root or module map changed.

Separate fresh isolated builds validate the exact c6f550e original dependency
closure (24 project modules) and the current closure (29). The identical witness
source compiles in BOTH; all ten original kernel type hashes match the original
reviewed census in both, and all sixteen helper theorem axiom sets use only
propext, Classical.choice and Quot.sound. These are two independent witnesses
under their respective definitions, not a proof that changed model definitions
are equivalent. Source snapshots, objects, queries, outputs and tools are sealed;
no shared project-cache fallback or held Premises import is permitted.

The final frozen gate passed in 263.208 seconds at 1686777856 bytes peak aggregate
RSS; current passed in 242.363 seconds at 1626148864 bytes. Actual Lean 4.24.0 /
Lake 5.0.0-src+797c613, explicit -j1 --tstack=131072, LEAN_NUM_THREADS=1,
12 GiB virtual cap, 4 GiB reserve and no swap. Frozen/current elapsed times are
not a before/after performance comparison. Bounded current KeySort separately
passed, exit 0 and empty diagnostics, in 1.516 seconds. Historical Premises
+80.254966536% STOP remains; no unchanged stopped workload rerun or runtime pass.

The checkout was adopted to coordinator master
a8f684928fa085d8976ead33e3d0db30208e7a4f AFTER the stable proof runs; every
current source/tool/log/object pin and the complete current dependency graph
still matched. The receipt source head records the actual checking revision.
The first frozen attempt reached the witness but failed its EM.sub observation
(Unit instead of the actual value/inner-locals pair); the corrected per-file
check and diagnostic passed before the two fresh final gates. That failure is
preserved and is not a passing gate.

Independent read-only finder and skeptic confirmed logical premise coverage.
Finder identified toolchain digest resampling; skeptic independently found that
and selection from a second live source read. The fixes retain the compared authenticated toolchain digest and
select interfaces from the exact captured, hash-checked byte buffer. Both
confirmed the fixes and exact accounting. Eleven external refusal/accounting
controls pass, including snapshots, held imports, incomplete/duplicate/changed
types, axiom records, mode/client substitution and collateral-entry changes.
Neither reviewer ran Lean/server/tests or wrote files. Their reviews and the
kernel evidence are separate artifacts.

Coverage uses ONLY the two exact executed receipt hashes, re-parses their sealed
probe logs, checks the same client bytes and exact original types, then updates
ten pending originals. The generator reads its immutable Git baseline so it
remains reproducible after the audit coverage file changes. A second invocation
after the root update generated all four accounting outputs byte-identically. All other 782
original rows and all 43 existing coverage entries are preserved. All 792
identities remain: 45 joint witnesses (previously 35), three target-failure joint,
45 intentional impossibility, 256 no-top-level-input, two V1 refutation/migration
and 441 ordinary pending (previously 451). Three private-identity gaps and all
nineteen signature-transport waits remain. No original statement, definition,
axiom, exclusion, premise or proof budget was changed; no sorry/native_decide.
Full original/inherited acceptance and H121 Source/world/native-frame adequacy
remain open, as does owner compiler success/G42.04.

P20's previously missing documentation reference is now actually resolved: its
in-tree target matches the owner's exact published SHA256 and repair commit
c9cf710a8459581006150a462b69ae8c4f0d13e0 is an ancestor. No P20 proof rerun is
claimed. The initial pre-adoption docs check instead reported a V09 handoff reference
to an absent external selected-heap witness. After adoption of a8f6849, the owner
documentation explicitly names its external H44 source; the final GLOBAL DOCS
GATE PASSES. That target was not materialized or proof-checked here. Both doc-only
tickets are closed, with no cross-chain edit, waiver or proof inference.

Raw paired proofs, accepted coverage delta, reviews and owner requests are under
/workspace/h62-audit-readonly-calls/effect-rules/; pins are in
`tests/h62/item2/audit-readonly-calls/effect-rules.sha256`. The committed checkers
and coverage generator reproduce the evidence with the admitted artifacts.
Receipt paths remain VM-specific; content verification is not independent SDK
source certification. Next: continue remaining joint witnesses/refutations and
live owner/type/source binding without treating these ten effect-algebra inputs
as full compiler totality or the full H121 producer. No goal completion or push.


### Primitive value and nonempty local transport inputs (2026-11-07)

Rebased the prior checkpoint onto master 65e69b6426a9a4fc3fb5541f41726a4bfefda5d0;
the proof-run head is e6a0ec767f081273fab6ebce82a53f8775414bb0. The two original
primitive interface files remain byte-identical to C6. The additive
`tests/h62/item2/audit-readonly-calls/PrimitiveTransportWitnesses.lean` supplies
inhabited inputs for all four PrimitiveValues statements and all four
PrimitiveLocals statements. Its bool/uint/int/bool locals contain true/9/-3/false;
the last index really reads false while the first reads true. Both local round
trips and both variable-read correspondences use these same inputs. The primitive
round trips use actual nondefault numeric values; default transport is applied to
Bool. Injectivity includes the concrete true/true image-equality premise jointly
with the original theorem application. A separate checked refutation rejects a
constant Bool translator. Eleven new audit theorems and eight input definitions;
no original declaration, definition, premise, exclusion, axiom or budget changed.

The SAME final client passed fresh isolated exact-C6 and current dependency
closures: 43/47 project modules, eight exact original raw kernel type hashes,
and eleven helper axiom sets containing only propext/Classical.choice/Quot.sound
(or no axioms). Frozen:315.859 seconds,1688174592 bytes peak aggregate RSS;
current:309.074 seconds,1623326720 bytes. Explicit -j1,LEAN_NUM_THREADS=1,
12GiB address cap,16GiB VM,no swap,4GiB reserve; Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613. Both include a passing bounded KeySort step. These are
independent model checks, NOT a timing comparison or release of the historical
Premises +80.254966536% STOP. No held import, cache fallback, full runtime pass,
SDK-library certification or whole-model definition equivalence is claimed.

The initial frozen run passed before the injectivity inputs were strengthened;
it is historical only. The strengthened per-file check passed in1.010 seconds.
Final frozen/current receipts are admitted by exact SHA256 before parsing, and
sources, toolchain, objects and actual query logs are rechecked. Eight external
controls pass for captured-interface substitution, imports/inventory, trust,
missing/duplicate/changed types, mode/client substitution, lost originals and
collateral baseline drift. A self-found copied receipt field still said ten;
it was corrected to derive the actual change count, with pre-fix metadata kept.
The accepted receipt and delta both report eight. Synthetic controls are not
Lean proofs. Independent read-only finder and skeptic confirmed the strengthened
logical inputs and negative control, with final accounting review recorded in
the exported handoff; neither ran Lean/server/tests or wrote files.

Coverage changes EXACTLY eight pending original statements, preserving every
other784 row and all53 prior entries: joint45→53 and pending441→433. All792
identities remain, including three private-identity gaps and all nineteen
H19/H60 statement-transport waits. Credit means inhabited inputs and original
applications, not ABI decoding, callee selection, compiler totality or Source/
world/native-frame adequacy. The full H121 producer and inherited queue remain
unfinished. Stage3 still waits on memory-reference-structs; H19/H60 transport
still waits on v10-storage-operations; historical proof-cleanup fb0defdc remains
UNVERIFIABLE. No new owner ticket or scope question, no push or goal completion.

Evidence: /workspace/h62-audit-readonly-calls/primitive-transport/; committed
pins: `tests/h62/item2/audit-readonly-calls/primitive-transport.sha256`.
`check_primitive_transport.py` regenerates proofs in fresh output directories;
`primitive_coverage.py` reproduces accounting from its immutable Git baseline and
admitted raw receipts. It requires the exported canonical prior ledger and raw
VM artifact paths; no off-VM independent acceptance is implied. Next independent
work: remaining433 original joint witnesses/refutations and precise input/type/
source/owner binding under all existing holds.


### Primitive initialization and authenticated dependency reuse (2026-11-07)

Fetched master f5038bc02bc52ea08f5a3cec7de292aef424e7c8 and rebased prior audit
checkpoints; proof-run head is f994997c163fa341adab6bb872f24dde7857c42c.
`tests/h62/item2/audit-readonly-calls/InitializationWitnesses.lean` imports
unchanged PrimitiveInitialization and instantiates zero_value,zero_values,
exhausted_nonempty,exhausted_empty. Explicit Env, Bool locals and Source state
observe horizon-one success, nonempty horizon-zero timeout, and empty horizon-zero
success. Mixed bool/uint/int returns use the same input/seed in every run. A
general pure-versus-timeout lemma and two concrete always-timeout refutations
guard successful initialization. Ten new helper theorems, five input definitions;
no original statement, definition, premise, exclusion, axiom or budget changed.

Both final modes passed:four exact original raw kernel types,ten permitted
helper axiom sets. Frozen:45 project nodes,43 reused and2 newly compiled modules,
39.504 seconds,793149440 bytes peak aggregate RSS. Current:50 nodes,47 reused
and3 newly compiled modules,34.237 seconds,792784896 bytes. The final client and
query compile separately in both modes. These are CHECKED DEPENDENCY REUSE gates,
not fresh full-closure rebuilds or timing comparisons. New dependencies compile
in isolated libraries; no arbitrary cache fallback or old-library LEAN_PATH.
The prior executed primitive pair is admitted by exact hashes; source/import/
object/compiler/log pins are verified before/after and copied objects/staged
sources checked. Historical Python tools changed by master are recovered ONLY
as exact hash-matched Git bytes at the admitted receipt's head. Current tools
stay untouched; missing/wrong objects or corrupted saved snapshots refuse
recovery. Read-only replay refuses absent snapshots. This authenticates saved
provenance, not execution of old tooling or SDK-library certification.

The initial check refused changed scan.py before compilation. Exact Git recovery
resolved that provenance mismatch. The next check compiled dependencies but
found an ambiguous Heap.empty in the new fixture; qualifying the Source heap
fixed it. The corrected per-file check passed in1.516 seconds. Those two failed
attempts remain saved, with no passing credit. Final frozen/current receipts are
separate and immutable. External controls cover actual temporary-Git recovery,
bad Git digests, absent/corrupt snapshots, forbidden artifact recovery, source/
object/destination substitution, unadmitted receipt bytes, held imports, changed/
missing/duplicate types, mode/client substitution and original-row loss. Intake
controls also keep lexical refusals separate from semantic credit. These are
external tooling checks, not Lean proofs. Independent read-only finder and
skeptic confirmed source logic, cache recovery and final accounting; neither
ran Lean/server/tests or wrote files.

Accounting changes exactly four original pending rows:joint53→57,pending433→429.
Every other788 original row and all61 prior coverage entries are retained. All792
identities, three private run_bind gaps and nineteen H19/H60 statement-transport
waits remain. Horizons are NOT gas/depth/fork resources; initializer refutations
are not negative controls for the public compiler. The historical Premises
+80.254966536% STOP remains; no unchanged held-workload run, before/after
rebaseline, runtime-pass label or full assignment completion.

Master now contains PublicCompilerTotal and its owner controls. Source-only
intake binds exact Git blobs and nine requested header spans. The lexical census
refused PublicCompilerTotal at an unmatched end; that file remains unbound,
and candidate headers do not establish namespace or kernel signatures. Frozen
census owner/kernel/witness defaults are removed from new producer rows; live
ownership and kernel binding remain explicitly unverified. This
refusal is recorded rather than hidden. Compiler-success source publication is
available; consumer kernel validation and complete negative controls remain
pending. Its stated ProgOk/Matches domain excludes external/self/library calls;
G42.04 library body/binding adequacy remains open. Owner P1 documentation says
gas/depth are not resources. Thus intake closes neither checkpoint3 nor our full
H121 Source/callee/native-frame producer; no original792 credit comes from text.

Artifacts: /workspace/h62-audit-readonly-calls/initialization/.
Committed pins: `tests/h62/item2/audit-readonly-calls/initialization.sha256`.
`initialization_coverage.py` reproduces its exact four-row delta from the immutable
Git baseline and admitted proof/cache chain. Raw ledgers and exact absolute VM
paths are required for replay; they are not independent off-VM acceptance.
Next:remaining429 original joint inputs/refutations and exact source/type/owner
binding, plus consumer validation of published compiler success under all holds.
No new scope question, owner ticket, push, goal reset or goal completion.


Final initialization acceptance:thirteen external controls pass; four accounting
outputs and the source-only compiler intake reproduce byte-for-byte. Skeptic's
unsupported inherited-owner finding is fixed by stripping all frozen owner,
kernel-name and witness/premise defaults from new producer rows. Both reviewers
confirm the fix. Actual bounded current KeySort passes (2.020 seconds), using
Lean4.24.0/Lake5.0.0-src+797c613, without a runtime-pass claim. No full repository
or producer compiler kernel gate is substituted by this prerequisite.


### SDK command surfaces for the published compiler producer (2026-11-07)

Fetched master f5038bc02bc52ea08f5a3cec7de292aef424e7c8; it is already an
ancestor of this branch. The legacy census remains unchanged. Its producer
refusal arose from mutual-block ends; equation-style theorem bodies also lack
its assumed := delimiter. No frozen792 headers, signatures, statuses or old
refusals are rewritten to make the new producer pass.

`tests/h62/item2/audit-readonly-calls/CommandSurface.lean` uses SDK syntax parsing
in a safe helper command with an initialized Lean environment. It never imports,
elaborates or executes inventoried project commands. It traverses declaration
nodes and mutual command children, not proof/quotation subtrees, and separates
parser declSig ranges from ordinary/equation bodies. Namespace/section variables,
UTF-8 byte ranges, early exit, parser errors and mismatched scopes remain explicit.
No unsafe initializer API, new theorem, axiom, sorry or budget change is used in
the final source; no production module or generated root imports this tool.

The live capture parsed four exact Git files at d38e44f7816bf01c23ec023d178488e07ebcb21b:
PublicCompilerTotal28 theorem surfaces, its Controls19, P1RevertBridge6 and
Evm.Compiler16, total69. All nine requested source headers are unique parser
candidates. These are surface names/ranges/context, NOT elaborated signatures,
private kernel identities, live ownership, compiler correctness or Source/native
adequacy. Legacy lexical refusal is retained as historical evidence; SDK parsing
refines only the surface facet. No original witness credit comes from parsing.

Seven live controls cover mutual/equation headers and scoped variables; an
available-Lean import with a run_cmd file marker that must never execute; a
separate nonexistent project import that must not load; proof-command quotations;
an unexecuted custom macro producing a parser refusal; early #exit preserving an
unscanned-tail refusal; and mismatched namespace closure. The marker/import
fixtures are separate so a missing import cannot mask an execution regression.
Five external unit controls cover polluted SDK variables, precompile helper
mutation/staging failure, UTF-8 and invalid ranges, partial/elaboration-claim
refusal and explicit guards. Live guards also pass under Python optimization.

Finder and skeptic found SDK override, transitive-tool sealing and helper-reread
gaps. Fixes remove all dynamic Python project imports, strip Lean/Elan overrides,
set private library/canonical SDK roots, check actual prefix before/after and
stage one authenticated helper buffer with pre-child seals. Both reviewers
confirm fixes and final saved evidence without executing Lean/server/tests or
writing files. SDK/stdlib contents remain external tool inputs, not certified
source. Initial unsupported-notation/prototype/kernel-refusal and fixture traces
are saved separately; none is promoted to final acceptance.

Final normal and optimized captures passed in3.525/3.527 seconds with
658362368/656969728 bytes peak aggregate RSS. These are two live reproducibility
checks, not a before/after speed baseline. Producer surfaces, nine requested
candidates and original-ledger preservation reproduce byte-identically; fixture
marker paths/ranges are deliberately run-specific. All792 original identities
and root coverage remain byte-bound and unchanged:57joint,3target-failure joint,
45intentional impossibility,256no-top-level-input,2V1refutation/migration and
429ordinary pending, including three private gaps. Nineteen transports, full
H121 producer, compiler consumer kernel validation, inherited queues and full
acceptance remain open. Historical Premises +80.254966536% STOP is unchanged;
no held producer proof was loaded/rerun and no RUNTIME_GATE_PASS is claimed.

Artifacts: /workspace/h62-audit-readonly-calls/command-surface/; committed pins
`tests/h62/item2/audit-readonly-calls/command-surface.sha256`. The deterministic
`command_surface.py` runs only live parser capture, not saved-receipt promotion.
Next independent work: actual compiler consumer kernel/type binding and remaining
original inputs under the holds. No scope question, owner ticket, push or goal
reset/completion.


### Public compiler consumer kernel/type and outcome checks (2026-11-07)

Fetched master5414256fdf7b78e8debe5e571c7af06ee55a5563 and rebased prior audit
work; checked tree2652005dc61266e7386b6e696d3a72f19e6bac5a. The producer's187-module
current closure including Controls excludes WorldCalls.Premises. An attempted
standard cache seed was stopped by the memory-reserve guard: its default tmpdir
was RAM-backed. The task-owned partial extraction and unused downloaded archive
were removed after recording checksum/failure evidence. No cache provisioning
pass is claimed. Existing cache plus necessary current-source rebuilds were used.

`tests/h62/item2/audit-readonly-calls/CompilerOutcomeWitnesses.lean` instantiates
PublicCompilerTotal on a nonempty Boolean-declaration program and a supported
bare-revert program. Both have actual intrinsic-source outcomes and share the
same explicit fresh typed state, machine, simulation and word bound. The Boolean
source local is true. joint_agreement retains those inputs with the FULL fixed
Compilation.Agrees relation. General lemmas derive target success from actual
source success and no payment, and target revert from actual source revert.
The no-payment fact follows the existing domain's quiet theorem. The public
compiler thus actually accepts and executes successfully at this supported
input; reject-all and always-revert behavior are refuted there. A second actual
compiled run reverts. No target-outcome/OracleAgrees premise is assumed.
Fourteen new audit theorems,five fixture definitions,no original statement,
definition,premise,exclusion,axiom or budget changed; no sorry/native_decide.

The repository per-file dependency check built the producer closure; its first
whole gate failed only because new generic helper applications left L/frame/
base/state implicit. Making those exact inputs explicit fixed the leaf. Final
per-file PASS1.514s. The final metadata/consumer kernel probe PASS18.608s with
1023172608 bytes peak aggregate RSS. It checks the same client source, nine
imported producer names/modules/closed types and exact direct source selections
against the prior SDK ranges. All14consumer and9producer axiom sets are within
propext/Classical.choice/Quot.sound(or subsets). The published totality theorem
and its inhabited owner controls therefore have current consumer kernel/type
validation under ordinary Lake cached-dependency assumptions. Nine of the69
producer surfaces have these explicit links; the other60 are not individually
type/location-inventoried by this probe. No private fallback or ownership claim.

The driver seals the transitive H62 Python tool tree, source/export/config
buffers, SDK/toolchain, complete187-source import graph and actual query log.
Original coverage is pinned before/after. Lake traces and374object-path snapshots
are post-query observations, NOT source-to-object fidelity or loader-byte
attestation. This is current-tree cached-import checking, not an independently
fresh dependency proof or SDK-library certification. Five external controls
refuse missing/duplicate identities, wrong modules/names/types, mismatched direct
locations, UTF-8 position errors and unexpected/missing/duplicate axioms. They
are tooling controls, distinct from kernel proofs. Read-only finder/skeptic
reviews confirm the final source/evidence with no findings; neither runs
Lean/server/tests or writes files.

This advances checkpoint3 only on the owner-stated intrinsic ProgOk/Matches
compiler domain. Agrees supplies its existing typed state/stack relation; these
outcome controls do not separately expose a target Boolean memory cell. Failure
is the basic machine's data-free revert, not returndata bytes. The word bound
is not gas/depth/fork; the basic machine does not supply those resources. This
is NOT resolved Solidity.Source/callee body adequacy, physical P1/native frames,
external/self/library call coverage or G42.04 body binding. Our full H121 producer
remains unfinished. No existing exclusion or observation is weakened to claim
those properties.

All792 original identities,429ordinary pending,three private gaps and nineteen
transports remain unchanged,with zero original witness credit from these new
post-base compiler consumers. Other checkpoints and inherited queues/full
acceptance remain open. Historical Premises +80.254966536% STOP is retained;
no unchanged held proof was rerun,no before/after rebaseline or RUNTIME_GATE_PASS.
Evidence: /workspace/h62-audit-readonly-calls/compiler-consumer/; committed pins
`tests/h62/item2/audit-readonly-calls/compiler-consumer.sha256`. Next:remaining
original joint inputs and full RO Source/callee/native-frame producer under all
holds. No new scope question, owner ticket, push or goal reset/completion.


### Nonempty primitive field/read joint inputs (2026-11-07)

Fetched and inspected master a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e; rebased the
audit branch before this increment. The separate CheckedMul reuse change does
not provide these clients. No production file, interface, dependent definition,
axiom, exclusion or proof budget changed.

`tests/h62/item2/audit-readonly-calls/PrimitiveReadWitnesses.lean` uses two actual
declared Bool fields, nonempty Bool locals, one Source store and one intrinsic
store. The head is written true; the tail reads its actual default false. The
Fields constructor supplies declaration lookup, exact types, persistence and
nonconstant metadata together. Rel is proved from the actual reads. The SAME
inputs instantiate PrimitiveFields.read_value/total/unique/select and
PrimitiveReads.read_of_read/read_head/target_read_head/target_expression. Tail
selection and a negative head-only target control preserve distinct values.
unique_joint checks the two simultaneous concrete relation premises; its
reflexive equality conclusion is premise-satisfiability only. No Source program
well-formedness/deployment, expression body or call/native-frame adequacy follows.

The unchanged isolated checker supplies exact frozen/current type exports and
axiom checks. A thin selection driver authenticates every admitted parent source
and import, including modules outside the consumer overlap, before the existing
cache verifier runs. Only the actual overlap is loaded; no arbitrary object
fallback or held WorldCalls.Premises import. Frozen closure:52 modules,42 reused;
current closure:57 modules,46 reused. Remaining nodes and the same fixture are
compiled from captured bytes. This is authenticated executed-object reuse plus
fresh extension checking, not a claim that all dependencies were freshly built.

Final frozen PASS53.328s/800108544 bytes peak aggregate RSS; current
PASS52.86s/801472512 bytes. Eight original raw kernel types match on each tree;
all eleven audit axiom sets use standard propext/Classical.choice/Quot.sound
or subsets. Repository per-file gate PASS95.17s,59 dependency jobs; actual
Lean4.24.0 and Lake5.0.0-src+797c613, serial bounded -j1. KeySort passes separately.
These are validation costs, not a before/after speed comparison or rebaseline.
Historical Premises +80.254966536% STOP remains unchanged; no RUNTIME_GATE_PASS.

Eight tooling controls pass: exact client inventory, cache-overlap authentication,
source/pin substitution refusal, held import refusal, original identity retention,
missing/duplicate/wrong type/client refusal and recredit/baseline refusal.
Finder and skeptic caught a stale pre-initialization census, split admission
hash/read and missing initial collector hash check; all three were fixed before
acceptance. Both reviewed the final saved evidence without executing Lean,
servers, tests or writes and found no remaining defect. Initial fixture
elaboration and tooling-test failures remain in off-git evidence.

The explicit committed admission pair and full verifier authorize exactly eight
new coverage entries: joint witnesses57→65; ordinary pending429→421. All792
identities and original fields remain;784 unrelated rows are unchanged. Other
counts stay256 no-top-level-input,45 intentional impossibility,3 target-failure
joint and2 frozen-v1 refutation/migration. The three private identity gaps remain
pending. No definition-equivalence claim is made by raw type equality or separate
frozen/current executions. Source/root_expression/caller-frame interfaces and
our full H121 RO Source/callee/native-frame producer remain open, as do nineteen
H19/H60 transports, G42.04 body binding, inherited queues and full acceptance.

Evidence: /workspace/h62-audit-readonly-calls/primitive-reads/; proof pair under
validated/, acceptance under accepted/. Committed pins:
`tests/h62/item2/audit-readonly-calls/primitive-reads.sha256`. No new scope question
or owner ticket. Next independent work: remaining original joint inputs and full
RO execution/frame producer under the retained holds.


### Nineteen Source version extracts received (2026-11-07)

Fetched master and found the requested Source producer extraction already
published, then rebased onto coordinator master
6fbbf971caeb4c9946fbd20aaa0b25b3f1fb1f9f while preserving owned work.
The integrated producer is scripts/h62/item2/audit-v10-storage/transport_pairs.py
at32c853a6396aad1f4f79ad1e4cdddc4aef9c6488. It supplies19 exact lexical pairs
(11 balance projections, one balance domain, seven typing parameters) plus
three removed private identities. It explicitly supplies zero transport proofs.

The consumer executes that producer and its direct lexical helper from retained
buffers verified equal to their exact Git HEAD blobs. Captured C6/current Lean
source buffers are independently Git-checked and reparsed from those same
buffers. The saved producer packet, executed tools, sources and output buffers
are sealed through completion. All22 cases bind to their exact original file,
source name, signature, variable context and visibility in the retained792-row
census. Historical kernel names/type hashes are reference-only; no current
Lean elaboration, Source-definition equivalence or kernel transport is inferred.

All792 original rows and root coverage remain unchanged:65 joint,3 target-failure
joint,45 intentional impossibility,256 no-top-level-input,2 frozen-v1
refutation/migration and421 ordinary pending. Three private gaps remain explicit
and are never mapped to replacement public helpers. Exact source delivery is now
received; the V10 wait is narrowed to H57/semantic/kernel transports and actual
consumer proof references. Live ownership is not established by source intake.
The old recorded observation commit exists on this VM; that fact alone does not
recover historical proof/test artifacts or clear any provenance hold. Historical
proof-cleanup fb0defdc remains UNVERIFIABLE.

Seven controls pass, including missing/duplicate identities, signature/context
drift, private alias/partition substitution and forbidden H57/kernel/proof credit.
The retained-loader control uses different disk bytes and verifies that only the
Git-verified captured buffers execute; Git mismatch refuses. Finder/skeptic
found three provenance gaps (executed tool vs Git, saved-packet final seal, and
second Source read); all were fixed, then both reviewed final source/evidence
with no remaining findings and no execution or writes.

Bounded final intake PASS1.01s/29773824 bytes peak aggregate RSS. This is a text
and tooling gate, not a Lean proof or performance rebaseline. No Lean source,
statement, definition, exclusion, axiom or budget changed; no held Lean workload
was run. Historical Premises +80.254966536% STOP and runtime/whole-goal gates
remain open. Our full H121 RO G42.02 Source/callee execution, selected
compiler/world binding and physical frame remain OUR unfinished producer for
memory-reference-structs; this intake is not that deliverable. G42.04 body
binding, inherited queues and the421 ordinary inputs also remain open.

Evidence: /workspace/h62-audit-readonly-calls/transport-intake/; committed pins
`tests/h62/item2/audit-readonly-calls/transport-intake.sha256`. Owner-ticket
historical requests are retained with explicit current routing/owned-producer
fields. No new scope question, owner ping, push or goal change. Next independent
work: remaining original joint inputs and the full owned RO execution/frame
producer, while preserving all holds.


The repository-wide documentation gate fails on an existing master citation at
line348 of docs/feature-work/h62-4-generic-v08.md: it backticks the name of an
explicitly untracked historical file. Exact bytes match master; the cited file
is absent. Owner request RO-DOC-GENERIC-V08-UNTRACKED supplies an off-git
formatting-only patch removing those backticks, retaining the filename and
historical claim. No other lane file was edited and no passing docs gate is
claimed. Source intake and all792-row preservation pass independently.


### Read/discard continuation witnesses and Source type drift (2026-11-07)

Fetched and checked coordinator master6fbbf971caeb4c9946fbd20aaa0b25b3f1fb1f9f;
no newer equivalent client was present. The existing primitive fixture is
extended additively with an explicit global record, a target Bool local and
a following assignment. Prior eleven fixture definitions and eleven proof
bodies remain byte-identical after the namespace opener, as checked against
abcf292e41410f0ba4eb379dd554c4269f1ec735. The import grows to ReadStatement;
this adds checking work, not an optimization or proof-speed rebaseline.

The same source/target storage and typed local inputs exercise actual Source
expressions, Source statements and the intrinsic read/discard block. Following
code writes a=false while retaining the old true local; a following revert
remains a revert. No global/callee adequacy follows from constructing the global
record: it supplies only the auxiliary primitive expression inputs. The two
credited target contracts use intrinsic state/root/evaluation/continuation only.

Strict cache reuse refused because master changed Hash/CollisionBound proof
source. No cache check was relaxed. Final frozen53-module and current58-module
closures were freshly compiled from captured bytes, serially within inherited
12GiB/no-swap/4GiB-reserve bounds. All nineteen helper proofs check separately
on both trees and expose only standard propext/Classical.choice/Quot.sound
axioms or subsets. Frozen PASS350.477s, current PASS341.091s; per-file repository
gate PASS102.158s. Actual Lean4.24.0/Lake5.0.0-src+797c613 and bounded KeySort
PASS are recorded. These durations are validation costs, not comparable
before/after performance measurements. Historical Premises +80.254966536% STOP
is unchanged; the held workload was not rerun and no RUNTIME_GATE_PASS follows.

The first full-six current gate compiled its source/witness/probe, then FAILED
the exact original kernel-type comparison. Four Source-facing statements have
unchanged lexical signatures/context but different elaborated types after
evalE/execS gained default RuntimePlan arguments: PrimitiveReads.source_expression,
PrimitiveReads.root_expression, ReadStatement.source_run and
ReadStatement.simulation. Their C6 joint applications compile; current
applications concern changed types. This is a type-fidelity blocker, not
a contradiction or a proof that the original hypotheses are impossible.
The four remain ordinary pending with zero bridge/current-fidelity credit.
Exactly one ESCALATE record per affected declaration is retained in off-git
read-statements/type-drift/ESCALATIONS.txt. Owner ticket RO-READ-PLAN-TRANSPORT
requests H57 legacy/planned pairs and exact consumer/semantic transports; no
existing interface or Source definition was edited, no premise/exclusion/budget
was changed, and no equivalence is inferred from successful concrete runs.

Only target_run and target_then match their exact frozen types on both trees.
Paired receipt acceptance credits exactly those two: joint65→67 and ordinary
pending421→419. All792 identities and original fields remain;790 unrelated rows
are unchanged, including the four drift cases and three private identity gaps.
Other counts remain3target-failure joint,45intentional impossibility,
256no-top-level-input and2frozen-v1 refutation/migration. Earlier eight-case
receipts bind the earlier committed fixture bytes; they are historical records,
not verification of the extended file. New paired runs recheck all old helpers.

The shared collector now accepts a restricted explicit proof mapping and
explanatory metadata configuration. Nine legacy controls pass, including exact
output equality with the historical eight-case collector; three new controls
check complete19-proof inventory, old-body preservation, exact two-case mapping,
fresh verification and held-import refusal. Finder and skeptic independently
reviewed the final source/evidence and confirmed the two credits/four retained
blockers without using Lean, tests, builds, a server or writes.

Artifacts: /workspace/h62-audit-readonly-calls/read-statements/; committed pins
`tests/h62/item2/audit-readonly-calls/read-statements.sha256`. Existing global
documentation failure RO-DOC-GENERIC-V08-UNTRACKED remains pending owner adoption;
no passing repository docs/full gate is claimed. Full H121 G42.02 Source/callee
execution, selected compiler/world binding and physical frame remain OUR
unfinished producer for memory-reference-structs. G42.04 body binding, nineteen
H19/H60 transports, inherited queues, historical proof-cleanup artifact recovery
and full acceptance remain open. No new scope question or goal change.


### Exact loaded-original type census (2026-11-07)

Fetched/rebased masterdcf33632c2e88dd2161a0f1b212954ea84647f5f, including its
private-path policy. No newer equivalent census was present. The query reuses
only the admitted current read-statement proof closure:58 project object hashes,
captured/current source hashes, tool/log/input pins and the leaf proof object
are checked before/after. It imports only that unheld closure and Lean metadata;
no Premises load, proof rerun, cache fallback or new dependency build occurs.
Standard SDK/import-loader trust remains; object hashes are not independent
loader-byte or source-to-object attestation.

Exactly49 of the original792 declarations belong to loaded modules. The actual
Lean query observes every original kernel name/module/kind, exports closed raw
types, and obtains direct declaration selection ranges. Private names use
Lean's constructor and are checked against original identities, with no public
alias or basename fallback. All49 are present and directly source-bound,
including seven private declarations;743 unloaded originals remain explicit.
Kernel ranges must match the exact lexical declaration name span in captured
source, not another occurrence of the same token. Current signature, variable
context and visibility are retained separately. A raw type match does not prove
unchanged dependency definitions, execution adequacy or live ownership.

The final bounded metadata gate passes12.568s/805502976 bytes peak aggregate RSS:
38 raw types match frozen exports and11 differ. Four Source drifts were already
reported and StaticJournal.balance_storage is already an H19 case. Six newly
reported drifts are SourceCallBoundary.call_zero/call_depth/call_static_value
and SourceTypedCall.eval_external/external_captured/external_capture_failure.
Their visible headers/context remain equal while elaborated types differ.
RO-READ-PLAN-TRANSPORT now contains ten Source-related declarations; the known
H19 overlap stays with its existing ticket. One new ESCALATE record per new
declaration is retained off git, without repeating the prior four records.

call_depth and call_static_value retain historical C6 joint-witness status.
That original result is preserved, but it is not current-version fidelity.
The new ledger records these axes separately and gives zero new credit. All792
original rows, root coverage and historical classifications are unchanged:
67joint,3target-failure joint,45intentional impossibility,256no-input,
2frozen-v1 refutation/migration and419ordinary pending, including three private
identity gaps. No unloaded/missing/private/range refusal is dropped or inferred
to be feasible, impossible, owned or semantically equivalent.

Six controls pass, including missing/duplicate identities, private missing-name
retention, wrong identity/range, same-token-at-wrong-location and type drift
without credit. Independent finder/skeptic found missing final log sealing and
insufficient declaration-location binding; both were fixed. The initial query
also needed explicit Lean.Name and proper private-name construction. Both
reviewers confirmed final source/evidence without execution or writes and found
no remaining issue. No new Lean declarations, premises, axioms or budgets.

Actual wrapper versions remain Lean4.24.0/Lake5.0.0-src+797c613. Prior bounded
KeySort PASS remains recorded in read-statements/evidence/keysort.json; this
metadata gate is not a new runtime pass or proof-speed comparison. Historical
Premises +80.254966536% STOP is unchanged. Full owned H121 Source/callee execution,
compiler/world binding and physical frames, nineteen H19/H60 transports,
G42.04 body binding, inherited queues and all final acceptance remain open.
The existing generic-v08 documentation citation failure remains owner-pending.

Evidence: /workspace/h62-audit-readonly-calls/loaded-original-types/; committed
pins `tests/h62/item2/audit-readonly-calls/loaded-original-types.sha256`. No scope
question, push or goal change. Next independent work: remaining original joint
inputs, broader exact bindings and the owned full RO execution/frame producer.
