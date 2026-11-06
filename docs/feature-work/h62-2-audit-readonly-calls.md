# H62 item 2: read-only-call empty-statement audit

Status: **blocked by mandatory performance stop; original goal unfinished**. The current frozen-file comparison exceeded the 10% stop threshold; no new proof work or remeasurement follows. Semantic/proof progress below is retained as a reviewable checkpoint, not completion. H69 assigns the two
unreachable frozen dispatch cuts to RO as **pending RO v2**: a reachable
versioned interface, explicit migration and consumer re-proofs. Their frozen
refutations remain evidence; they are neither erased nor counted as witnesses.
The separate compiler-success theorem is a pending deliverable of V13
(`v12-v17/v13-abi-world`) for G42, with V15/P10 observation dependencies. It
must prove success for that owner's compiler on the stated supported inputs;
no frozen interface statement changes. Both previous scope questions are resolved; the semantic continuation adds Q-CALLBACK-INTENT below. H70 supplies the exact H69 rule: checked joint-impossibility proofs are the audit result for intentional negative controls/separation/refutations; ordinary interfaces still need joint witnesses. RO, V13 and V15 have accepted the ticket relays. Proof and inspection work is now paused by the performance stop; only read-only checkpoint preparation continues.
No frozen statement, hypothesis, exclusion, observation, proof budget,
interface file or library root was edited.

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
| 1. Frozen inventory and owners | Exact type/identity census complete: 129 files, 792 elaborated theorem types, all 33 private names resolved, owners retained. Semantic global-vs-input feasibility continues with the witness queue. |
| 2. Simultaneous witnesses | Partial: 27 joint clients; 42 checked intentional impossibility results under H69; 256 statements with no top-level input hypotheses; two pending RO v2; three pending callback-owner intent; 462 other entries pending. |
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
| census generator with `--coverage tests/h62/item2/audit-readonly-calls/coverage.json` | Pass: 129 modules, 792 declarations, with elaborated census: with current semantic stage: 24 joint / 3 target-failure joint / 42 intentional impossibility / 256 no-top-level-input / 2 RO v2 / 3 owner intent / 462 pending. |
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

Remaining obligations: 462 ordinary semantic/witness entries, three callback-intent decisions and two RO-v2 migrations; remaining semantic global-vs-input feasibility classifications; RO v2 publication/migration and consumer re-proofs for the two cuts; independently fixed compiler success/totality,
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

The earlier H69/H70 questions were resolved. The current semantic continuation adds Q-CALLBACK-INTENT; owner items also remain pending RO v2 and V13 compiler success with V15/P10 fixed outcomes. After the performance stop is resolved, resume remaining ordinary entries without modifying frozen interfaces.

Review correction: syntactic binder-free metadata never removes a witness obligation. Full exported records, including binder arrays, are reparsed from their successful hash-bound Lean log at census ingestion. Mutation tests reject binder-array tampering and separately exercise private kernel identity. At the pre-semantic checkpoint, all 339 syntactically binder-free rows remained pending. Their current accounting is derived only from the separately verified reducing/axiom inspection, not the empty syntactic binder array.

Continuation checking-repeatability capsule: five samples of the identical unchanged Premises file measured median 1.149105 s before and 1.093362 s after, delta -4.850972%. No >10% slowdown stop was triggered. This is not a whole-build migration performance claim.

## Semantic continuation after published-master preflight

Before selecting the new work item, git fetch origin master completed and history/code were inspected at 5f7bb1441566aaad64a34436904afc61de762fd2. The frozen read-only surface has no upstream changes and the audit tooling is not published there, so the duplicate-work rebase condition does not apply. A second fetch/code inspection preceded the hidden-input witness batch. No existing producer implementation was redone.

The generated reducing query checks the original exact types/names and uses forallTelescopeReducing plus collectAxioms under unchanged budgets. It passed all 339 selected declarations in 110.737 s with peak aggregate RSS 1,123,995,648 bytes. Every collected proof axiom set is a subset of propext, Classical.choice and Quot.sound. The original raw Expr remains pinned to the exact 792-type export. Canonical receipt/query/log/toolchain verification is repeated at semantic ingestion. Binder, axiom and inspection fields cannot be modified independently of the checked log.

The reviewed partition of these 339 is 256 rigid logical results with no top-level input hypotheses (211 Eq, 38 And, seven Exists), 42 deliberate Not/Ne control/separation/refutation results with one refused proposition leading to False, and 41 initially unresolved predicate/alias cases. The 256 label is deliberately narrow: it does not certify compiler success, nested semantic guards, representation feasibility or actual admitted executions. The 42 original checked proofs are H69 results, not newly created proof aliases or positive witnesses; their exact identities and frozen type/signature hashes are pinned in semantic-policy.json. Unreviewed negatives remain pending.

HiddenClients.lean then supplies eleven ordinary joint clients for four Effect predicates, six SameStorage predicates and receiver injectivity, using populated existing source states and actual addresses. It also proves three callback-choice conjunctions impossible. All fourteen helpers passed in 4.012 s, peak RSS 915,017,728 bytes, with only standard proof axioms. The three new callback controls remain pending owner intent rather than being silently declared intentional negatives.

Current exact accounting: 792 = 27 joint clients + 42 checked intentional impossibility results + 256 no-top-level-input statements + two pending RO v2 + three pending callback-owner intent + 462 other pending entries. Global record inhabitance is never substituted for per-input feasibility. Five original census, twelve exact-export and seven semantic mutation/acceptance tests pass. Tests reject altered semantic binder/axiom arrays, wrong type pins, nonstandard axiom policies, unreviewed negative acceptance and premature discharge of named predicates.

### Q-CALLBACK-INTENT — waiting RO owner decision

The three fixed-strategy CallbackHistories declarations below have globally impossible callback-choice premises, despite their inhabited global certificates. The checked subset refutations establish impossibility of each full admitted-child conjunction. V13 owns these controls; RO owns the underlying source-history interface. Requests and exact paths are in the scoped owner-tickets.json. The coordinator confirms routing this decision to RO: wait {lane: solidity-compiler10-20261028/readonly-external, item: Q-CALLBACK-INTENT}. The owner decision remains pending; this routing does not classify the controls or discharge their obligations.

Question: are these intentional no-callback separation controls, eligible for the checked-impossibility result under H69, or ordinary producer obligations that must await reachable versions/fixtures? Options: classify as intentional separation and accept the checked impossibility, never as a positive witness; or retain ordinary pending status until owners supply reachable versions/fixtures. No recommendation or frozen-interface edit is implied.

ESCALATE: Solidity.Backend.WorldCalls.ClosedSourceControls.closed_callbacks — V13/RO; HiddenClients.closed_children_joint_impossible and continuation-semantic/evidence/hidden-clients.log prove the fixed answer strategy cannot satisfy the callback choice. Options: owner confirms intentional H69 no-callback separation; or owner supplies a reachable version/fixture and consumers re-prove.
ESCALATE: Solidity.Backend.WorldCalls.UnknownSourceControls.children — V13/RO; HiddenClients.unknown_children_joint_impossible and continuation-semantic/evidence/hidden-clients.log prove its fixed answer strategy cannot satisfy the callback choice. Options: owner confirms intentional H69 no-callback separation; or owner supplies a reachable version/fixture and consumers re-prove.
ESCALATE: Solidity.Backend.WorldCalls.UnknownRevertControls.children — V13/RO; HiddenClients.revert_children_joint_impossible and continuation-semantic/evidence/hidden-clients.log prove its credit/answer strategy cannot satisfy the callback choice. Options: owner confirms intentional H69 no-callback separation; or owner supplies a reachable version/fixture and consumers re-prove.

Semantic continuation bulk evidence is off Git under /workspace/h62-audit-readonly-calls/continuation-semantic/evidence/. Its handoff/report supersede earlier status summaries while retaining earlier sealed artifacts as historical. Full run-lean.sh, remaining ordinary witness work, RO v2 publication/migration, V13 separate compiler success with V15/P10 fixed outcomes and final all-statement acceptance remain unfinished.

## Mandatory performance stop

The semantic-continuation comparison failed with median 1.042592 s before and 1.879323 s after, delta +80.254967% (threshold +10%). The benchmark process exited 1 with SLOWDOWN_STOP. New proof work and further measurements stopped immediately. The source hash, command, Lean/Lake binaries and recorded resource flags match; no cause is established and no code-regression claim is made. No threshold override or repeat-to-green is requested.

Evidence: /workspace/h62-audit-readonly-calls/continuation-semantic/evidence/timing-before-samples.json, timing-after-samples.json, timing-after.json and performance-stop-context.json. The shell pipeline stopped before structural checks; those read-only non-Lean checks may be completed solely to prepare this blocked checkpoint. Full run-lean.sh and final witness acceptance remain pending. There are still 462 ordinary entries that may be worked after the performance stop is resolved; this report does not claim they all require missing producers. Prior RO-v2/compiler-success dependencies and Q-CALLBACK-INTENT remain separately pending.

Coordinator routing follow-up: Q-CALLBACK-INTENT is an RO-owner wait, not an unanswered human scope question. Published master was fetched and inspected at 0b2a648b32335f35ff323ff468f75907e926fc13; its new coordination tooling supplies no audit proofs or performance-stop resolution. The mandatory timing stop remains binding; no Lean, benchmark or new proof work was resumed. The 462 ordinary entries remain queued independently of producer waits.

Routing follow-up reviews: independent read-only inventory_finder and inventory_skeptic found no issues. Both confirmed the exact RO wait, unresolved classification, unchanged frozen originals, binding timing stop and 462 independently queued entries; neither ran Lean, benchmarks or writes.
