# H62 item 2: read-only-call empty-statement audit

Status: **blocked, not complete**. The frozen all-statements witness gate is
impossible for two mapped dispatch cuts. No frozen statement, hypothesis,
exclusion, observation, proof budget, interface file or library root was edited.

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
| 1. Frozen inventory and owners | Partial: 129 mapped files, 792 named theorems, frozen bytes checked, source signatures and lexical variable context saved. Full elaborated signatures, 33 private kernel names and remaining premise classifications are pending. |
| 2. Simultaneous witnesses | Blocked: four concrete simultaneous clients; two hypothesis conjunctions refuted; 786 entries still pending. |
| 3. Success/totality and negative controls | Blocked: Source success/failure/timeout and both-pipeline gas refusal checked; reject-all and nonempty target-revert controls checked. General compiler success and executable gas/fork adequacy remain unproved. |
| 4. Fidelity census and uncovered owners | Partial: every named source declaration accounted exactly once, six outcomes bound to signature hashes; remaining entries retain pending status and owners. Full all-witness acceptance and final integration gates have not passed. |

The census intentionally includes controls and helpers with no explicit
hypotheses. It makes no silent interface-theorem exclusion. Source headers and
lexical `variable` commands are not elaborated binder exports; open/notation
resolution and private-name mangling remain explicit limits.

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

All three audit files passed separate bounded Lean checks. Their printed axiom
sets contain only `propext`, `Classical.choice`, and `Quot.sound`; no added
`axiom`, `sorry`, `native_decide`, trust shortcut, or raised heartbeat limit.
Failed intermediate attempts are retained separately and are not certificates.
No H55 producer proof was duplicated. P1 producer ownership remains V12 and
H55-G49 where applicable, even though these consumer files belong to V13.

## Owner escalations

Each affected original declaration appears once below. The structured tickets
are saved in `tests/h62/item2/audit-readonly-calls/owner-tickets.json` for the
local coordinator to retrieve. No relay script exists in this VM; delivery to
external producer sessions is pending coordinator retrieval. No existing-file
write request or permission is implied by these questions.

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
| census generator with `--coverage tests/h62/item2/audit-readonly-calls/coverage.json` | Pass: 129 modules, 792 declarations, statuses 1 joint witness / 3 target-failure joint witnesses / 2 refutations / 786 pending. |
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

Remaining obligations: 786 witness entries; full elaborated signature/private
kernel-name export; remaining global-vs-input classifications; owner decisions
on the two impossible cuts; independently fixed compiler success/totality,
P10 observation, gas/fork boundary; full repository final gate and all-statement
acceptance. Save/relay these typed blockers, preserve the exact original goal,
VM and branch, and resume only under authorized owner scope. This handoff is
not completion of the four-checkpoint assignment or the 8–10 hour work queue.
