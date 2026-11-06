# H62 item 2: audit-theories — blocked handoff

This is a reviewable partial audit, not completion of the frozen assignment.
The strict acceptance command exits 1. No RUNTIME_GATE_PASS is claimed.

## Frozen scope and continuation identity

- Batch/owner: solidity-h62-2-20261106/audit-theories.
- Branch: codex/solidity-h62-2-20261106/audit-theories.
- Base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
- Actual checkout: /workspace/audit-theories; original checkout at
  /workspace/solidity-lean was preserved at 6cf853aea0417155aca29ddb91f1767d3f3a3cc4.
- VM/environment: ccarenv_b64_Y2NhcmVudl8yZmZkMjNiNDVmNTg4MTkxOTI3MDI3NGVhZWM4N2E1ZA.
- Continue the existing persistent goal; never create/reset a replacement.
  Supplied original rendered-prompt digest:
  1939e0477546471c70cd0f97b2c74438439569f0c02197327dbfa6fa38724929.
  get_goal was unavailable; coordinator explicitly confirmed this optional
  inspection absence is not a blocker. No goal ID was invented.
- Remote fetch recovered the required base. Both remote ancestry and assigned
  branch ancestry were verified; commands/results are in setup.json off Git.
- Writes are confined to the two assigned audit subtrees and this document.
  All frozen Theory sources, generated roots/maps, axiom pins and toolchain
  remain unchanged. No owner coordination is interpreted as permission to edit
  producer files. No H55 implementation, merge, pre-gate, PR, or push was made.

## Census and exact accounting

The module map contains 25 files. Comment-masked source extraction finds 500
explicit theorem/lemma declarations (497 public, 3 private). Lean's environment
contains 1,486 theorem constants in those modules. Every explicit declaration
matches exactly one typed record, including inherited binders, binder types,
logical-hypothesis flags, fully qualified names and raw elaborated type AST.
The 986 additional generated constants are retained as pending candidates;
they have not been silently excluded from the assignment.

| Explicit declaration disposition | Count |
|---|---:|
| Simultaneous witness checked | 6 |
| Empty elaborated input telescope | 18 |
| Intentionally empty inputs; certificate checked, acceptance blocked | 3 |
| Public inputs not yet witnessed | 470 |
| Private declarations retained, witness pending | 3 |
| Total | 500 |

uncovered.json contains 1,462 unique pending/blocked records: 470 public,
3 private, 3 impossible-input boundaries and 986 generated candidates. It gives
names, source/module locations, documented producer routing and unresolved live
owners. verified-census.json retains every full typed record and source header.
Neither inhabited global structures nor individual premise witnesses are
counted as simultaneous feasibility. Logical-vs-data binders are typed; the
remaining per-statement global-vs-per-input interpretation is still pending.

Historical producer routing covers Mutability (VS2), Progress (VS3), CallerModel
(VC2), Reachable (VC3): see semantics-extensions.md lines 68–79, 442 and
calculus-modes.md lines 35–44, 135. Current live confirmation remains pending.
The nine Typed/Segs/Bridge files have no confirmed proving owner. The exact-file
migrate-theory overlay is recorded separately and explicitly does not transfer
live ownership. Coordinator ticket T-OWNERS requests routing, not file edits.

## Checked additive declarations

All names below are in namespace H62.AuditTheories. The six witness helpers are
in [ProgressWitnesses](../../tests/h62/item2/audit-theories/ProgressWitnesses.lean)
and [ScopeControls](../../tests/h62/item2/audit-theories/ScopeControls.lean):

- tuple_stmt_progress_joint_witness and stmt_progress_joint_witness pack every
  input and all original hypotheses, plus a concrete successful tuple result.
- expr_progress_joint_witness, items_progress_joint_witness,
  body_progress_joint_witness and callsOKX_none_joint_witness pack every input
  and hypothesis of their respective unchanged statements.
- tuple_returns_both_pipelines, tuple_excludes_always_error, tuple_fuel_boundary,
  timeout_ends_without_return establish actual source success, reject every
  always-error source result, and distinguish fuel exhaustion from success.
- call_free_global_does_not_supply_call and empty_system_has_no_entry expose
  the global-premise/per-input distinction. emptyBody and emptySystem are the
  two fixture definitions. In particular A=False cannot witness call_progress's
  additional admitted-call hypothesis.
- no_plain_tuple_input, no_tuple_locals_input and no_finite_array_path_input
  certify the three impossible joint input telescopes. The third is in
  [FiniteBoundary](../../tests/h62/item2/audit-theories/FiniteBoundary.lean).

There are 15 new proved theorems, 2 fixture definitions and 1 census metaprogram.
Final axiom reports use only propext, Classical.choice and Quot.sound, or subsets;
no new custom axiom, sorry, native_decide, trust option or increased heartbeat
budget was added. Earlier failed elaboration attempts remain in evidence, but
only matching successful artifact/log/source provenance is accepted.

## Owner tickets and required decisions

Q-NEGATIVE-INPUTS was asked during work and has no recorded answer. These are
intentional negative structural boundaries, not evidence that the original
classification theorems are defective. Their literal all-input witness
requirement is contradictory; their frozen statements remain intact.

ESCALATE: Solidity.Theory.Progress.Val.not_tuple — Tuple.lean:40 assumes a plain tuple Val and concludes False; H62.AuditTheories.no_plain_tuple_input proves no such input exists. Options: accept the checked impossibility certificate as this negative boundary's audit disposition while preserving its statement; retain the literal witness criterion and its typed blocker.
ESCALATE: Solidity.Theory.Progress.Controls.no_tuple_local — Controls.lean:141 assumes locals headed by a tuple and concludes False; H62.AuditTheories.no_tuple_locals_input proves its input telescope empty. Options: accept its checked impossibility disposition without editing the statement; retain the literal witness criterion and blocker.
ESCALATE: Solidity.Ty.Finite.not_array — Leaves.lean:305 requires a finite shape plus a direct path to a dynamic array and concludes False; H62.AuditTheories.no_finite_array_path_input refutes that conjunction. Options: accept its checked impossibility disposition while retaining the theorem; retain the literal witness criterion and blocker.

T-PUBLIC-LINK routes the compiler obligation to the coordinator/area producer,
with H55-G49 consulted for shared final-contract linkage. Source Ends permits
revert/panic/timeout and CoreEnds classifies every core result. The new source
success controls do not prove compiler admission or reject-all compiler
exclusion for a frozen public compiler contract. Program.lean:38 and
Outcome.lean:32–34 explicitly state gas is unmodelled. legacy/viaIR is a source
pipeline parameter, not an EVM fork. Required compiler success, observable
failure-byte/gas/fork linkage remains unproved. Options for the producer ticket:
supply an existing frozen adapter and exact owning paths for additive audit
consumption; assign the missing relation proof to its existing owner and retain
this dependency blocker. No interface repair or new premise is authorized.

## Validation and resource evidence

Off-Git evidence directory: /workspace/h62-audit-theories-evidence.
The final external handoff adds exact committed head, patch paths and checksums.
Bulk JSON and compiled artifacts are not committed; generators are committed.

Actual runtime: Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake 5.0.0-src+797c613. This audit retains the frozen toolchain; the coordinator's
official v4.35.0 archive pin is scoped to migration lanes, and was not substituted
here. All five coordinator input checksums were verified.

One heavy Lean process at a time, LEAN_NUM_THREADS=1, explicit -j1,
--tstack=131072, 12 GiB virtual-address cap, no host swap, at least 4 GiB
container/host available reserve, 300-second module timeout. The writer lock
was acquired before writes/checks. No systemd-run or heartbeat increase.
The initial 118 dependency checks took 771.790s, peak sampled process RSS
1,714,769,920 bytes. KeySort passed in 2.008s at 256,262,144 bytes. Runtime labels
are not proofs and no full runtime gate pass is claimed.

| Command / gate | Outcome and decisive evidence |
|---|---|
| python3 -m unittest discover -s scripts/h62/item2/audit-theories -p test_*.py -v | 5 pass; census-tests-final.log |
| serial_check.py --lean /workspace/.setup/tools/lean-4.24.0-linux/bin/lean --out /workspace/h62-audit-theories-evidence/serial <audit targets> | All 4 final helpers passed individually; matching provenance/axiom logs checked by verifier. No full-build equivalence claimed. |
| verify_census.py --evidence /workspace/h62-audit-theories-evidence | Exit 0, 500 exact explicit matches; generated candidates retained. verify-census-final.log |
| Same verifier with --require-full | Exit 1: FULL_ACCEPTANCE_BLOCKED, 1,462 pending/blocked candidates plus unlinked compiler obligations. |
| node scripts/check-layers.mjs | Exit 0: 857 core modules, none reach elaborator or checked parser adapters. |
| bash scripts/coord-tools/register.sh --check | Exit 0; generated roots unchanged. |
| bash scripts/coord-tools/fragments.sh --check | Exit 0; generated maps/pins unchanged. |
| bash scripts/check-doc-paths.sh | Exit 1: pre-existing off-scope missing MathlibTest/SplitIfs reference in after-roadmap-va1.md. No authorized fix made. |
| ./run-lean.sh and complete affected/full acceptance/performance gates | Pending; mandatory heavy-check stop, incomplete witnesses and producer linkage. |

[ElaboratedCensus](../../tests/h62/item2/audit-theories/ElaboratedCensus.lean)
uses the unchanged imported environment. The producer validates absolute off-Git
output paths. Forced replay is byte-identical: 54,772,963 bytes, SHA256
71ac6a3e7efc088d7d2f4bad700f887bf2e5146052e2fe8e2aa6ab811a9d1a63.
The verifier checks producer/source/artifact/log provenance, external receipt
and both replay byte hashes, frozen-map-derived rescanning, module identities
and unique accounting. The receipt and scanner tests are external bookkeeping,
not a Lean proof of census correctness or compiler behavior.

Census check: 25.876s before, 33.515s replay (+29.52%) at the same producer and
transitive dependency fingerprint. ScopeControls warning cleanup: 1.406s to
2.011s (+43.03%). CPU scheduling/OS page caches were not controlled; these do not
establish code-caused regression or a passing matching-cache performance gate.
Further heavy checks stopped at the threshold crossing; no retry hid it.

ESCALATE: action serial_check.py::ElaboratedCensus timing gate — 25.876s to 33.515s, +29.52%, exceeds the frozen 10% stop threshold; see timing.json and both driver logs. Options: coordinator investigates a reproducible matching-cache measurement under unchanged resource/proof budgets before resumption; retain the heavy-check stop and continue only non-Lean handoff/backfill.

## Independent reviews and fixes

Independent finder and skeptic worked read-only, without Lean/server/build
jobs. Confirmed fixes: frozen-map scope guard, comment/string handling,
unsupported-prefix fail-closed control, structure-style where/let headers,
cache artifact/log hashes and retained history, absolute off-Git path guard,
forced side-effectful census replay, producer/output provenance binding,
frozen-source rescanning, module identity and unique accounting. Both checked
six witness shapes against exact frozen premises, identified the three empty
input boundaries, and confirmed source/fuel/pipeline labels do not claim
compiler/gas/fork correctness. Both report no residual findings for this
blocked handoff. Their results are saved in reviews.json; this is not a review
approval of the unfinished assignment.

## Committed continuation handoff

Request a coordinator-managed fresh thread after these reviewed work items:
source/typed census, joint-input witnesses, negative/success controls, and
provenance/acceptance tooling. Use this original VM, branch, evidence and
existing goal. Do not self-launch a replacement, reset the goal, merge, push,
pre-gate or publish. The goal remains unfinished.

Next work: resolve the heavy-check stop and Q-NEGATIVE-INPUTS; confirm proving owners for nine files and
current live routing for all 25; classify all generated candidates;
finish remaining joint witnesses without assuming empty catalogues or global
structures suffice; consume owner-provided compiler success and failure/gas/fork
adapters; run all required affected/final gates and independent reviews. Keep
all blockers until discharged. Deferred registration suggestions are supplied
in tests/h62/item2/audit-theories/registration-fragment.txt; no registration was
applied. The census metaprogram must remain outside dependency-free core roots.
