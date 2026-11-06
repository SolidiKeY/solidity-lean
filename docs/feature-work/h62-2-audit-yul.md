# H62 item 2 — audit-yul

Status: **partial; original goal remains unfinished**. H69 resolves the former
Q-REFUTATION-01 scope blocker. All four frozen checkpoints, ownership rules,
proof/resource budgets and final gates remain binding. No original interface,
premise, exclusion, observation, root or axiom pin changed. No push, merge, PR,
deployment, pre-gate or H55 work occurred.

Repository: `/workspace/solidity-lean`; branch
`codex/solidity-h62-2-20261106/audit-yul`; frozen base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The prior clean `work` branch remains
preserved. Base ancestry was verified before branch creation and again on resume.
Final full committed head and exported artifact hashes are in the off-Git handoff.

## H69/H70

[H69.md](../../tests/h62/item2/audit-yul/H69.md) records the human decision
verbatim. Checked impossibility is an audit result only for explicitly classified
intentional negatives/refutations/separations. Ordinary statements still need a
simultaneous witness. No statement change is authorized or performed.

The eleven historical negative candidates are all certified and classified by
name, intentional reason and proof in
[witnesses.json](../../tests/h62/item2/audit-yul/witnesses.json). Their historical
escalation lines remain once each in
[owner-tickets.md](../../tests/h62/item2/audit-yul/owner-tickets.md), marked resolved.
H70 relays reached VY1/VY2/VY3; VY5/V07 went to the current Claude coordinator.
The receipt path is host-only, not a VM file. No relay installation or further
human question is pending for these historical tickets.

## Four-checkpoint accounting

| Checkpoint | State | Actual result and remaining work |
|---|---|---|
| 1 — signatures and owners | Partial | 1,960 selected frozen files; 19,230 named theorems, 1,887 anonymous examples and 268 structures. All blobs and module map match the base. 2,017 source declarations now have unique typed matches, including 100 complete structure-field inventories. Full type/name/owner reconciliation remains open. |
| 2 — simultaneous hypotheses | Partial | Five ordinary joint witnesses and eleven H69 intentional-refutation results. 513 named theorems have no exposed hypotheses and are recorded separately. 18,701 named theorems remain uncovered. |
| 3 — meaningful success | Partial | Actual all-word literal-assignment compiler result, source/scalar success, arbitrary-certificate REVERT rejection, reject-all rejection and source-horizon refusal. Full public/Source/G24/native failure, gas and fork closure remain unfinished. |
| 4 — fidelity census | Partial | Frozen-blob verification, source-parser provenance, reducing kernel telescope/fields, exact eleven-refutation fidelity, successful proof-source snapshots and negative stale-evidence controls pass. Full corpus, all witnesses and final gates remain unfinished. |

These categories are disjoint. The arithmetic is
19,230 = 18,701 uncovered + 513 no-exposed-hypothesis + 11 intentional refutations
+ 5 ordinary joint witnesses. Closed statements are **not** joint-witness counts
or evidence of meaningful per-input success. Global record inhabitation does not
establish actual supported-program feasibility. Owner labels remain explicit area
assignments pending full live-producer reconciliation; no ownership is taken.

The source census has 21,083 parser-confirmed spans and 302 source candidates
(268 structures, 32 examples, two named WordLogic statements with custom notation).
Kernel metadata is separate from source spans: fields for 100 structures are
now recorded without promoting their lexical headers to full source signatures.
The 6,365 typed records from 268 already source-checked modules include generated
kernel auxiliaries; only unique (module, source-name, kind) source matches enter
primary accounting. No synthetic utility declaration enters the source census.
Fifty additional fully exposed negative conclusions remain in a separate
intentionality-review list; they have not been automatically accepted under H69.

## Checked proofs

[Refutations.lean](../../tests/h62/item2/audit-yul/Refutations.lean) preserves the
ten original telescopes exactly and applies the unchanged negative theorems.
They cover empty declaration/function/external contexts, pure-word/MLOAD
separation, global/write and global/local separation, and fixed/dynamic storage
separation. These are intentional refusals, not weaker success statements.

[ImpossiblePremises.lean](../../tests/h62/item2/audit-yul/ImpossiblePremises.lean)
retains the exact resource-premise bundle and refutes its joint existence through
the unchanged ResourceContractLaw1 dependency. It has no axioms. This is an audit
of the negative statement; it is not an actual P8a producer or resource-model fix.

[RefutationFidelity.lean](../../tests/h62/item2/audit-yul/RefutationFidelity.lean)
checks ten literal elaborated type/level-parameter equalities and the original
SourceRealization resource statement's type against its proof dependency up to
alpha/definitional equality. All eleven comparisons pass after the unchanged
SourceRealization import is checked.

[Success.lean](../../tests/h62/item2/audit-yul/Success.lean) retains the prior
expression and statement endpoint joint witnesses and the generic composition
witness. The latter jointly supplies toy Stages, full PublicBoundary and
TablesLinked; it is global toy inhabitation, not actual assembly admission.
The visitor returns exactly the tested literal-assignment certificate for every
256-bit word, with actual source/scalar completion and arbitrary caller tails.
Its source-fuel boundary is not native gas; Scalar has no fork/gas parameter.

Two further ordinary frozen statements, `Solidity.Yul.pow_halve` and
`Solidity.Yul.powBits_correct`, have complete closed existential witnesses in
[DefaultWitnessControls.lean](../../tests/h62/item2/audit-yul/DefaultWitnessControls.lean).
The second includes the real proof-valued exponent bound. The generated values,
original type fingerprint, source hash, tool hash and passing gate are snapshotted
off Git. Synthetic universe/hidden-premise/empty-input controls are never counted.

[DefaultWitnesses.lean](../../tests/h62/item2/audit-yul/DefaultWitnesses.lean)
constructs all exposed binders from the exact imported theorem type, preserving
universe parameters. Head reduction exposes lets/aliases. An independent
`forallTelescopeReducing` construction fixes the complete existential target and
binder count. Terms must be closed; normal `addAndCompile` kernel checking and
the axiom whitelist precede any covered record. Search failure is uncovered.
A reducible decision must actually be true before its proof is constructed.
No `native_decide`, sorry, axiom, unsafe proof acceptance or raised heartbeat
budget is used. Read-only IO utilities create no proof declarations.

The negative controls caught a hidden-premise risk and a false `mkDecideProof`
expected-type hint candidate before rollout. The kernel rejected the invalid
candidate; its failed attempt remains in evidence. Head/shape/arity checks and
explicit decision reduction now close those gaps. The final data/proof-hypothesis,
universe, let/alias positive and impossible-input negative controls all pass.

## Validation, resources and timing

Actual toolchain remains the frozen audit pin: Lean 4.24.0, release commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
No migration cut-over or v4.24 per-master cache restoration occurred. The separate
migration pin is not applied outside that authorized scope. Five coordinator
input SHA256 values passed verification during setup.

All checks use the writer lock and one heavy Lean process at a time,
LEAN_NUM_THREADS=1, explicit -j1, --tstack=131072 and -M=11000. The VM has a hard
16 GiB cgroup limit. The at-most-12-GiB resident budget and four-GiB available
reserve are sampled stop guards every 0.2 seconds, not a hard 12-GiB cgroup.
Swap configuration/usage is checked during each run. No systemd-run is used.

The prior audit runner incorrectly also charged virtual reservations to the
resident budget with RLIMIT_AS. Correcting that accounting did not increase the
Lean heap or resident budget. The unchanged SourceRealization import now passes:
Source/Horizon 518.910 s (6.937 GiB sampled peak RSS, 13.800 GiB peak virtual;
11.090 GiB assigned resident budget), HorizonDeploy 11.473 s, Session 2.825 s,
and SourceRealization 1.008 s. No swap/resource stop occurred. The old 305.158 s
std::bad_alloc attempt stays in historical evidence. This is not a valid passing
before/after timing pair, and no full-build timing delta is claimed. Source/Horizon
exceeds 300 s on this worker; gate-VM time-budget validation remains pending and
no original-file performance refactor is authorized or attempted.

Actual KeySort prerequisite passed: 377 taclets, 131 read-bearing, table covers
131; OK. This external conformance check is distinct from Lean proof checking.
The typed reader completed 6,365 declarations with zero errors and no unexpected
axioms. H69 certificates use only existing standard axioms where reported;
new sorry/axiom/native_decide/heartbeat overrides are zero. The exact fidelity
gate reports `H69_FROZEN_TYPE_FIDELITY_PASS: 11 exact elaborated telescopes`.

The registry updater binds the latest passing proof and generator source hashes,
not historical append-log rows. Acceptance checks ordered six-record snapshots,
type fingerprints, binder/value counts and universe parameters. Three negative
provenance tests reject a stale tool hash, failed tool gate and duplicated record
without editing any proof or original interface.

Full affected/final validation, `./run-lean.sh`, all remaining ordinary witnesses
and native failure/gas/fork obligations are pending. No RUNTIME_GATE_PASS or full
completion is claimed.

## Reproduction and evidence

Canonical current census: `/workspace/h62-audit-yul-evidence/h69-census/census.json`.
Kernel data: `/workspace/h62-audit-yul-evidence/h69-kernel/types-v2.jsonl`.
The old first-checkpoint outputs remain historical. Bulk data stays off Git (H44);
only deterministic tools, small registries and additive audit modules are committed.

```
flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 scripts/h62/item2/audit-yul/record_h69.py --output /workspace/h62-audit-yul-evidence/h69-registry
flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 scripts/h62/item2/audit-yul/census.py --parsed /workspace/h62-audit-yul-evidence/reproduced-complete/parser.jsonl --witnesses tests/h62/item2/audit-yul/witnesses.json --kernel /workspace/h62-audit-yul-evidence/h69-kernel/types-v2.jsonl --output /workspace/h62-audit-yul-evidence/h69-census
flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock python3 scripts/h62/item2/audit-yul/acceptance.py /workspace/h62-audit-yul-evidence/h69-census/census.json --output /workspace/h62-audit-yul-evidence/h69-acceptance
```

Each Lean gate's full executable/arguments, source hash, exit, wall time, resident
budget, sampled RSS/virtual peaks and log path are in its `commands.jsonl` under
h69-refutations-final, h69-fidelity, h69-default-checked, h69-kernel-v2-check and
h69-source-gate. Dedicated uncovered and pending-negative lists are under
h69-acceptance. Earlier failures remain visible; they are not passing gates.

## Reviews and continuation

Independent read-only finder and skeptic used no Lean server and made no fixes.
They confirmed exact refutation telescopes, no statement weakening, complete
reducing existential construction, universe preservation, closed-term checks,
correct disjoint accounting and absence of synthetic coverage. Their findings
about hidden hypotheses, false decision hints, source/tool provenance and sampled
resource claims were fixed and tested. Final reports are saved off Git.

This checkpoint completes four bounded work items: H69 refutation certification,
typed census/field extraction, ordinary joint-construction controls and two real
witnesses, and original SourceRealization import recovery. Hand off to the
coordinator at the requested 3–5-item fresh-thread boundary, preserving this exact
VM/branch and original existing goal; do not create/reset a goal or self-launch a
replacement. All four original checkpoints remain partial.

Next work: expand source-checked kernel coverage beyond the 268 queried modules;
review the fifty additional negative conclusions individually; apply the checked
joint constructor in bounded batches to ordinary statements; add missing concrete
per-input fixtures; finish supported-program/native failure/gas/fork results and
all final gates. The current isolated resolver supports core and quoted audit
module paths; Bridge package-root/dependency handling still requires a scoped
tooling extension before Bridge can be claimed covered. Keep all producer files
read-only and coordinate any exact-file change through the current coordinator.
