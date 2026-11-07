# Resumed audit — 2026-11-07

The coordinator explicitly resumed this lane after merging its retirement head. Origin/master was fetched and verified at `5da4771e63a4278ed53932ac39a032e3d7aea6ed`; it contains retirement head `4e34f3c4a0190c7085a7fbae4094dcadad645b42`. The existing lane was merged onto that baseline without resetting history. The retirement notice below is historical and is superseded by this resume instruction. No goal was created, reset or marked complete; the get/pause APIs remain unavailable.

All four full-assignment checkpoints remain partial. Original frozen base remains `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`; historical statement obligations remain binding while current source validation uses the new baseline. The old evidence, retirement exports and original prompt/scope files remain preserved.

## Completed resume milestone

1. [resume_inventory.py](../../scripts/h62/item2/audit-yul/resume_inventory.py) authenticates the exact original census and frozen blobs, checks current selected files against the new commit, holds the writer lock, and retains all 21,385 original declaration records unchanged. Current selection is 1,995 files: 1,898 same blobs, 62 changed and 35 additions. It lists 21,948 lexical candidates (19,757 named theorems, 1,921 examples, 270 structures). Original obligations cannot disappear when scope changes; ambiguous navigation is explicitly unaccepted. Lexical/file matches confer no new proof credit. Determinism and corruption/wrong-baseline/held-lock controls pass.
2. [AllocationWitnesses.lean](../../tests/h62/item2/audit-yul/AllocationWitnesses.lean) covers every one of Allocation's twelve original theorem declarations exactly once: nine ordinary simultaneous witnesses, including all implicit arities, inhabited Fin 1 indices, injectivity equalities and the caller-ordering premise; three H69 interval-separation certificates. The independent reducing existential target and literal refutation-type/universe checks pass. This is allocation arithmetic, not runtime storage/memory preservation.
3. [ReservedRefutation.lean](../../tests/h62/item2/audit-yul/ReservedRefutation.lean) certifies `Solidity.Yul.slotnum_not_reserved` under H69: assuming SLOTNUM membership contradicts the pinned reservation table. Its full type/universes are unchanged. ReservedNames differs from the original only in the existing count theorem's proof. This says nothing about executable builtin support or fork/gas adequacy; the count statement remains separately classified.
4. [record_resume.py](../../scripts/h62/item2/audit-yul/record_resume.py) binds each of the thirteen results to the authenticated original declaration/signature, unchanged source definitions, current helper/import hashes, successful bounded gates and unique fidelity markers. It regenerates and compares the complete inventory under the writer lock, fingerprints that inventory and its generator, and checks compiled imports against the baseline Git blobs. It rejects stale proof hashes, failed gates, duplicate helper entries and tampered inventory baselines. The complete generated registry and raw evidence remain off git; [resume-witnesses.json](../../tests/h62/item2/audit-yul/resume-witnesses.json) contains the compact registration records.

Fresh serial Lean checks passed with zero warnings for both final helpers. Allocation closure: 0.807 s for the unchanged interface and 1.409 s for the audit helper. Reservation closure: 2.018 s Builtins, 0.404 s ReservedNames and 2.016 s audit. Commands, source hashes, peaks/reserve budgets and outputs are in `/workspace/h62-audit-yul-evidence/resume-20261107/`. Checks used explicit `-j1`, `LEAN_NUM_THREADS=1`, heap 11000 MiB, sampled resident/reserve/no-swap guards and the existing 16-GiB VM cap. No budget or maxHeartbeats was raised. Actual Lean is 4.24.0 release `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Lake 5.0.0-src+797c613. This audit does not claim the separately pinned v4.35 migration completed.

The nine ordinary fixtures have no axioms; separation wrappers inherit only approved axioms (Allocation prints propext/Quot.sound; reservation prints propext). All thirteen run through explicit axiom guards. No sorry, new axiom, native_decide, trust bypass, original interface/body edit, root/map or axiom-pin edit was introduced by this milestone. No refactor of existing proof checking occurred; comparable full-build timing delta remains unavailable. No RUNTIME_GATE_PASS is claimed. Historical KeySort passed with 377 taclets, 131 read-bearing, table covers 131, OK; it was not rerun for this milestone.

## Accounting and continuation

For the ORIGINAL frozen corpus only, combined results now count 14 ordinary witnesses, 15 intentional refutations, 513 statements without exposed hypotheses, and 18,688 uncovered named theorems: total 19,230. Four of the former fifty pending negative candidates are certified; 46 remain. For the CURRENT baseline, this milestone freshly validates only nine ordinary witnesses and four intentional refutations; historical results are not silently promoted. The inventory snapshot is intentionally taken before these new proofs and reports zero credited current proofs; the separate source-bound registry records the thirteen later results.

Still open: remaining simultaneous witnesses; 46 negative intentionality/certificate reviews; full exact type/private/example/owner reconciliation; public/Source/G24/native success, observable failure/gas/fork coverage; Bridge root/dependency support; registration by the coordinator; final affected/full run-lean.sh validation and controlled timing. The Source/Horizon 518.910-second result still waits for gate-VM validation against the 300-second timing stop. Original budgets remain; no unchanged STOP was rerun. Original complete work/backfill queues are in the preserved handoff files. No push, publication or master merge was performed by this worker.

Static registration, fragments, doc paths and diff checks pass. `node scripts/check-layers.mjs` exits 1: 901 core modules, zero elaborator/parser reachability, but twelve new core-to-non-core edges against 95 pinned allowances. All graph/checker/allowlist inputs are identical to the fetched baseline. This is a failing gate, not waived or counted as a pass; exact paths and a coordinator ticket are preserved in the off-git evidence and [resume-owner-ticket.md](../../tests/h62/item2/audit-yul/resume-owner-ticket.md). No allowlist/exclusion was changed.

Finder and skeptic reviewed inventory, joint telescopes, separation intentionality and registry read-only without Lean or edits. Findings about locking and ambiguous joins were fixed; final review/evidence details are in the off-git resume handoff. Four bounded work items have now been completed; hand off this same VM/branch/unfinished original goal to the coordinator for a fresh thread, without creating a replacement goal. Final head and authenticated exports are recorded off git.

---

# H82 retirement — stopped, assignment incomplete

This worker has stopped implementation under the explicit human retirement instruction. Handoff to `solidity-inline-assembly5-20261031/vy2-physical`; successor integrates the final isolated branch head. No push is authorized by available H71 evidence. No original statement changed and no new Lean work was performed for retirement.

[Original assignment](../../tests/h62/item2/audit-yul/handoff/original-assignment.txt), [original queue](../../tests/h62/item2/audit-yul/handoff/original-work-backfill-queue.md), [scope descriptor](../../tests/h62/item2/audit-yul/handoff/scope-manifest.json), [capture provenance](../../tests/h62/item2/audit-yul/handoff/provenance.json) and [all remaining obligations](../../tests/h62/item2/audit-yul/handoff/remaining-queue.md) are committed. The complete enumerated scope, cumulative patch/bundle, portable evidence and checksums are in `/workspace/h62-audit-yul-artifacts/retirement/` and its authenticated archive. Bulk evidence remains off git.

The human requested the existing goal PAUSED. The exposed goal API supports only complete/blocked, so no PAUSED transition can be issued; neither substitute was called. No automatic implementation continuation is authorized. All four checkpoints remain partial; Source/Horizon gate-VM timing validation remains a wait. Final head, clean status, artifact hashes and read-only retirement reviews are recorded in the off-git retirement handoff. Earlier continuation language below is superseded by this stopped retirement notice.

---

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

### Y04 Source-to-graph path identity audit

`tests/h62/item2/audit-yul/SourceGraphEndpoints.lean` instantiates the public StorageOps path endpoint for arbitrary finite word-key chains in the existing checked persistent nested-mapping family. The graph key encoding and recursive location equality are proved; the slot image is derived from those laws, rather than assumed. A joint witness constructs a two-key declaration through the existing intrinsic Source syntax and derives its ordinary Source path. A negative control rejects certifying that nested path as the untouched root slot. This is symbolic path/slot metadata correspondence at the existing root0 placement, not Source liveness, graph-value adequacy, numeric-store agreement, compiler selection or ReachedEndpoint. No new witness is counted against the frozen theorem census.

The attempted production import raised NestedMappingLayout checking from median 0.40 seconds to 0.83 seconds. The performance STOP was honored: the exact production source was restored, with a restoration check of 0.40 seconds; the slowed version was not rerun unchanged. The checked prototype is isolated in the authorized additive audit scope. Production integration needs an isolated module boundary, requested through coordinator question VY2-Y04-MODULE. No production producer readiness or full runtime pass is claimed. Independent read-only finder/skeptic found no defects; kernel, axiom exports, raw failed attempts and timing evidence are retained at `/workspace/vy2-evidence/y04-path-endpoint/`.

The current NestedMappingControls execution fixture fails against the available cache at its migrated FailureExecution cursor field. That failed check is retained; Source/Horizon is not rebuilt unchanged. The path audit avoids that execution fixture, so no checked execution adequacy is inferred from stale fixture artifacts.

### Routed Raw contract intake

The VY1 handoff at 45773c1cb85088579dbf48ddfe91ae34d1ad6c40 was fetched read-only and authenticated: packet SHA256, all three Git blobs at producer source 239f71cd3d547c01c0d751f9053c6442c918d0fc and all twenty exact signature hashes match. Sixteen signatures match the live checkout text. RawTypedScope lacks project_close, drop_clean, drop_world and close_captured; that producer branch was not merged. This authentication is not an integration or physical-adapter gate.

`tests/h62/item2/audit-yul/RawContractIntake.lean` consumes already-live RawFrame laws to prove arbitrary world-observer preservation after an actual completed Tier-A run, the completed materialized snapshot identity and skip completion for every supplied raw frame. It does not infer coherence of arbitrary dirty frames, Source/world-changing execution, physical layout or compiler adequacy. RawFrame and RawCoherent checked after refreshing stale objects; their live source bytes match the packet. The current RawTypedScope dependency build stops at LocalU8Statement because the cached Source.evalE lacks its current plan parameter. Raw failure retained; no H16 edit or unchanged Source/Horizon rerun.

The exact V17 synthetic-reference repair a2b8558db548751e414f71d1d3c7889f64cc0ee8 was reused, preserving owner file bytes and all six passing fixture controls. Independent read-only finder/skeptic found no defects in the Raw consumer. Evidence is at `/workspace/vy2-evidence/raw-contract-intake/`; all previous physical/reached-state, production promotion, timing and final-validation limitations remain open. No shared interface is frozen or changed here.


### Supplied-witness receipt experiment stopped and restored

A reusable audit_joint_existing command was prototyped in DefaultWitnesses to check a supplied theorem against the existing complete existential telescope, universe parameters and axiom boundary. Positive and refusal controls compiled, but the matched per-file timing gate stopped it: tool median 0.97→1.07 seconds (+10.3%). Removing redundant receipt serialization did not resolve the stop (median 1.12 seconds, +15.5%). Both source files were restored byte-for-byte and the original tool cache was rebuilt; no new command or control is retained. Raw proof checks, both failed timing comparisons and the rejected patch remain at /workspace/vy2-evidence/views-witness-receipt/.

The prior byte_payload_joint theorem and its separate exact-telescope check remain valid at a483e32bc22970f0693e5807a93480cf48900645. Its single-statement evidence is not promoted into the original corpus totals: the authenticated bulk census needed by record_resume.py is absent locally. Retrieval of the original h69-census/census.json (SHA256 1a6f4f9352a0004aa3cfcc67e8e3abd313e5c83864dfe436880aeeb0cb2adcde) remains required. This experiment changes no production statement, proof, budget, trust inventory, acceptance criterion or coverage count. The wider independent witness/backfill queue and all final obligations remain open.


### Public word-memory joint-premise batch

Eight closed witnesses now cover every public WordMemory theorem telescope, including the full read congruence hypotheses, 32-byte prefix bound, division bound and final-byte index. They use an ordinary existing ByteView at unaligned base 129 and a nonempty 32-byte window; division uses k=16 and the byte witness uses index31. The existing general DefaultWitnessControls module hosts these audit declarations, with no new per-shape module or memory carrier. The small word-witnesses.json binds all eight source/proof pairs to frozen c6f550e281a7e5affa9a99bc2cdaed556dec00e4 signature hashes. The private division_byte helper is outside this public-interface batch.

All eight full existential telescopes and universe lists check against the imported theorems. Six witnesses use no axioms; the two containing a Roadmap.Word numeral use propext. A negative witness lacking readBE_congr's second view and agreement hypothesis is rejected. The first placement in Fixtures exceeded the 10% stop (0.54→0.63 seconds, +16.7%); that placement and its cache were restored exactly. Moving the audits to the existing general controls module gives matched median 2.02→2.12 seconds (+5.0%), below the stop. Original controls are byte-identical apart from one import and the additive block. Raw failures, restoration, final checks and timings are retained at /workspace/vy2-evidence/views-word-family-witnesses/.

These are local joint-inhabitance results, not per-input feasibility, global census acceptance, physical adequacy or reached execution. Global counts remain unchanged while the authenticated census is missing. The existing Y04 bridge obligation, producer waits, migration/full acceptance obligations and previous STOPs remain open.


### Primitive byte-operation joint-premise batch

Seven added witnesses in the existing general audit-controls module cover the eight public Bytes laws, reusing word_window_joint for mcopy_self. Live copy/store indices select byte31 of a nonempty 32-byte interval. The other-address and outside-region witnesses retain their dependent inequalities for the same addresses and lengths; source and destination are ordinary existing ByteViews. The small primitive-byte-witnesses.json records all eight source/proof pairs and original c6f550e281a7e5affa9a99bc2cdaed556dec00e4 signature hashes. All frozen signatures match, and all existing audit declarations are byte-identical outside the added block.

All eight full existential telescopes and universe lists pass serial Lean 4.24 checks. Six mapped witnesses use no axioms; the two word-valued store witnesses use only propext. A negative check omitting the copy outside-region premise is rejected. Three matched control-module samples give median 1.90→1.91 seconds (+0.5%), below the stop. Raw checks and audit source are retained at /workspace/vy2-evidence/views-primitive-byte-witnesses/. This is local joint inhabitance, not memory-range validity for arbitrary inputs, actual overlap execution, compiler admission, physical adequacy or global corpus acceptance. No original theorem, representation, budget, axiom boundary or exclusion was changed; all wider obligations and prior STOPs remain open.
