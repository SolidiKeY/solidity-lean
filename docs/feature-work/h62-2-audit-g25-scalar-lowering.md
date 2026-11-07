# H62 item 2: frozen G25 scalar-lowering statement audit

Batch `solidity-h62-2-20261106`, lane
`solidity-h62-2-20261106/audit-g25-scalar-lowering`, repository
`/workspace/solidity-lean`, branch
`codex/solidity-h62-2-20261106/audit-g25-scalar-lowering`, frozen base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.

**RETIRED / STOPPED by explicit human H82 instruction.** C1/C2/C3 are
complete and reviewed; C4 is partial. No automatic implementation continuation
is authorized. Successor: `solidity-compiler10-20261028/memory-reference-structs`.
The original launcher goal is not complete. PAUSED cannot be set through the
exposed tool, which accepts only complete/blocked; neither substitute was called.

## Authorization, scope and provenance

The coordinator resolved Q-TOOLCHAIN-01: Lean 4.35 applies **only** to batch
`solidity-h62-6`; this audit stays on master's Lean 4.24.0. No 4.35 installation,
overlay or cache is used after that clarification. Earlier 4.35 import failures
are historical, superseded attempts, not active audit blockers. The earlier
question and migration tickets are resolved for this lane.

Actual Lean: `4.24.0`, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Actual Lake: `5.0.0-src+797c613` (Lean 4.24.0). Bounded KeySort passes.
No `get_goal` tool is exposed; coordinator explicitly confirmed that optional
inspection absence is not a blocker. No goal was created or reset.

The checkout started clean on `work` at
`6cf853aea0417155aca29ddb91f1767d3f3a3cc4`. Fetching `origin master` established
that the exact assigned base is an ancestor of published
`821e3e8f4c7a5ac3a51dc5cba8be813bb173e310`; the assigned branch was created
at that base without resetting/discarding work. Coordinator inputs match their
supplied SHA256 manifest. Both G25 and G31 remain V09-owned in that snapshot.
The G31 preparation rows are inside the assigned G25 area map and are included.
H55 files and ownership remain untouched.

Only new/owned audit scripts, tests and this document are edited. All frozen
interfaces, proof budgets, roots, central maps and axiom pins are unchanged.
No producer edit, push, merge, PR, pre-gate or deployment is performed.

## Checkpoint 1: exact inventory and premise roles

PASS: 48 mapped modules, 311 public named theorems, 56 private named helpers.
G25 has 37 modules/185 public/54 private; G31 has 11 modules/126 public/two
private. Exponentiation and Axioms have zero public named theorem declarations;
they are accounted for, not silently omitted. Private entries use source labels,
not Lean's generated internal private names. Anonymous examples and record
projections are not miscounted as exported named theorem declarations; their
premise schemas and relevant controls are separately inspected.

`source-census.json` preserves each literal frozen source signature, owner,
location, section-variable context and signature/file hashes. Every mapped file
and the map are compared to `git show BASE:path`. The scanner fails closed on
unsupported layouts. A discovered `let low :=` signature-boundary bug was fixed
before fidelity acceptance; the complete signedClean_nat conclusion is retained.
The source scanner grants no proof credit or stale proof-status labels.

`kernel-census-v424.json` independently records all 311 actual kernel types,
full binder telescopes, conclusions, proposition/instance flags and empty
universe-parameter lists. Its name set equals the complete frozen public set.
`premise-structures-v424.json` records the actual constructor types of 16 public
premise/certificate structures. `statement-inventory-v424.json` joins them with
owner and exact source signatures, classifying all 984 binders:

| Role | Binders |
|---|---:|
| Global uniform certificate structures (Type-valued) | 10 |
| Global function law | 1 |
| Per-input feasibility structures | 17 |
| Per-input logical premises | 110 |
| Intrinsic input data | 843 |
| Instance data | 3 |

Eleven statements have global-model premises; 100 have per-input feasibility
premises (these sets overlap). Unary/Binary/Checked/ClosedCertificate laws are
uniform over their original operand/tail/state domains. Invocation capacity,
Represents, Stable, HashInput and NamespaceInput fields relate one shared input
assignment. State-specific ValueCertificate/ValuesCertificate constructors are
not mislabeled as uniform over source states. Their target-tail uniformity is
recorded separately. A proposition flag alone is never used to distinguish
these roles: global certificates have data fields and are Type-valued.

## Checkpoint 2: simultaneous witness for every frozen statement

PASS: **311 verified joint witnesses; zero uncovered statements**. Each original
public theorem occurs exactly once across 46 additive witness modules.
Every full telescope is existentially bound, including implicit/unused inputs,
instance data, proof premises and global certificate values. Every witness
retains the original instantiated conclusion. No individually inhabited premise
is substituted for a simultaneous assignment.

`WitnessCommand.lean` constructs the expected existential type directly from
the unchanged declaration, retains all binder domains, checks exact argument
count and emits ordinary kernel-checked Exists introductions plus an application
of the original theorem to those same inputs. `Fixtures.lean` provides actual
intrinsic states, a typed heap/path/reference, a represented nonzero environment
frame, stable frame pair, coherent hash/namespace inputs, and source steps.
The generated files show every chosen argument explicitly. No new premise,
source IR or surrogate contract is introduced.

The final verifier independently opens the original forall telescope and walks
the actual existential domains in order; it does **not** reuse the type generator.
It checks every dependent domain and the unmodified conclusion. Standard Not/Ne
negative conclusions stay intact; custom aliases hiding additional forall
premises fail closed. All 311 frozen statements pass, with no universe or hidden
premise case excluded. Dependency sets are limited to the existing foundational
`propext`, `Classical.choice`, `Quot.sound`; no new axiom/sorry/native_decide or
heartbeat override is introduced.

Proof-mode `verify_census.py` validates the entire 149-module source/dependency/
distribution/output/receipt chain. Emitted census, schema and verification JSON
hashes are bound to the successful producer receipts. Producers archive/remove
old reports before a forced replay, so stale reports cannot earn credit.
Exact source/kernel/verification name sets, witness FQNs, binder counts, raw
original types, permitted axioms and report statuses must all agree.
`coverage-ledger.json` is the authoritative exact-once proof ledger; source scans
and unverified candidate markers never award proof credit.

## Checkpoint 3: constructive success and negative controls

PASS, finder/skeptic reviews closed: 55 additive public theorem reports, with
104 current source/dependency/distribution/output/receipt checks. The dependency
union is exactly propext, Classical.choice and Quot.sound. There are zero new
axioms, sorry, native_decide or heartbeat overrides.

ScalarTotality constructs well-ranged successful inputs for every accepted
unary/binary operator/type pair, proves actual pure/checked selector availability
and empty-tail capacity, and supplies the explicit division/modular fallbacks.
Generic certificate success is derived from those constructed source cases;
no target-success premise is assumed. Reject-all and arbitrary-payload
always-revert alternatives contradict the unchanged public contracts.

ClosedTotality constructs intrinsic literal certificates at every primitive type,
and one unary/binary layer for every available pure operator certificate.
The binary operands deliberately decline the existing short-circuit test.
This is constructive coverage of these supported families, not an arbitrary
recursive compiler grammar, generic reads/calls, or short-circuit compilation.
Generic certificate-field projections are consistency consumers and earn no
additional program-totality credit. Literal capacity covers every tail shorter
than 1024; the full physical boundary is explicitly refused.

EnvironmentTotality proves actual environment selection totality, resolved
metadata/hash selection success, and coherent nonempty typed hash/namespace
execution. Generic value/list certificate consumers retain the original state
and tail quantification. Caller observations distinguish success and panic
payloads while preserving the frozen equivalence of exceptional halt and empty
revert. SuccessControls retains its nine Boolean, checked arithmetic, panic,
capacity and local opcode-refusal controls.

BoundaryVectors kernel-checks two real encoder identities and exports the actual
bytes with a producer-bound hash. Six finite external EthereumJS cases pass:
negatedTrue at exactly six gas versus five, metadata PUSH0 on Osaka/Shanghai
versus Paris refusal, and a synthetic always-revert negative compiler control.
Two harness negatives reject a wrong value and wrong halt. Installed dependency
versions are asserted against the unchanged repository pins before reporting;
vector SHA256 is recorded. Host step-limit errors propagate as harness failures,
never as EVM out-of-gas or source exhaustion.

The local Lean evaluators have no gas/fork input. These kernel proofs do not
prove fetched EVM execution or gas/fork agreement. The six reference runs are
external tests only, not compiler correctness proofs or a universal gas theorem.
No takeover of H55/G49 or any unassigned compilation scope occurs.

Independent finder and skeptic found no weakened contract or invented success
premise. Their three tooling findings are fixed: pre-launch 4 GiB headroom refusal
(with a boundary regression), installed-version provenance assertions, and a
fresh producer-bound axiom stdout hash required by the C3 evidence verifier.
A first final-gate attempt was deliberately stopped with exit143 to apply the
review fix and finish this checkpoint before checkpoint4; no pass is credited.

### Checkpoint 3 committed handoff

Commands: bounded_lean.py --reuse with native4.24 on ScalarTotality,
ClosedTotality, EnvironmentTotality, SuccessControls, BoundaryVectors (bound
boundary-vectors.json) and SuccessAxioms all exit0; reference-boundaries.mjs
reports six cases/two negative controls PASS; success_evidence.py reports
55 theorem axiom sets/104 valid receipts PASS. Exact command arrays, output,
source/output hashes and timings are retained in the private receipts/logs.
Final affected acceptance and checkpoint4 remain pending. Scope questions=[];
no active producer/interface-repair blocker and no frozen statement modified.

## Checkpoint 4: partial, preserved at retirement

Census/fidelity remains311 exact-once joint witnesses across48 unchanged modules,
zero uncovered. Both read-only reviewers independently accepted the original48
recheck: wall313.914 ->319.745 seconds (+1.858%), CPU313.649152 ->319.326654.
All commands, source/fingerprints/output hashes/resource policy match. The
immutable baseline manifest830102ff... and all164 entries are verified, with
indexed receipt hashes, duplicate rejection, exact module-set checks and fresh
measurement-log/receipt agreement. No >10% timing STOP occurred.

The first recheck hit the4GiB reserve guard at PowerBounds216.288s and receives
no passing credit. Read-only POSIX_FADV_DONTNEED on owned unused historical
files released cached pages without deleting data or changing bounds. Current
memory dropped4,628,021,248 ->717,115,392 bytes. Retry passed PowerBounds238.548s,
sampled peak8,225,436KiB, under identical active cache/flags/source/policy.

The normal native4.24 ./run-lean.sh was explicitly stopped at retirement, after
last completed job776/5999. No build error appeared before stopping. Supervisor
exit143, outer wrapper exit1; queued post-gate acceptance was canceled exit143.
No full-gate or RUNTIME_GATE_PASS credit is given. Bounded KeySort passed first,
and actual Lean4.24.0/Lake5.0.0-src+797c613 are logged. Partial native artifacts
and all original VM evidence remain on disk; nothing was deleted.

Open original obligations: finish full normal gate and actual SolKey sort check;
final affected acceptance; final C4 finder/skeptic closure; successor integration.
No extra backfill candidate was assigned. No new proof implementation after the
retirement instruction. H82 standing permission does not override the stop.

### Retirement handoff and operational limits

The complete original first task message was read from this thread and saved
as original-rendered-assignment.md under tests/h62/item2/audit-g25-scalar-lowering/handoff/.
That directory also contains the complete work/backfill queue, exact scope
manifest, subsequent toolchain/H82/retirement messages and stopped-state record.
They are committed into the cumulative patch and bundle. Bulk evidence and
checksums remain off git. Coordinator-local paths are provenance, not assumed
accessible to a survivor VM; export packages include actual VM copies.

No H71 push permission text was available in this thread or coordinator inputs;
original no-push authorization therefore remains. Only the original isolated
branch is committed; no push, master operation, PR, replacement goal or VM.
No Claude-owned original source was edited and no message sent to its owners.

Goal pause failure is precise: the only exposed goal transition tool accepts
complete|blocked, not PAUSED. No unsupported parameter or substitute state was
sent. The worker has stopped and must not resume automatically; coordinator
must perform any missing PAUSED transition externally. Schema-v1 validation is
limited to the visible task contract because no authoritative schema/validator
was present; the format question was unanswered before retirement.

## Resource policy and measurements

Heavy checks are serial and hold the repository writer lock. Lean receives
`LEAN_NUM_THREADS=1`, explicit `-j1 --tstack=131072`, unchanged proof options and
an isolated, source-hashed Lean 4.24 cache. Reuse requires current source and
transitive imports, the full toolchain bin/lib distribution, intact successful
receipt and output hashes; direct mode requires validated imports and one file.
Failed clients are blocked; independent files may continue serially, with an
overall failing verdict retained. Expected emitted evidence is receipt-bound.

The hard limit is the existing **16 GiB VM cgroup**, with zero system swap.
The live 4 GiB headroom and 12 GiB child-RSS guards are **sampled soft stops**,
not a hard 12 GiB cgroup cap. No VM bound is raised and no systemd job is used.
Children are terminated/reaped on guard failure, exception or interruption.
An initial artificial 12 GiB address-space limit aborted PowerBounds around
4.8 GiB RSS; it was removed because the repository warns that virtual arenas
are not resident memory. That failed attempt is preserved and is not used as a
passing or comparable timing baseline. The corrected run passes PowerBounds
in 232.044 seconds, sampled peak 7,910,508 KiB. No proof budget/source was changed.

Normal receipts record actual command, source/dependency/distribution hashes,
exit, wall/CPU times, sampled RSS and the correctly labeled cumulative maximum
child RSS. Exception/interruption cleanup does not append a normal result row.
Original48 recheck passes at +1.858% wall time. Failed/differently bounded
attempts receive no passing timing credit.

## Reviews and reproducibility

Independent read-only finder and skeptic review every milestone; neither uses
Lean/server or edits files. Confirmed findings are fixed before acceptance:
source fidelity, signature boundaries, namespace/identifier handling, correct
model roles, direct-mode dependency validation, toolchain/receipt integrity,
quoted imports, resource labels, exact witness links, duplicate rejection and
emitted-report provenance. Regression suites cover these failure modes.
Final review records and command results remain off git with SHA256 manifests.

Bulk signatures, inventories, proof ledgers, logs and timing data remain under
`/workspace/h62-audit-g25-artifacts/evidence`; deterministic generators are in
`scripts/h62/item2/audit-g25-scalar-lowering`. Checked Lean modules remain under
`tests/h62/item2/audit-g25-scalar-lowering`. No central registration is applied.
Audit elaborator/IO tools are not core-registration candidates: core imports
must remain free of elaborator dependencies. Coordinator registration fragments
will distinguish audit support from any separately approved pure proof exports.

The exported handoff records the actual full committed head, base, absolute VM
paths, exact commands/outcomes, proof/external-test boundary, timings, reviews,
remaining work and checksum manifest. Do not start/reset a goal or self-launch
a replacement thread. After the required 3–5 completed items, hand the exact
original VM/goal/state to the coordinator; a checkpoint is not full completion.

## Successor regeneration after H82 consolidation

This update preserves the retired worker's historical results above. Their raw
archives and original timing baseline are unavailable here and are
**UNVERIFIABLE** as exact bytes under H30/H86. Fresh results below are separate
measurements, not authentication or reproduction of the old receipts. The
ownership labels were reconstructed verbatim from the authenticated H82b frozen
assignment; they are not recovered/current registry keys.

The fresh Lean 4.24 witness closure checked 149 modules in 513.191 seconds and
verified all 311 frozen public statements with zero uncovered statements. The
original statement base remains c6f550e281a7e5affa9a99bc2cdaed556dec00e4. The only
permitted mapped-file scheduling difference is the published exact PowerBounds
preamble setting Elab.async false; any other source change fails census
validation. PowerBounds took 212.904 seconds. Checking witnesses establishes
these particular simultaneous premises, not full semantic coverage or complete
Source/EVM correspondence. Fresh C3 evidence validates 55 public theorem axiom
reports and 104 proof receipts. Six actual-byte gas/fork/halt cases and two
rejecting-harness controls are external tests, not universal gas/fork correctness.

Fresh resource policy v3 retains the hard 12 GiB per-process address-space
limit, sampled 10 GiB workload-tree RSS stop, 4 GiB available reserve and existing
16 GiB VM bound with no active swap. Per-file time is 300 seconds; aggregate
build time remains 14,400 seconds. The sampled guards are not a hard aggregate
12 GiB cgroup cap. The runner now tracks detached descendants through a child
subreaper, reaps its own children after interruption, and rejects late successful
exits. Regression tests cover detached-session cleanup, cancellation during
process creation and late completion. The interrupted v2 attempt receives no
proof credit. Historical PID-1 zombies remain recorded; cleanup of new owned
children does not establish cleanup of all historical processes.

The first core checkpoint failed with thread-creation exceptions in generated
Yul checks. A direct recheck of the failing Arithmetic.Part00 with scheduling
Elab.async=false passed in 10.598 seconds under unchanged budgets. A temporary
command wrapper applies that scheduling setting only to Yul/Checks modules;
production Lean statements and proof bodies were not edited. This is a new
operational recovery measurement, not a successful before/after speed baseline.
The resumed core checkpoint was interrupted after its outer supervisor disappeared across a turn/environment transition. Its orphaned workload was stopped after detection; the sampled aggregate guard had a coverage gap, so this attempt receives no resource or full-gate pass. The queued documentation correction likewise did not survive and was executed explicitly afterwards. These failures are preserved separately. The interrupted checkpoint does not establish the
full Examples/run-lean.sh gate or remove original timing STOPs.

Acceptance retains all original 15 checks, including the original-base
whitespace and global documentation checks. Consolidated incremental scope is
checked against the exact authenticated H82b manifest, while frozen statement
fidelity continues to use the original base. The collector records its source
hash. Unit controls reject arbitrary widened manifests and wrong namespaces;
a positive main-path test exercises report serialization. These tests do not
supply runtime-gate proof. Original-base whitespace debt and other-owner missing
documentation references remain failures, without checker exemptions.

The fresh kernel and C3 receipts above were generated before adoption of master e8247d927. Their exact input fingerprints remain recorded; they do not automatically validate changed upstream dependencies. Acceptance is rerun after adoption, with any invalidated receipt retained as a failure requiring regeneration.

Post-adoption acceptance completed 13/15 checks. The current collector source
hash is 934df9288cee02a2cfe681b4e51a020cee8b5b4ec6497bc4bcba82d339404489;
the report records no scope violations or forbidden Lean tokens. All 149 witness
closure receipts and all 311 statement links remain valid after adoption.
Original-base whitespace exits 2 and global documentation paths exits 1 (five
missing references); neither failure is waived. The incremental diff is clean.
Independent read-only finder and skeptic reviewed the scoped tooling and these
boundaries without Lean/server/build. C4 and the original whole lane remain
incomplete. No resource/full-gate acceptance or historical timing identity is
claimed from the interrupted checkpoint.
