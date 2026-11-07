# H62 item 2: audit-bytecode-selection

Resumed by the subsequent explicit coordinator instruction; the full four-checkpoint assignment remains unfinished.
This is additive audit work on the assigned branch, based on
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Audit-owned changes leave original interfaces, generated
roots, module maps, axiom pins and toolchain untouched; explicitly merged upstream
changes are separate. No general H55/G49 proof is supplied.

## State and reproducible commands

Repository: `/workspace/solidity-lean`.
Original VM: `ccarenv_b64_Y2NhcmVudl84NjViY2M2ZmQ4ZTA4MTkxOTNlNTE4OGJlYWQ1ZGRmZg`.
Original assignment rendered-prompt SHA256:
`361608a45a000cb8b29a5b031ef22ea04588a0d905a9895dc65f0dbc4d416c18`.
The active goal ID is not exposed; preserve that existing goal, not a substitute.
Branch: `codex/solidity-h62-2-20261106/audit-bytecode-selection`.
The initially clean `work` branch at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`
was preserved. `git fetch origin master` retrieved the published base; Git
confirmed the base is an ancestor of fetched `origin/master` (`c73b8b33f` at setup).
The assigned branch was created at the exact base under the writer lock.

The coordinator inputs in `/workspace/h62-coordinator-inputs/` all matched
`sha256.json`. This is an audit lane, not a migration overlay: it preserves
`lean-toolchain` at v4.24.0. The official v4.35.0 pin is recorded in the supplied
migration inputs and is not a license to edit the audit lane toolchain.
`get_goal` is not exposed; the existing supplied goal remains authoritative and
must not be reset or replaced. No per-file Lean MCP tool is exposed. The local
lean-verify skill was read; source-only serial Lean checks are the fallback.

Actual tools:

- Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release.
- Lake 5.0.0-src+797c613 (Lean 4.24.0).
- Tool binaries: `/workspace/.setup/tools/lean-4.24.0-linux/bin/`.
- VM cgroup memory: 16 GiB; swap absent. No `systemd-run` was used.
- Writer lock: `/tmp/solidity-lean-feature-groups-20261025/writer.lock`.

From the repository root, under that lock:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item2/audit-bytecode-selection/test_census.py
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-bytecode-selection/census.py --output /workspace/h62-audit-bytecode-selection-evidence/census.json
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item2/audit-bytecode-selection/verify.py --repo /workspace/solidity-lean --evidence /workspace/h62-audit-bytecode-selection-evidence/verification-FRESH --lean /workspace/.setup/tools/lean-4.24.0-linux/bin/lean
```

The verification output directory must be fresh. Its dependency traversal masks
comments, handles multiple import names, rejects cycles, and builds every local
import from source in order. It uses neither the old package build nor Lake's
v4.24 artifact cache. Current verifier processes use `LEAN_NUM_THREADS=1`, `-j1`, `-M8192`,
`--tstack=131072`, the existing hard 16 GiB VM cgroup cap, no swap,
a 300-second timeout and a polled 4 GiB physical/cgroup reserve. The allocator
setting is `MIMALLOC_PURGE_DELAY=0`. The extra virtual-address cap used at the
first checkpoint was removed after the resource diagnosis recorded below. No proof options or
heartbeat budgets are raised.

## Three completed backfill items

1. Deterministic conservative source census plus four adversarial scanner tests.
   It pins BOTH the module-map bytes and all mapped source files to the frozen
   base. All 227 distinct mapped files are present; 1,660 named theorem/lemma
   candidates are retained exactly once by source offset, with literal source
   signatures, SHA256, preceding-context hash, and explicit uncovered status.
   These are source candidates, not elaborated declaration names/types. Section
   parameters, structure fields, hypothesis classification and owner assignment
   still require elaborated review. No filtering by presumed feasibility occurs.
2. Five additive feasibility/control theorems in
   `tests/h62/item2/audit-bytecode-selection/Witnesses.lean`.
3. Five additive supported-literal totality/success/control theorems and the
   separate `LiteralTotal` audit requirement in
   `tests/h62/item2/audit-bytecode-selection/LiteralSuccess.lean`.

The source census deliberately reports zero mechanically linked witnesses:
proof-to-original-statement linkage is not inferred from theorem names.
The following manual links are limited and must survive statement-fidelity review:

| Frozen declaration / contract | Audit evidence | Accounting |
|---|---|---|
| `Solidity.Backend.Selection.V2.FrameCertificate.prefixes` | `Solidity.H62.BytecodeSelection.prefixes_jointWitness` | All explicit parameters and hypotheses simultaneously realized; empty identity code/frame, admitted room, split and run. |
| `Solidity.Backend.Selection.V2.no_overfull_output` | `Solidity.H62.BytecodeSelection.no_overfull_output_jointWitness` | Its large-output hypothesis is feasible; negative conclusion retained. |
| `Solidity.Backend.Selection.V2.Controls.reject_push_program` | `Solidity.H62.BytecodeSelection.reject_push_program_jointHypotheses_impossible` | Intentional negative control, not a positive witness and not itself a public-interface defect. |
| `Solidity.Backend.Selection.V2.CompilerPremise` | `Solidity.H62.BytecodeSelection.compiler_global_and_input_jointWitness` | Global producer inhabitance plus one actual numeric-height input in the same fixture; NOT full RuntimeConsumer coverage. |
| `Solidity.Backend.Selection.RuntimeConsumer.consume` | `Solidity.H62.BytecodeSelection.legacy_runtime_empty_relation` | Reproduced legacy V1 empty-relation admission, conditional on a supplied composition certificate; owner ticket below. |

`selectLiteral_total` covers every `Fin Evm.W` literal.
`selected_literal_success` connects the very same selected certificate's code
with actual scalar execution and exact output for every literal/input stack.
`reject_all_not_total` rejects the dependent reject-all selector.
`literal_ir_success` executes a nonempty literal IR program and preserves the
whole nonstack caller machine. `always_revert_fails_literal_success` proves
observable revert differs from this required successful result.
These are gasless component results: the scalar/IR models have no gas/fork
parameter and do not enforce the charged EVM's physical stack domain. Neither
arbitrary-height scalar success nor a self-adapter is external-EVM evidence.
No charged failure/gas/fork-boundary obligation is discharged by these fixtures.

## Owner ticket V1-EMPTY-RELATION

Owner routing: area producer through coordinator, with H55-G49 as consumer.
The supplied snapshot identifies coordination roles, not a verified exact-file
owner for every mapped module; that ownership census remains open. This saved
ticket is for the coordinator's relay; no unavailable `relay.sh` delivery is
claimed, and no owner permission is inferred.

ESCALATE: Solidity.Backend.Selection.RuntimeConsumer.consume admits the constantly-false source relation given any supplied composition certificate; checked evidence is Solidity.H62.BytecodeSelection.legacy_runtime_empty_relation, and no execution follows. Repair options: owner approves V1 deprecation and a witnessed V2 consumer migration; owner publishes a versioned source-coverage contract with supported-case witnesses; owner couples the public compiler contract to explicit supported-program success and rejects trivial compilers. Frozen V1 remains unchanged pending owner action.

V2 already contains `inhabited`; this ticket does not claim its source relation
covers all source observations. It requests no unapproved premise or exclusion.
The intentional `reject_push_program` control is a distinct issue: optional
Q-N01 asks how the final census should classify deliberate contradictions. It
must not block positive public-interface work or be called a vacuous interface.

## Checks and reviews

Off-Git evidence root: `/workspace/h62-audit-bytecode-selection-evidence/`.
`keysort.log` records the bounded prerequisite passing in 1.768 seconds.
The initial timing attempt used unavailable `/usr/bin/time` (exit 127); rerunning
with Bash `time` passed. This provisioning error is not a proof failure.

The first source check stopped on recursive reduction of the 1,025-element list
witness. Its failed log is retained in `verification/`. The proof was repaired
using `List.length_replicate`, without raising a budget or altering a statement.
The second check, `verification-2/`, passed all 41 files in 101.502 seconds;
a final single-file check removes an unused binder warning. Its current proof
and axiom output is in `witnesses-final.log`. The ten audit theorems use only
`propext`, `Classical.choice`, and/or `Quot.sound`; no new axiom, `sorry`,
`native_decide`, kernel shortcut, or maxHeartbeats override was introduced.

The 38 unchanged dependency files common to the two clean-output runs took
102.312 seconds then 98.493 seconds (−3.73%). This is reproduction timing on
unchanged source, not a claimed refactor speedup or the final whole-package
performance gate. No existing proof or representation refactor occurred.

The first staged doc-path gate detected fictitious backticked Lean paths in the
scanner's removed-row fixture. The fixture now uses existing mapped paths;
the regression's removed-row assertion is unchanged. Both its tests and the
staged documentation gate were rerun after the fix.

Independent finder and skeptic reviews were read-only, with no Lean server or
build. Both found that the mutable module map could shrink the census; pinning
it to BASE and a deleted-row regression fixed the finding. Skeptic also asked
for fresh/cycle-safe import traversal and same-selected-artifact execution;
both are implemented. Their rechecks found no remaining objection to the
limited backfill. Documentation/handoff wording received a final read-only
review before export. Full review records are saved as `reviews.md` off Git.

## Second backfill milestone: three further items

All four assignment checkpoints remain partial. The branch now has twenty
checked audit theorems in four standalone Lean files, plus two new closed proof
structure definitions (`RuntimeFixture.compiler` and `RuntimeFixture.consumer`).
These do not implement the general H55-G49 theorem or edit producer interfaces.

### Elaborated census and fidelity provenance

`scripts/h62/item2/audit-bytecode-selection/elaborated_census.py` generates an
external Lean inspection program. `inventory_report.py` normalizes its output.
The final Selection and ValueGate reports cover six distinct mapped modules,
188 constants, 33 direct fields and 28 proof fields. The other 221 mapped files
remain uninspected by this elaborated census. The complete conservative source
census still contains all 227 files and 1,660 named theorem candidates.

The new reports retain fully qualified names, raw kernel type expressions,
pretty types, universe parameters, binder types/proofness, head constants and
parent-subobject metadata. Proofness is not an automatic global/per-input role
classification. Direct fields are not flattened inherited obligations; parent
links must be followed in the final coverage census. Generated/private theorem
origins are retained for review. No field or source theorem is silently filtered
because it is difficult or apparently infeasible.

An inspection manifest pins exact frozen source bytes, the selected module set,
and the SHA256 of the unexpanded inspection template. Each emitted record and
completion marker carries that manifest fingerprint; completion also reports
per-module counts. The reporter checks the actual inspection source checksum,
module/source equality, unique declarations, complete counts, diagnostics and
the supplied ownership snapshot checksum. It honors writer exclusions.
Nine report/roster regressions reject truncation, diagnostics, mismatched modules,
duplicate declarations, stale inspector output, and excluded-owner matches.
The default verifier roster includes all four audit Lean files; a regression
checks that no new audit file is silently omitted. The four earlier source-scanner
tests also pass.

Two independent runs for each context normalize byte-identically. Evidence:
`selection-elaborated-final-1.json`, `selection-elaborated-final-2.json`,
`valuegate-elaborated-final-1.json`, `valuegate-elaborated-final-2.json`, and
`inspection-final-gates.json` under the evidence root. The Selection context has
158 records and no explicit file-writer match in the supplied H30 snapshot;
those owner fields remain unresolved. The 30 ValueGate records match the
explicit PAR-AE writer scope. This does not transfer compiler or producer ownership.
Raw census records still have no mechanically inferred witness linkage; the
following reviewed links are additional manual evidence, not a complete ledger.

### Full closed runtime projection witness

`tests/h62/item2/audit-bytecode-selection/RuntimePremiseWitness.lean` uses the
existing nonidentity 70-byte composition. Its V2 compiler record has an actual
successful input and preserves the chosen relation uniformly. The closed
consumer retains the unchanged compiler and decoder antecedents and derives
its fixed input/output stacks from the relation using `irStack_injective`.
It reuses the published `CompositionControls.conditional_transport`.

`runtime_projection_jointWitness` simultaneously supplies the consumer self,
compiler, decoder and every per-input antecedent of
`Solidity.Backend.Selection.V2.RuntimeConsumer.consume` for that SAME artifact.
`runtime_antecedents_jointWitness` additionally carries the actual successful IR
execution. `actual_nonidentity_bytes` reuses the independently fetched six-step
byte execution. This is one fixed local self-adapter fixture; it supplies no
external Bridge agreement, source-wide coverage, gas/fork result or general G49
construction. Q-H55-SELF was resolved within the authorized additive audit scope;
a missing general H55 artifact does not block this closed fixture.

### Checked public-compiler success and observable refusal

`tests/h62/item2/audit-bytecode-selection/ValueGateSuccess.lean` supplies the
existing global `ValueGateCertificate` with actual `Compiler.compile` selection
and execution of that same compilation. Its uniform theorem retains both the
success and revert branches for every caller machine. A concrete inhabited
context witnesses execution premises. The nonpayable case has nonempty code
and succeeds at zero call value; a separate theorem observes nonzero-value
revert. Reject-all selection and always-revert execution controls fail, including
an explicit always-revert comparison against the nonempty supported program.
These are actual intrinsic compiler/IR results, not a replacement compiler.
They remain gasless and do not establish charged native behavior or source-origin
adequacy. Original failure/gas/fork observations are neither erased nor reclassified.

### Actual verification, resources, reviews and remaining work

The expanded runtime source check first failed in unchanged `PowerBounds.lean`
with `std::bad_alloc` under the audit wrapper's additional 12 GiB virtual cap.
The VM recorded no OOM. Without that extra cap, the identical module passed in
259.666 s, sampled peak RSS 7,951,300 KiB and virtual size 15,544,028 KiB. The
physical cgroup cap, 8 GiB Lean heap cap, no-swap requirement and 4 GiB reserve
were retained. This follows the repository warning that reserved virtual space
is not resident memory. The documented allocator setting
`MIMALLOC_PURGE_DELAY=0` then passed the same module in 264.308 s (+1.79%), sampled
RSS 3,758,948 KiB. No heartbeat, proof or physical-memory budget was raised.
These are single-prerequisite measurements, not the final package timing gate.

The runtime closure checked 94 original modules successfully, then the new leaf
exposed a missing V2 import. After adding that import, its additional prerequisite
and current runtime leaf passed (`premises-v2-extra.log`, `runtime-final-2.log`).
The independent ValueGate closure passed all 188 files in 684.877 s. Its final
leaf with the added concrete refusal controls also passes (`value-gate-final.log`).
All twenty audit theorems and the two new closed proof definitions use only
standard `propext`, `Classical.choice`, and/or `Quot.sound`. No new axiom,
`sorry`, `native_decide`, or raised maxHeartbeats option appears in the audit files.

A proposed binary-import consolidation rejected unequal binary hashes for two
independently checked `Evm/Signed` outputs. No binary was combined or accepted by
that experiment. Its unused copier and failure are retained off Git only.
The final inspections instead use their separate coherent source-check contexts;
comparison of inventory DATA does not combine opaque imports. See
`import-context-boundary.md` and the individual source-check journals.

Independent read-only finder and skeptic reviews used no Lean server or checks.
Finder required completion/manifest binding, module/source equality, ownership
checksum and exclusion checks, and finally the inspection-template fingerprint.
All were fixed with regressions. Skeptic confirmed the closed self witness is
within additive audit scope and the checked compiler controls preserve the
frozen observation branches. Final review records are `reviews-milestone-2.md`.

The full elaborated census, per-statement role/owner and witness ledger, remaining
supported compiler families, charged gas/fork controls, full affected validation,
`./run-lean.sh`, and final acceptance/performance gates remain pending. No
RUNTIME_GATE_PASS or complete checkpoint is asserted. After these three further
backfill items, continue on the SAME VM/branch/goal in a coordinator fresh thread.
The next useful step is expanding the elaborated inventory to the other core
mapped modules (190 total core roots; 703 local source dependencies), then the
37 mapped Bridge files. Keep import contexts and their evidence provenance
explicit. A kernel-type-derived explicit-hypothesis witness domain may help avoid
manual binder omissions; it must be independently reviewed and must not unfold
negative conclusions into false extra preconditions or omit hidden premises.

## Third milestone: derived domains and full core census

Four further additive work items are checkpointed: the exact-domain audit
elaborator and five applications; coherent source validation of all mapped core
roots; the complete core elaborated census; and its reviewed evidence linker.
The full assignment and all four checkpoints remain partial.

`HypothesisDomains.lean` derives a new feasibility proposition directly from the
frozen theorem's raw forall binders. It retains implicit, data, self and proof
binders with their dependencies, substitutes lets, and replaces only the terminal
conclusion by True. Not/Ne conclusions are not turned into extra false premises.
It rejects non-theorems, universe-polymorphic targets and hidden binders under
reducible results. It imports Lean only in this standalone test module and must
never enter the intrinsic core or generated roots. Toy cases check these
boundaries. No frozen declaration or representation was changed.

Four positive domains cover V2 RuntimeConsumer.consume (including consumer self,
compiler, composition, decoder and actual related input), FrameCertificate.capacity,
FrameCertificate.prefixes with a populated tail and nonempty executed prefix,
and no_overfull_output. A fifth theorem refutes the intentional reject_push_program
domain; it is not a positive witness or a repaired interface. There are now 25
named audit theorems and two closed proof definitions across the five audit files,
plus private elaborator regression fixtures. The newer exact-domain ledger does
not automatically infer coverage from the other 20 audit theorems.

The serial fresh-output check covers 190 mapped core roots, their 703 original
local source dependencies, and all five audit files: 708 successful checks in
2,559.278 s. Each journal row records the exact command, unchanged source hash,
output hash, log, elapsed time and sampled RSS/virtual peaks. All original
Solidity source bytes match the frozen base. Peak RSS was 3,759,408 KiB; no
resource stop occurred. The existing 16 GiB cgroup cap, no swap, four GiB reserve,
Lean eight GiB heap, one thread/-j1 and 300 s per-file limit were retained.
PowerBounds took 283.104 s versus the earlier same-source 264.308 s (+7.11%);
this is reproduction evidence, not the final whole-package performance gate.

Actual binaries remain Lean 4.24.0 Release commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b and Lake 5.0.0-src+797c613.
The bounded KeySort prerequisite already passed (exit zero, 1.768 s;
`keysort.log` and metadata.json record the command). This audit branch performs
no toolchain migration or cut-over; the official v4.35.0 pin is preserved in
coordinator inputs, and no migration/runtime gate is claimed on these results.

The latest inspector uses Lean's original-theorem metadata query. The 190-core
inventory contains 3,111 records: 2,499 theorem records, 154 direct fields
(130 proof fields), and 458 other interface/premise constants. It records kernel
type expressions, binders, direct parents and frozen source hashes. Of the theorem
records, 1,213 match source names directly and 1,286 retain generated/private
origin follow-up. Exact-file writer matches are unresolved for 1,145 records.
Two inspections in the SAME coherent checked-import context took 86.813 s and
85.810 s and produced byte-identical normalized inventory data. The 37 mapped
Bridge files remain explicitly uninspected; inherited obligations are not flattened
and predicate definitions still need body/role classification.

`witness_ledger.py` links the four positive domains and one refuted control to
unique frozen records, exact helper result signatures, checked source/output
hashes and allowlisted axiom output. It leaves 3,106 records uncovered. It is an
evidence linker that trusts genuine upstream inventory/journal inputs, not an
independent proof checker or authenticator. It does not establish original
conclusions or silently waive any source candidate. The output records every
core declaration once and preserves all 37 uninspected paths.

Independent read-only finder and skeptic reviews used no Lean server/jobs.
Skeptic found that exit-zero without an output could pass the verifier; this now
fails closed, with a fake-runner regression. Both reviewers found that an initial
linker regex accepted weakened helper-type suffixes; it now matches the complete
expected signature through the proof delimiter. All-five-helper implication and
disjunction mutations are rejected. Both reviewers confirmed the fixes and no
remaining blocking finding for this limited milestone. All 16 scanner/inventory/
evidence regressions pass. The five checked audit files' printed axiom sets use
only propext, Classical.choice and Quot.sound; no new axiom, sorry, native_decide,
kernel shortcut or raised maxHeartbeats was introduced.

New evidence lives under the existing off-Git evidence root: full-core-check/,
full-core-inspection-gates.json, full-core-repeat-gates.json,
full-core-inventory.json, witness-ledger.json, milestone-3-python-tests.log,
reviews-milestone-3.md and milestone-3-axioms.json. The source verifier still
compares only Solidity originals to base: extend that check and resolve vendored
package roots before claiming Bridge validation.

Pending typed dependencies: Q-O01 requests exact-file owners for the 64 mapped
Selection/FailurePaths files lacking a snapshot match (coordinator routing is
not permission to edit them). Q-P6 requests the existing checked ByteWorld.Producer
and matching emission provenance through PAR/P6-V11 for paired-load domains.
The current MLOAD slice refusal alone does not refute every possible producer;
paired loads remain conditional, without weakening their universal memory law.
Neither missing response grants permission. Q-N01's intentional-control
classification remains open but does not block positive interface work. The
previous closed runtime self witness resolved Q-H55-SELF; a general H55 artifact
is not needed for that closed fixture. The existing single legacy-vacuity owner
ticket above remains pending, without duplicated escalation or interface edits.

## Remaining four-checkpoint queue and handoff

| Checkpoint | State | Remaining |
|---|---|---|
| 1. Exact frozen inventory and owners | partial | Core inventory complete; 37 Bridge files, generated/private origins, inherited obligations, predicate roles, owner gaps and global/per-input classification remain. |
| 2. Simultaneous witnesses | partial | Four exact-domain links and one negative control; 3,106 core records unlinked, remaining source/Bridge statements and producer dependencies remain. |
| 3. Public supported-program totality/success | partial | Beyond numeric literal and ValueGate families; remaining public compilers, observable failure, gas, fork and resource boundaries; owner-approved repairs if needed. |
| 4. Witness/fidelity verification | partial | Complete proof-to-statement census and uncovered-owner report; all final affected/full gates and acceptance/performance checks. |

No checkpoint is claimed complete. The required final `./run-lean.sh`, bounded
whole affected validation, external charged/fork acceptance and final timing
gates remain pending. `RUNTIME_GATE_PASS` is not asserted.

After these three backfill work items, the coordinator should continue in a
fresh thread on THIS VM, THIS branch and the SAME persistent goal. Do not
create a replacement goal, reset the branch, merge, pre-gate, push, publish or
register modules without the appropriate owner action. Read this handoff,
`census.json`, the ticket and the two verification logs before continuing.
The next useful work is extending the existing exact-domain ledger to the
remaining positive interfaces, classifying predicate definitions and inherited
obligations, and resolving coherent Bridge imports plus the paired-load producer
dependency. Keep all unsupported targets and owner gaps explicit.

Registration proposal for coordinator (not applied): keep the standalone audit
fixtures directly checked under `tests/h62/item2/audit-bytecode-selection/`.
If an area producer approves library adoption, give each helper a producer-
approved module path and add rows describing joint-feasibility witnesses and
same-artifact literal success to the bytecode-selection fragment. Do not import
test paths into generated roots or transfer producer ownership implicitly.

Original patch, bundle, handoff and checksum manifest are exported under the
evidence root. The final CLOUDVM-RESULT gives their absolute paths and committed
head. Bulk census/logs/oleans remain off Git; only generators, small fixtures
and this handoff are committed.


## H82 final retirement handoff

The human has explicitly retired this worker and accepted the successor relay to
solidity-parallel-20261103/executable-bytecode. No further proof implementation
or automatic continuation is authorized. This final checkpoint preserves the
small in-progress census edit and required assignment/scope handoff files only.
The successor integrates the final committed head recorded in the off-Git
retirement metadata; this worker does not take scope from the survivor.

The expanded inspector now retains all constants, original kinds, normalized
private names, optional declaration line ranges, predicate-valued result tags
and available non-theorem bodies. A bounded three-module smoke check passed in
8.420 s, producing 31 records; normalization confirms ExecutionTrace.Safe and
FailurePaths.Emits are predicate-valued definitions with bodies, not proof evidence.
The expanded version has NOT had a full census rerun or performance gate. Its
changed template rejects old pins. Preserve the earlier generated source/pins/logs
and 190-module/3111-record report as historical evidence from commit9a0c1b2bd;
never relabel it as output of this expansion. Private source-name mapping, UTF-8
positions and flattened parent edges remain incomplete. More body output may
increase runtime/storage; no full expanded-resource measurement is claimed.

Mandatory authenticated handoff files are tracked in
`tests/h62/item2/audit-bytecode-selection/handoff/`:
original-rendered-prompt.txt (complete visible original message from this thread,
including owner table), original-work-backfill-queue.md (verbatim extraction),
scope-manifest.json (all227 frozen mapped source paths/hashes, original scopes
and H82 changes), coordinator-updates.txt (all subsequent task instructions,
including retirement), remaining-queue.json (every open checkpoint/backfill/wait),
and PROVENANCE.md. Their actual file digests travel in the final SHA256SUMS.
The transcript-copy digest differs from the historical launcher-prompt digest;
no get_goal or original prompt file was exposed to verify unavailable launcher
payload bytes. This provenance limit is explicit, with the complete visible
assignment retained rather than summarized away. Coordinator-local paths are
not assumed accessible to the successor.

H82 withdraws any exact-file permission wait for statement-preserving edits.
Owner attribution gaps remain report data. The real waits are the P6/V11 checked
ByteWorld producer/code provenance and the existing legacy V1 owner repair
proposal. Neither is a blanket blocker to the successor's independent queue.
All four original checkpoints, remaining scanner/fidelity/witness work, supported
families, charged/fork acceptance and final full/performance gates remain partial;
remaining-queue.json is the comprehensive checklist. No new theorem, original
statement/definition/interface, proof budget, axiom set or exclusion was changed
in this retirement step. H68 bridges and H78 shims were not touched; intentional
contradictions remain distinct from positive witnesses.

No push is performed: H71's text/authorization is absent from available inputs,
while the original explicit no-push instruction remains in force. The cumulative
patch and branch bundle, source/evidence archive, original inputs, review records
and checksum manifests are exported off Git; no master push or Claude-owned source
edit/message occurs.

The requested PAUSED transition cannot be executed with exposed tools: the sole
goal mutation accepts only complete|blocked, with no pause/get/update endpoint.
No invalid completion/block transition, reset or new goal is used as a substitute.
The human's explicit retirement governs: this worker stops after the final saved
head acknowledgement and will not automatically resume this assignment.


## Resumed after upstream merge

The later explicit coordinator instruction authorizes continuation and merging
origin/master into this original lane. Fetch verified master20e492ee99a3fa8679aa526de0b6e731d85e4134
contains bd740a170984c03f8fedc92c4de1d5a52174ddef and the frozen original base.
The merge fast-forwarded cleanly; no default branch, goal, remote publication or
interface was changed by this action. Historical retirement files remain intact;
resume-instruction.txt and resume-state.json under the tracked handoff directory
record the newer authorization and complete updated queue. No new goal was created
or reset, and get_goal remains unavailable. All four checkpoints remain partial.

Three audit work items follow the authorized merge. The expanded inspector keeps
all4224constants from190frozen core files, including63proposition-valued constants.
It omits theorem/proof-valued bodies while preserving every declaration and exact
type, and keeps available predicate-definition bodies. All3111prior record names
and raw kernel type hashes remain identical. The old three-module proof-definition
records also remain present. The expanded data do not infer role satisfaction or
exclude data helpers from subsequent review. Direct fields remain154, including
130proof fields. The37Bridge files remain uninspected.

The source scanner now records Unicode codepoint name positions. The reporter
requires a unique module, normalized user name, original theorem kind and selection
position match. All1402named core theorem candidates map uniquely; no candidate is
unmatched or ambiguous. Generated/private-origin records still require review;
source attribution does not prove hypothesis feasibility. Regressions cover private
names, generated auxiliaries, ambiguous/duplicate locations, wrong positions and a
multibyte attribute before the declaration name. Exact signatures and source hashes
remain anchored to the original frozen base. Predicate bodies and inherited/global
versus input roles remain separate unfinished classification work.

The same expanded inspection ran in163.195s and164.794s (+0.98%) with byte-identical
normalized results. This is audit-data reproduction, not a whole-package proof
performance gate or a comparison to the smaller former census. The authenticated
import context retains703original source hashes at the frozen base and5audit files
at commit9a0c1b2bd, with every output rehashed before use. Current master differs
from that context only at Scalar/PowerBounds, where upstream added Elab.async false.
No upstream speed/resource change was undone. Results are explicitly frozen-base
inspection, NOT current-tree source validation. The current-tree/full gates remain
pending. Lean4.24.0/Lake5.0.0-src+797c613 and bounded settings remain unchanged;
no migration or RUNTIME_GATE_PASS is claimed.

`tests/h62/item2/audit-bytecode-selection/FailurePathsWitnesses.lean` adds three
closed audit theorems. Two derive the entire frozen literal_statement and
encoded_return domains, including concrete selection/encoding, states and fit/room.
The third ties every source pipeline to the same selected actual program, Emits,
admitted machine geometry, source revert and checked terminal-slice execution.
It is neither general compiler totality nor a charged/native/fork theorem or a
success-side always-revert control. Literal/ValueGate controls remain separate.
Final per-file checking passed in1.405s, with only propext, Classical.choice and
Quot.sound. Initial import-search shadowing and a multiline record-update parser
failure were fixed without statement/budget weakening; failed logs remain off Git.
No source sorry was introduced or accepted from the failed parser recovery.

The optional failure ledger group adds two exact links while preserving the
original five and rejecting duplicate targets across groups. Combined coverage is
6positive domains,1refuted intentional control and4217unlinked RAW records; the raw
count includes data/helpers and is not an asserted theorem count. Cumulative audit
proofs are28named theorems plus2closed proof definitions. No new axiom, sorry,
native_decide, frozen statement, dependent definition, exclusion or budget change.
The evidence linker continues to trust genuine upstream journals/inventory and is
not an independent proof authenticator. Independent read-only finder and skeptic
found no blocking fidelity or scope issue and confirmed the fixture boundaries;
neither ran Lean or wrote files. Focused regressions pass19tests.

New evidence: expanded-core-gates.json, expanded-core-repeat-gates.json,
expanded-core-inventory-1.json, expanded-census-acceptance.json,
failure-linked-check.json, expanded-witness-ledger.json and reviews-resume.md
under the existing off-Git evidence root. Actual commands, outputs, hashes and
reproducible generators are preserved. The next independent work includes remaining
positive witnesses, global/input/inherited obligation classification, Bridge import
validation and charged/fork acceptance. The existing P6 producer and legacy V1
owner-ticket waits remain typed dependencies; H82 exact-file permission waits
remain withdrawn. Continue the SAME VM/branch/original goal in coordinator fresh
context after these three work items; no replacement goal or completion claim.


The post-merge global doc-path gate initially found five pre-existing references
outside this lane. Under H82, four minimal verification-only file fixes retain a
duplicate-map test using an existing file and describe two proposed unregistered
modules with dotted module names and identify an off-Git experiment as an artifact
filename. No production source, proof, registration,
owner agreement or proposal-adoption state changes. The affected ABI-world scanner
regressions and the global doc gate are checked separately; initial failure logs
are preserved. These fixes do not claim an additional audit/proving scope.

Final global documentation checking passes after the four file fixes. The19audit
regressions and4affected ABI-world scanner regressions pass. The complete227file
source census repeats identically and retains all1660original signature hashes.


## Coordinator-requested b7c3cc5110b1 merge resolution

The coordinator requested merging published masterb7c3cc5110b1 into the original
audit branch. The only conflict was the packet-panic H71 candidate documentation.
This lane's sole prior edit there replaced a nonexistent proposed file reference
with its module name. Upstream already retains that module identity and adds the
newer Q1 authorization for three-control review-only proposals, including their
unregistered/unvalidated boundaries. The resolution takes that exact upstream
file, preserving the newer decisions without editing any Lean source or approving
producer adoption. Original pre-merge source/queue evidence remains historical.
The full four-checkpoint audit remains unfinished; this merge establishes no new
proof, runtime, gas/fork, axiom or performance gate. Exact parents, conflict blobs,
resolution and validation live off Git in merge-b7c3cc5110b1 under the evidence root.

Independent read-only finder and skeptic confirmed the exact-upstream resolution
and retained proposal limits, without Lean, jobs or writes. Their review covers
this documentation conflict, not validation of other incoming upstream changes.

The whole staged whitespace check reports eight single-space context lines in
an unchanged upstream migration proposal patch. Its exact upstream bytes are
retained because those spaces are unified-patch context markers. A separate
comparison against origin/master checks this lane's own changes. No complete
current-tree build or proof validation is asserted by the merge resolution.

The global documentation check also exposed a newly merged reference to a
proposed, unapplied InferHelpers file. H82 permits the documentation-only repair:
identify the proposed module by its dotted name, retaining all unvalidated
migration and owner/adoption requirements. No proposal or definition was applied.

Both independent reviewers also confirmed the InferHelpers citation-only fix
retains its unapplied/unvalidated status and owner/adoption boundaries.


## Coordinator-requested 2a43bf4fcdaf merge resolution

The coordinator requested merging published master2a43bf4fcdaf into this same
audit branch. The sole conflict was the ABI-world scanner duplicate-row fixture.
Both sides replaced the same synthetic filename with an existing module path;
this branch used ValueGate and upstream used Interface. The resolution takes the
exact upstream file. The duplicate assertion, all other regression cases and
frozen scanner expectations remain byte-identical. No scanner implementation,
Lean source, proof, interface or ownership scope was changed by the resolution.
Original four-checkpoint audit work remains partial; merge-resolution checks do
not establish proof, runtime, gas/fork or whole-package performance gates.
Exact parents, conflict blobs and validation are preserved off Git under
merge-2a43bf4fcdaf in the existing evidence directory.

Independent read-only finder and skeptic confirmed the exact-upstream fixture
resolution preserves the assertion and all other cases, without running tests
or Lean or writing files.


## Coordinator-requested 5da4771e63a4 merge resolution

The coordinator requested merging published master5da4771e63a4 into the same
audit branch. The only conflict was the generic-structuredflow registration
proposal. This lane previously named the proposed production module without
claiming its file existed. Upstream retains that intent, identifies the actual
staged test helper, and adds the newer H82 standing agreement in place of the
historical exact-file permission wait. The resolution takes the exact upstream
document. Its unvalidated/unregistered proposal and required owner/versioned
reviews for semantic, interface, budget, axiom and exclusion changes remain
explicit; no module registration or adoption is performed. No Lean source or
proof is changed by this resolution. All original audit checkpoints remain
partial. Conflict blobs, exact parents and validation are saved off Git under
merge-5da4771e63a4 in the existing evidence directory.

Independent read-only finder and skeptic confirmed the exact-upstream resolution
retains H82 and the proposal's unregistered/unvalidated status and pending gates,
without Lean, tests, jobs or writes.
