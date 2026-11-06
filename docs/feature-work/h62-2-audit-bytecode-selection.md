# H62 item 2: audit-bytecode-selection

Partial checkpoint; the full four-checkpoint assignment remains unfinished.
This is additive audit work on the assigned branch, based on
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. No original interface, generated
root, module map, axiom pin, or toolchain was edited. No H55/G49 proof is supplied.

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

## Remaining four-checkpoint queue and handoff

| Checkpoint | State | Remaining |
|---|---|---|
| 1. Exact frozen inventory and owners | partial | Elaborated complete census including public structure fields; exact-file ownership and global/per-input premise classification for every statement. |
| 2. Simultaneous witnesses | partial | Almost all statement witnesses; whole runtime composition/compiler/decoder/input conjunctions; deliberate-negative classification. |
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
The next useful work is an elaborated inventory of structure fields and an
owner-linked witness ledger, starting with positive Selection interfaces.

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
