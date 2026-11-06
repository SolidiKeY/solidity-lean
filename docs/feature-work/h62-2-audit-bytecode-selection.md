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
v4.24 artifact cache. Each Lean process uses `LEAN_NUM_THREADS=1`, `-j1`,
`-M8192`, `--tstack=131072`, a 12 GiB address-space cap, a 300-second timeout,
and a continuously checked 4 GiB available-memory reserve. No proof options or
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

## Remaining four-checkpoint queue and handoff

| Checkpoint | State | Remaining |
|---|---|---|
| 1. Exact frozen inventory and owners | partial | Elaborated complete census including public structure fields; exact-file ownership and global/per-input premise classification for every statement. |
| 2. Simultaneous witnesses | partial | Almost all statement witnesses; whole runtime composition/compiler/decoder/input conjunctions; deliberate-negative classification. |
| 3. Public supported-program totality/success | partial | Beyond the numeric literal component; actual public compilers, observable failure, gas, fork and resource boundaries; owner-approved repairs if needed. |
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
