# H62 item 2: audit-language — blocked continuation handoff

Batch `solidity-h62-2-20261106`, owner `audit-language`.
Repository `/workspace/solidity-lean`; branch
`codex/solidity-h62-2-20261106/audit-language`; frozen base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
VM environment: `ccarenv_b64_Y2NhcmVudl9hNTQ3YjYwNzYwNjA4MTkxOGJhYmM3MGZiMTJjYzk0Mw`.
The exported `handoff.json` records the full committed head without a self-hash
inside this commit. This is an incomplete checkpoint, never completion of the
four-checkpoint assignment. The existing goal must remain unfinished.

## Work completed in this thread

1. Recovered the older clean checkout without discarding work; fetched master,
   verified the exact base is an ancestor of published origin/master, and
   created the assigned isolated branch at that base under the writer lock.
   All five coordinator-input SHA256 checks passed. `get_goal` is not exposed;
   the coordinator explicitly says this optional absence is not a blocker.
2. Built a deterministic conservative source census and reconciled every named
   theorem/lemma command in the two module-map areas: 389 resolved files,
   4,146 declarations, no unresolved first-column file references or scan
   errors. Duplicate map rows share one path/declaration ID. This includes
   Bridge, controls and private declarations rather than silently excluding
   them. It is a source superset, not an elaborated interface classification.
3. Added feature, lattice and checked-arithmetic witness/client modules plus
   twelve full-telescope certificates. `hypotheses_of%` derives the existential
   input/proof tuple from the imported constant's exact leading forall binders;
   dependent hypotheses use the same local inputs. A checked command compares
   each certificate type to its indexed target and emits a canonical receipt.
   The wrong-target Lean guard and an in-memory index-reassignment attack both
   reject. No independent-inhabitant argument is substituted for a tuple.
4. Added actual ABI one-boolean decoding with both values, nonzero output,
   malformed/truncated reverts, insufficient fuel and allocation panic. The
   companion success requirement rejects always-revert and always-fuel-error
   **decoders**. This is backfill, not compiler totality or gas/fork coverage.

Four useful work items have been handed off, meeting the requested 3–5-item
fresh-thread interval. Do not self-launch a replacement goal/thread. Resume
this exact VM/goal/branch through the coordinator after prerequisite delivery.
Further independent backfill and all original queues remain authorized.

## Checkpoint status and uncovered obligations

| Frozen checkpoint | Status | Remaining work |
|---|---|---|
| 1. Exact signatures and owners | Partial | Raw frozen signatures, file hashes, complete source prefixes and scope candidates are recorded. Complete Lean name/signature verification, distinguish interface hypotheses from controls/parameters, and confirm every live owner. |
| 2. Joint hypothesis witnesses | Partial, dependencies blocked | Twelve kernel certificates are mapped exactly once. 4,134 source declarations have no certificate; not all have yet been classified as hypothesis-bearing interfaces. No universal coverage claim. |
| 3. Supported-program success | Blocked | Source/compiler totality, reject-all/always-revert compiler controls and observable failure/gas/fork boundaries remain required. ABI decoder evidence does not discharge these. |
| 4. Fidelity and witness census | Partial | All twelve mapped receipts and source-signature hashes reconcile. Every uncovered source declaration and owner candidate is reported; full elaborated census/verification remains pending. |

`tests/h62/item2/audit-language/witness-index.json` records the twelve targets.
`Unmodelled` is an inhabited diagnostic structure, not a compiler producer.
Feature exclusion feasibility is per input. No inhabited global compiler
premise structure has been established by this checkpoint.

No weakened/vacuous frozen statement has been established by this partial
review, so there is no theorem-repair escalation or interface edit. Compilation
failures below are migration dependencies, not mathematical counterexamples.
Future confirmed vacuity must emit the required single `ESCALATE:` line per
fully qualified theorem with evidence and repair options, preserving the blocker.

## Pinned runtime and gates

Official archive: `lean-4.35.0-linux.tar.zst`; SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: `4.35.0`, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Actual Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
No root toolchain file or v4.24 per-master cache was used for the new checks.
Lean MCP tools are not exposed; focused checks use explicit serial Lean `-j1`
with `--tstack=131072`. Full `./run-lean.sh` remains a required pending gate.

All final focused checks acquire the repository writer lock, reread frozen
source bytes and use fresh off-Git libraries. `check.py` chooses a virtual
memory cap below both 12 GiB and current cgroup/host available memory minus
4 GiB reserve and 256 MiB headroom. It monitors the reserve every 0.1 seconds,
requires no host swap, kills only its own process group on reserve/300-second
stops, and records the failed command. No `systemd-run` was used.

| Command/gate | Outcome and decisive evidence |
|---|---|
| Pinned `lean -j1 --tstack=131072 Solidity/KeySort.lean` | Exit 0, 1.521 s, 507356 KiB peak RSS; `toolchain/keysort-v435.json`. The final guarded focused sequence also rebuilt KeySort successfully. |
| `python3 scripts/h62/item2/audit-language/acceptance.py` | Exit 0: 389 files, 4146 reconciled declarations, kernel certification false; `acceptance-final.log`. |
| `check.py --lean <pinned>/lean --output <evidence>/final-reviewed` with all four audit files | All nine original/helper compilation records exit 0; `final-reviewed/checks.json`, per-file logs and `final-reviewed-command.log`. No warnings in final helper logs. |
| `verify.py --census <evidence>/census-final/census.json --checks <evidence>/final-reviewed/checks.json --output <evidence>/fidelity-final` | Exit 0: 12 checked full-telescope certificates, 4134 source declarations uncovered; `verify-final.log`. |
| `verify_negative.py` with the same census/checks | Exit 0: wrong-witness reassignment rejected; `verify-negative.log`. |
| `node scripts/check-layers.mjs` | Exit 0: 857 core modules, zero reaching elaborator or checked-parser adapters; `layers-final.log`. |
| `bash scripts/coord-tools/register.sh --check` | Exit 0; `roots-final.log`. No registration applied. |
| `bash scripts/coord-tools/fragments.sh --check` | Exit 0; `fragments-final.log`. No fragments generated. |
| `check.py ... Solidity/Source/Hoare.lean` | Exit 1 on unchanged Hash/CollisionBound dependency; `hash-final-blocker/checks.json`. |
| `check.py ... Solidity/Language/FixedPoint.lean` | Exit 1 on unchanged fixed-point proofs; `fixedpoint-final-blocker/checks.json`. |
| `./run-lean.sh`, Bridge validation, final SolKey check and full acceptance | Pending; no full-gate or RUNTIME_GATE_PASS claim. |

Exact absolute commands, hashes, resource observations and exits are in the
JSON records. The early unavailable `/usr/bin/time` attempt and initial
helper/parser failures were corrected, not counted as passing gates. Early
focused records predate the improved cgroup guard; only `final-reviewed` is
used for final certificate acceptance.

No existing original file was refactored or rechecked on a changed statement.
There is no valid same-resource before/after full-build timing baseline yet;
no speedup or <=10% regression claim is made. Per-file timings are saved.
A comparable whole affected validation/timing gate remains pending with the
migration prerequisites. Stop and escalate any later >10% slowdown.

## Independent reviews

Read-only finder and skeptic used no Lean job/server and made no fixes. Both
identified attributed declarations, equation/where boundaries, mutual scope
and root-name handling; these were fixed and independently reconciled. They
also found cgroup reserve, fresh-library, timeout evidence and witness-target
association gaps; all were fixed. The final finder and skeptic confirmed all
twelve checked receipts/current hashes and reported no material artifact bug.
Their review remains limited to this partial checkpoint, not full assignment
acceptance. Summaries are saved in `<evidence>/reviews.json`.

## Typed blockers and owner handoff

See `tests/h62/item2/audit-language/owner-tickets.json` for self-contained exact
file requests and reproduction evidence. The Hash migration owner is
`solidity-h62-6-20261106/migrate-hash`; its unchanged file fails at lines
407, 660 and 680 under the pinned release. The language migration owner is
`solidity-h62-6-20261106/migrate-language`; unchanged FixedPoint fails from
line 152 onward. Existing originals remain read-only. No failure artifact
is reused and no proof/premise is weakened to make these pass.

The saved tickets request coordinator delivery of owner-approved migration
prerequisites while preserving frozen statement identity. `relay.sh` is absent
in this checkout; tickets are saved for retrieval, not falsely reported sent.
Migration overlay ownership never replaces live producer ownership. No H55
source-relation or final-theorem work was duplicated or edited.

A fresh thread must first reread this handoff, the unchanged frozen prompt,
owner tickets and all gate records, then continue the 4,134-declaration backlog
and supported-program/compiler/gas/fork obligations. Any registration requires
owner approval; a proposed optional test-library/map fragment is supplied in
`tests/h62/item2/audit-language/registration-fragment.md`, not applied.

## Artifact paths and trust boundary

All bulk data and compiler products are outside Git under
`/workspace/h62-audit-language-evidence/`:
`original.patch`, `handoff.json`, `SHA256SUMS`, `census-final/`,
`fidelity-final/`, `final-reviewed/`, both final blocker directories and
review/runtime/gate JSON logs. `export.py` regenerates the patch and checksum
manifest from the committed head. The manifest excludes extracted toolchain
contents (the verified original archive is hashed) and intermediate `.olean`
libraries; final checked source hashes and all proof logs remain included.

The census/ownership matching, source hashes and attack test are external
Python checks. Lean kernel checking establishes only the explicitly compiled
witnesses/ABI facts. No external EVM/solc equivalence, global compiler producer,
full success contract or uncompiled theorem is claimed. New source counts:
zero `sorry`, zero `axiom` declarations, zero `native_decide`, no raised proof
budget. Standard imported axioms are printed; telescope certificates use at
most `propext`. No merge, push, publish, PR or deployment was performed.
