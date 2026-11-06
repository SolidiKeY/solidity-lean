# H62 item 2 audit-roadmap — H69 continuation handoff

Batch `solidity-h62-2-20261106`, worker `audit-roadmap`.
Repository `/workspace/audit-roadmap`, branch
`codex/solidity-h62-2-20261106/audit-roadmap`, frozen base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The older clean `/workspace/solidity-lean` checkout remains on `work`.
Exact base was fetched and verified an ancestor of published origin/master.
All writes remain inside the three assigned audit prefixes. No original
interface, generated root, central map, axiom pin or proof budget was edited.
No push, merge, PR, pre-gate, publication or deployment.

## Current accounting

**17 checked theorem audits; 334 uncovered. Full assignment incomplete.**
All 351 source theorem declarations in all 46 frozen mapped files occur exactly
once in the generated census. Another 642 declaration candidates require
semantic classification, including proof-bearing definitions such as `Cert.comp`.
No complete elaborated telescope/structure-field census is claimed.

| Checkpoint | Saved evidence | Remaining |
|---|---|---|
| 1 frozen signatures and owners |46 mapped files,351 theorem source signatures,642 other candidates; source hashes; snapshot scope matches for every module |Elaborated telescopes, inherited-premise classification and exact live-owner confirmation |
| 2 simultaneous hypotheses |15 Evm mappings and2 Context mappings checked jointly;3 H69 controls explicitly classified |334 uncovered; all3 H69 impossibility checks blocked by unchanged Hash dependency |
| 3 totality/success and controls |3 checked Evm gas/observation/fork-depth boundaries; supported-constructor and generic compiler-control drafts |Production supported-program success/totality and complete compiler/failure/gas/fork coverage; drafts blocked |
| 4 fidelity census and validation |Hash-bound per-row report; deterministic reproduction; stale-evidence controls; independent finder/skeptic |All uncovered witnesses, semantic census, full affected gates and comparable timing |

Canonical off-git source inventory:
`/workspace/audit-roadmap-evidence/census/census.json`.
Canonical checked audit:
`/workspace/audit-roadmap-evidence/h69-audit/audit-census.json`.
Every row has its criterion, checked/uncovered status, original source signature,
proof reference where applicable, and source-import dependency blockers.

## H69 criterion resolution

Human authorization is saved verbatim in
`tests/h62/item2/audit-roadmap/h69-decision.txt`:

> for theorems whose hypotheses are contradictory on purpose (negative controls, separation lemmas, refutations), a checked Lean proof that the hypotheses cannot hold together IS the audit result for that theorem. Ordinary interface theorems still need a joint-satisfiability witness. Change no statement.

`SCOPE-NEG-01` / `Q-NEG-01` are resolved by this authorization. No question remains
pending. Proof checks remain separate obligations, not waived by that decision.

Historical escalation below is resolved by H69; it is not an active request:

ESCALATE: Solidity.Roadmap.PublicCorrectness.not_alwaysRevert — frozen Contracts.lean:1078–1083 concludes False from h : PublicCorrectness, hv : S.NonVacuous and hrev denying successful compiled runs. Options recorded before H69: (A) authorize a separate checked joint-impossibility criterion; (B) retain literal simultaneous witnesses and block. H69 explicitly authorizes A without changing the theorem.

`h69-classification.json` explicitly records names, intentional-control reasons
and unchanged impossibility-proof references. Exactly three declarations have
entire explicitly contradictory hypothesis worlds:

- `Solidity.Roadmap.PublicCorrectness.not_alwaysRevert`: public success contradicts universal success denial;
- `Solidity.Roadmap.Controls.toy_no_event`: assumed member of the toy's proven empty event list;
- `Solidity.Roadmap.Controls.toyEvm_no_event`: assumed member of the compiled toy's proven empty event list.

All three have additive joint-impossibility drafts in `tests/h62/item2/audit-roadmap/WitnessObstruction.lean`;
none has reached a successful pinned dependency check. Their status is uncovered.
The 44 other root refutation/separation results retain ordinary outer-world
witness requirements, plus their refutation proof references. Successful signed
negative values, bitwise NOT clients, inequalities inside positive conjunctions
and false Hoare success postconditions are not misclassified as impossible input
worlds. Source review or a theorem name never counts as a checked proof.

## Checked additive proofs

`tests/h62/item2/audit-roadmap/EvmWitnesses.lean` imports the unchanged `Solidity.Roadmap.Evm`. Its 15 indexed
wrappers jointly inhabit all inputs/premises of every frozen Evm theorem,
including Fixed structures, resource/order hypotheses and the full certificate
with a specified artifact, allowed environment and admissible resource in one
world. `witness-index.json` describes global versus per-input premises per row.
The certificate fixture is nonconstant but illustrative, not a real EVM model.
The nonempty hash witness uses a singleton and zero roots; root-interaction
coverage is not claimed.

Three additional checked controls show the exact Osaka transaction cap versus
its explicit pinned idealization, preserved/distinct failure observations, and
the Osaka P256/call-depth/stack boundaries. They are interface-boundary results,
not full compiler totality, intrinsic-gas accounting or transaction adequacy.
Two private lemmas support the collision/overlap witness. All20 Evm helper
lemmas checked;18 public axiom reports printed.

`tests/h62/item2/audit-roadmap/ContextWitnesses.lean` imports unchanged `Solidity.Automation.H28.Context`.
Both indexed theorems use one explicitly constructed nondefault Core.Context,
including budget/heartbeat/diagnostic fields. Those fields are witness data;
no proof-checking option or resource budget is increased. Both axiom reports
printed. Total checked helper theorems: 22 (including 2 private); indexed original
statement coverage: 17. Only standard `propext`, `Classical.choice`, `Quot.sound`
appear where needed; no new axiom/sorry/native_decide declaration.

Unverified drafts: 6 theorems in `tests/h62/item2/audit-roadmap/WitnessObstruction.lean`,1 in
`tests/h62/item2/audit-roadmap/FrontendWitnesses.lean`,3 in `tests/h62/item2/audit-roadmap/CreationWitnesses.lean`. The latter constructs
actual finite 105-byte constructor success and reject-all-return/always-revert
controls on published supported target code; it does not claim Source admission,
account installation, gas adequacy or compiler pipeline closure.

## Census and acceptance corrections

The generator reads original sources using `git show` at the frozen base.
It tracks namespace/section/mutual scopes, masks nested comments and strings,
distinguishes 11 private source aliases from generated elaborated names, and
retains section variables as context rather than claiming they are used binders.
Partial definitions and anonymous instances have explicit candidate/source IDs.

H69 re-review found that the old extractor treated result-type `let :=` as a
proof delimiter. Fixed and regression-tested:50 source signatures are now complete
through those lets; no original declaration was changed. Repair name/hash list:
`/workspace/audit-roadmap-evidence/signature-repairs.json`.
The superseded truncated census is retained only under
`/workspace/audit-roadmap-evidence/superseded/pre-h69-census`.
The canonical census and reproduction were regenerated and are byte-identical.
Six scanner acceptance tests pass, including nested comments/mutual scopes,
private/root/anonymous names, binder defaults, result-type lets, equation proofs
and fail-closed unterminated comments.

`audit_report.py` accepts a witness only with successful original/helper checks,
matching source hashes for its complete local import closure, an unchanged
compiler binary, the exact coordinator pin and verified official archive hash,
and printed helper axiom evidence without sorryAx/nonstandard axioms. Five
integration controls accept valid 17 coverage and reject stale dependency/helper
hashes, a failed check and a changed compiler. Synthetic negative records are
explicitly labelled test fixtures and never count as proof evidence.

Exact snapshot scope claims, including migration-overlay separation, are saved
in `/workspace/audit-roadmap-evidence/owner-snapshot-evidence.json`. In particular,
VX1 explicitly claims Contracts in the snapshot. Overlay scope never transfers
live ownership. Live owner fields remain unresolved until confirmed; no
original-file edit was attempted. No `relay.sh` was present. Owner tickets are
saved for the coordinator's normal retrieval; no unrelated messaging app used.

## Actual gates, commands and timings

Official archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`. No v4.24 cache used.
Tracked `lean-toolchain` stays unchanged; the explicit official binary is used.

Successful commands (prefix paths shown in full in results.json):

```sh
python3 scripts/h62/item2/audit-roadmap/serial_checks.py --lean /workspace/audit-roadmap-evidence/toolchain/official/lean-4.35.0-linux/bin/lean --output /workspace/audit-roadmap-evidence/lean-evm-h69-final --target evm
python3 scripts/h62/item2/audit-roadmap/serial_checks.py --lean /workspace/audit-roadmap-evidence/toolchain/official/lean-4.35.0-linux/bin/lean --output /workspace/audit-roadmap-evidence/lean-context-h69-final --target context
python3 -m unittest discover -s scripts/h62/item2/audit-roadmap -p test_census.py -v
python3 scripts/h62/item2/audit-roadmap/check_report_acceptance.py --evidence /workspace/audit-roadmap-evidence
```

All exit 0. Actual module commands, exact source/compiler/pin/archive hashes,
per-file wall times, logs and limits are in each run's `results.json`.
KeySort passes before each targeted run. The actual taclet comparison remains
blocked at Parser; KeySort compilation does not establish that comparison.
Prior static checks pass for 857 core modules (no reach to elaborator/checked
parser), generated roots and fragments. Existing doc-path check fails on the
optional missing Bridge/.lake/packages/mathlib/MathlibTest/SplitIfs.lean citation;
introduced audit paths are checked separately.

Four reproduced external-owner blockers, all in unchanged source:

| Ticket | File | Decisive pinned failure/evidence |
|---|---|---|
|DEP-HASH-01|Hash/CollisionBound|407 unsolved equality,660/680 omega; lean-audit/results.json |
|DEP-PARSER-01|SortCheck/Parser|76 missing String.trim; lean-pinned/results.json |
|DEP-RAW-01|Syntax/Raw|597/650/665/682String versus Slice mismatches; lean-frontend-h69/results.json |
|DEP-LINKING-01|Backend/Creation/Linking|109Disjoint simplification type mismatch; lean-creation-h69/results.json |

These result paths are under `/workspace/audit-roadmap-evidence`.
The source import graph places a known failed dependency on all 44 mapped modules
outside the two successfully audited modules. This is an import-path obstruction
census, not a Lean declaration dependency graph or proof of all future blockers.
Do not bypass it by copying interfaces, introducing shims, editing owners' files
or counting frozen proof text as checked. Owner-compatible overlays are needed.

Writer lock held for writes/Lean. One Lean process at a time,
`LEAN_NUM_THREADS=1`, explicit `-j1`, 300 s timeout, `--tstack=131072`, heap
`-M11264`; no swap observed. Hard address-space cap is min(12 GiB, host available
minus 4 GiB, cgroup remaining minus 4 GiB), minus 256 MiB margin. No systemd invocation.
The original admission-only reserve guard was corrected after review; old logs
remain historical evidence, not retroactive reserve certification.
No existing hot proof/representation was refactored. Comparable same-tree/cache/
resource before-after full timing remains pending; different targeted runs are
not a slowdown comparison. No RUNTIME_GATE_PASS, full affected validation,
full acceptance or full-assignment completion is claimed.

## Reviews and next thread

Independent finder and skeptic were read-only, used neither Lean/server nor
edits, and confirmed all17 same-input witness pairings and the H69 distinction.
Fixed their findings: result-type let truncation, stale imported-source evidence,
compiler/pin/archive binding, private/anonymous identities, proof-bearing
candidates, inferred-owner labelling, reserve-derived cap and version failure
handling. Final report acceptance controls pass; detailed reviews saved off git.

Five bounded subitems are finished: extraction repair, H69 classification,
Evm witnesses/boundaries, Context witnesses, evidence acceptance controls.
Fresh-thread continuation is handed to the coordinator on this SAME VM/branch
and SAME existing goal; do not self-launch or reset/create another goal.
The original full frozen objective remains binding, rendered prompt SHA256
`1f2f43a9089ad3fc56319ade15f7e99c83c1466170941c9c81c12defc4eadbf1`.
Environment ID:
`ccarenv_b64_Y2NhcmVudl9lNmE5OTQwMjI2ZDg4MTkxYmZhZGE0ZGM1MTYwNmYyZQ`.
get_goal is unavailable; coordinator explicitly permits that optional absence.

Next: obtain owner-compatible migration overlays, check the3 H69 impossibility
proofs, complete334 uncovered rows and642candidate classifications, confirm
live owners, finish supported-program totality/success and all required
failure/gas/fork controls, elaborated fidelity/axiom census, full affected gates
and timing/acceptance requirements. H55 implementation remains untouched.
Keep all four checkpoints and persistent objective unfinished while blocked.

Exports: `/workspace/audit-roadmap-evidence/original.patch`,
`/workspace/audit-roadmap-evidence/HANDOFF.md`,
`/workspace/audit-roadmap-evidence/SHA256SUMS`.
Full committed head is in external commit.json and CLOUDVM-RESULT to avoid a
self-referential hash. All H44 bulk evidence remains off git.
