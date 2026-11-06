# H62 item 2 audit-roadmap — blocked handoff

Batch `solidity-h62-2-20261106`, owner `audit-roadmap`.
Repository `/workspace/audit-roadmap`, assigned branch
`codex/solidity-h62-2-20261106/audit-roadmap`, exact base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The clean older `/workspace/solidity-lean` checkout on `work` was preserved.
Fetched exact base and published master; ancestry passes (off-git `setup.json`).
No push, merge, PR, pre-gate, publication, deployment or interface edit.

## Binding objective and status

All four checkpoints remain unfinished. This is a reviewable blocked backfill
checkpoint, not completion of the assignment or a runtime gate pass.
The original persistent goal remains the supplied full frozen assignment
(rendered prompt SHA256 `1f2f43a9089ad3fc56319ade15f7e99c83c1466170941c9c81c12defc4eadbf1`).
`get_goal` is not exposed among tools; coordinator explicitly permits continuing
without that optional inspection. No goal was created or reset.
Original VM/environment ID:
`ccarenv_b64_Y2NhcmVudl9lNmE5OTQwMjI2ZDg4MTkxYmZhZGE0ZGM1MTYwNmYyZQ`.

| Checkpoint | Evidence achieved | Remaining |
|---|---|---|
| 1 exact signatures and owners | 46/46 mapped files, 351 source theorem declarations exactly once; raw signatures and source hashes | Elaborated telescopes, global versus per-input hypotheses, exact-path owner evidence, proof-bearing definition classification |
| 2 simultaneous witnesses | Exact obstruction identified; four additive proof drafts | All 351 theorem rows remain uncovered; own proofs and axiom checks unverified; impossible literal witness requires scope decision |
| 3 totality/success | Draft generic reject-all exclusion, joint published toy success and explicit toy resource-failure boundary | Production supported programs, observable real failure/gas/fork boundary, comprehensive controls and proofs |
| 4 fidelity and verification | Independent lexical count and reproducible frozen census, no original statements edited | Kernel telescope comparison, all witness associations, full affected gates and owner resolution |

## Exact obstruction, without changing its statement

ESCALATE: Solidity.Roadmap.PublicCorrectness.not_alwaysRevert — frozen Contracts.lean:1078–1083 concludes False from h : PublicCorrectness, hv : S.NonVacuous and hrev denying every successful compiled run; h.succeeds hv supplies precisely such a run, so a simultaneous inhabitant is impossible. Options: (A) explicitly authorize a separate negative-control audit criterion proving joint unsatisfiability while preserving the theorem; (B) retain the literal simultaneous-witness criterion and keep checkpoint 2 blocked.

This is an intentional negative control, not a finding that the public contract
is defective or that the theorem should be weakened. No option is silently
selected or recommended. Stable question `Q-NEG-01` / ticket `SCOPE-NEG-01`.
The source-exact signature and its SHA256 are in
`tests/h62/item2/audit-roadmap/owner-tickets.json`.
No fresh premise, axiom, proof shortcut, changed exclusion or observation is used.

## Committed additions and external artifacts

The generator `scripts/h62/item2/audit-roadmap/census.py` reads **git show at the
frozen base**, not current edited source. Comments/strings are masked with offsets
preserved; namespaces, sections and mutual scopes are tracked. All theorem/lemma
declarations are retained, including ones with no explicit hypothesis binder.
11 private declarations have source aliases, visibility and null elaborated names.
Section-variable text is context, not a claim about actual used binders.
642 other declaration candidates include proof-bearing definitions such as
`Cert.comp`, partial definitions and anonymous instances, including binder-led forms (source-location IDs).
These candidates still need semantic classification. This source scan does not
claim a complete elaborated interface or structure-field census.
All 351 exact owner fields remain unresolved; family hints are separately labelled
candidates. The older ownership snapshot is not treated as current ownership proof.

Bulk outputs stay off git at `/workspace/audit-roadmap-evidence/census/census.json`.
Reproduction at `census-reproduction/census.json` is byte-identical.
The generator rejects an output directory inside this checkout.
The acceptance script covers nested comments/mutual scopes, private declarations,
root names, binder defaults containing `:=`, equation proofs, proof-definition
candidates, and unterminated comments failing closed. Five tests pass.

`tests/h62/item2/audit-roadmap/WitnessObstruction.lean` imports unchanged Controls.
Its four declarations are:

- `Solidity.H62.AuditRoadmap.no_simultaneous_not_alwaysRevert_witness`;
- `Solidity.H62.AuditRoadmap.reject_all_excluded`;
- `Solidity.H62.AuditRoadmap.toy_joint_success`;
- `Solidity.H62.AuditRoadmap.toy_failure_boundary`.

They are **unverified drafts** because unchanged migration dependencies fail first.
The toy control is not production compiler correctness or a real Osaka gas law.
New axiom/sorry/native_decide declarations: zero by source inspection; the kernel
axiom census remains pending. Registration is only a proposal fragment in tests;
generated roots, central module maps and axiom pins are untouched.

## Actual validation and blockers

Coordinator input hashes all match `/workspace/h62-coordinator-inputs/sha256.json`.
Official archive downloaded from the supplied pin URL, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
No v4.24 cache was used. Tracked `lean-toolchain` remains unchanged/read-only.
Actual compiler: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake
`5.0.0-src+eb6cafb (Lean version 4.35.0)`.

Runner command (first attempt, exit 1):

```sh
python3 scripts/h62/item2/audit-roadmap/serial_checks.py --lean /workspace/audit-roadmap-evidence/toolchain/official/lean-4.35.0-linux/bin/lean --output /workspace/audit-roadmap-evidence/lean-pinned
```

Decisive output: KeySort exit 0 (1.372 s), AST exit 0 (7.844 s), Annotations
exit 0 (1.483 s), Parser exit 1 (4.394 s): `String.trim` missing at Parser:76.
The actual taclet comparison did not run. Ticket `DEP-PARSER-01`; exact producer
key unresolved. No unauthorized edits or compatibility shims were made.

Unaffected audit dependency attempt (exit 1):

```sh
python3 scripts/h62/item2/audit-roadmap/serial_checks.py --lean /workspace/audit-roadmap-evidence/toolchain/official/lean-4.35.0-linux/bin/lean --output /workspace/audit-roadmap-evidence/lean-audit --target audit
```

KeySort exit 0 (1.624 s); Hash/CollisionBound exit 1 (4.585 s): unsolved equality
at line 407 and omega failures at 660/680. Ticket `DEP-HASH-01`; exact producer
key unresolved. The additive audit file and its `#print axioms` were not reached.
All commands, exit codes, logs, wall times and resource settings are in each
attempt's off-git `results.json`. Logs retain warnings and exact errors.

One Lean subprocess at a time, `LEAN_NUM_THREADS=1`, explicit `-j1`, 300 s timeout,
`--tstack=131072`, heap budget `-M11264`, no swap observed. Final runner bounds
address space by min(12 GiB, host available minus 4 GiB, cgroup available minus
4 GiB), with another 256 MiB margin; version failures abort. Writer lock held.
Initial attempt used the simpler admission-only reserve guard; independent
review identified and fixed it before the audit attempt. This correction does
not retroactively certify the first guard. Neither attempt approached its cap.
No systemd invocation or proof-budget increase.

No representation/refactor or existing proof edit occurred. Comparable same-tree,
same-cache, same-resources before/after full timing gate remains pending. The two
KeySort observations have different resource guards and are not a slowdown test.
No performance improvement or RUNTIME_GATE_PASS is claimed. Full `./run-lean.sh`,
all affected validation, passing taclet comparison, proof/axiom census and final
acceptance remain pending until external migration dependencies are supplied.

## Independent reviews and fixes

Finder and skeptic reviewed read-only, neither using Lean/server or making edits.
Both independently confirmed the impossible literal simultaneous witness and the
mathematical shape of all four draft helpers. Finder independently counted 351
actual theorem declarations in 46 files (raw regex 352 includes prose in Evm).
Fixed: mutual scope tracking; private source alias versus elaborated identity;
proof-bearing definition candidates including Cert.comp; partial/anonymous
candidate handling; inferred ownership separated from unresolved ownership;
resource cap preserving reserve; version-command failure handling. Five scanner
tests and deterministic reproduction pass. Review source findings are addressed;
mathematical inspection is not elaboration or completion.
Detailed reviews saved off git in `reviews.md`.

## Coordinator continuation

Owner tickets are saved for coordinator retrieval; no `relay.sh` was available
in this VM and no message was sent through an unrelated application. Tickets
request unchanged-statement compatible migration overlays only; they transfer no
producer ownership. H55 G49/G50 implementation was not duplicated.

Keep this exact VM, existing persistent goal and assigned branch. Obtain the
explicit negative-control criterion decision and external owner fixes for Parser
and CollisionBound; then rerun prerequisites and audit checks with the pinned
archive, finish elaborated census and per-statement simultaneous witnesses,
production success/totality/failure/gas/fork coverage, all owner associations and
required final gates. Supply approved registration fragments through coordinator.
Commit/export future checkpoints here. After 3–5 completed work items, relay a
fresh-thread handoff through coordinator; do not launch/reset another goal.

Exported patch `/workspace/audit-roadmap-evidence/original.patch`, external handoff
`/workspace/audit-roadmap-evidence/HANDOFF.md`, and checksum manifest
`/workspace/audit-roadmap-evidence/SHA256SUMS`. Full committed head is recorded in
external `commit.json` and the final CLOUDVM-RESULT (avoids self-referential hashes).
