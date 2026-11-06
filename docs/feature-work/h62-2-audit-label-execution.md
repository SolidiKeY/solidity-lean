# H62 item 2: label-execution empty-statement audit

Status: **BLOCKED; none of the four audit checkpoints is complete.** This is a
reviewable tooling/backfill checkpoint with concrete migration-owner tickets.
The persistent assignment must resume after compatible owner overlays arrive.

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-2-20261106/audit-label-execution`.
Repository: `/workspace/solidity-lean`.
The exported handoff records the full committed head; no push/merge/PR occurred.

## Scope and current census

The frozen `docs/module-map/label-execution.md` expands to 147 files, including
its Bridge, Yul, Frontend and lowering entries. There are 656 named source
candidates: 620 public and 36 private helpers. All remain accounted for exactly
once by `(path, textual qualified name)`; private kernel names need elaboration.
No textual hypothesis filter silently excludes a statement or control.

The scanner compares the map and every module byte-for-byte against its Git
blob at the frozen base. It retains exact raw source signatures, signature
hashes, full-prefix hashes and preceding variable command text. Eight result-type
`let` signatures were repaired after independent review. These are source-level
records, **not exact elaborated signatures**: section binders, implicit parameters,
Prop/data classification and global-versus-per-input feasibility remain pending.
The supplied ownership snapshot provides unique H30 reservation evidence for
605 candidates. Eighteen files / 51 declarations have no exact reservation in
that snapshot: 13 `Frontend/Yul` files and five `Lowering/G19` files. No ownership
was assumed or transferred.

| Checkpoint | State | Remaining obligations |
|---|---|---|
| 1. Frozen inventory and owner | partial | Elaborated signatures, exact missing ownership and premise classification |
| 2. Simultaneous hypothesis witnesses | blocked | Every required witness; zero checked witnesses |
| 3. Meaningful success/totality | blocked | Supported-program success and reject-all/always-revert controls; actual failure/gas/fork observation boundaries |
| 4. Fidelity and witness census | blocked | All elaborated-type/witness checks and full final gates |

No frozen statement was changed. No theorem was proved weakened or vacuous in
this checkpoint, so there is no theorem-vacuity ESCALATE claim. Compilation
failures are dependency blockers, not nonvacuity evidence.

## Reproducible tooling

- `scripts/h62/item2/audit-label-execution/census.py`: deterministic frozen
  source census; bulk JSON stays off Git.
- `scripts/h62/item2/audit-label-execution/serial_probe.py`: explicitly serial
  per-file import prerequisite probe; official sysroot and tracked Bridge vendor
  roots are resolved. It never patches dependencies or certifies proofs.
- `scripts/h62/item2/audit-label-execution/blocked_report.py`: joins every source
  candidate to root import blockers. Repeated graph traversal is cached; the
  initial uncached reporting process was stopped and superseded. A successful
  report-generation/import exit never certifies premise satisfiability.
- `tests/h62/item2/audit-label-execution/test_census.py`: six scanner regression
  tests, including frozen-source mutation and all eight real result-let cases.
- `tests/h62/item2/audit-label-execution/owner-tickets.json`: six exact-file
  migration failures plus a Bridge provisioning ticket, addressed to migration
  owners for coordinator retrieval. Live producer ownership remains unchanged.
- `tests/h62/item2/audit-label-execution/reviews.md`: independent finder/skeptic
  findings, fixes, commands and explicit review boundaries.

## Toolchain, prerequisites and failed gates

All five coordinator inputs passed their supplied SHA256 manifest. The official
`lean-4.35.0-linux.tar.zst` archive passed SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual tools: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release;
Lake 5.0.0-src+eb6cafb (Lean 4.35.0).

All paths below are under `/workspace/h62-audit-label-execution-evidence`.
Commands run from the repository; the full binary path is
`/workspace/h62-audit-label-execution-evidence/toolchain/lean-4.35.0-linux/bin/lean`.

| Command | Outcome | Evidence |
|---|---|---|
| `git fetch origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4`; `git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master` | exit 0; exact published base verified; clean checkout preserved | exported setup record |
| Pinned `lean --version`; `lake --version` | versions above | toolchain verification |
| Pinned `lean -j1 --tstack=131072 Solidity/KeySort.lean`, under writer lock, `LEAN_NUM_THREADS=1`, `ulimit -v 12582912`, bash `time` | exit 0; 1.067s elapsed | `keysort-v435.log` |
| `python3 -B tests/h62/item2/audit-label-execution/test_census.py` | exit 0; six tests OK | `scanner-tests.log` |
| `python3 -B scripts/h62/item2/audit-label-execution/census.py --ownership /workspace/h62-coordinator-inputs/ownership.json --output /workspace/h62-audit-label-execution-evidence/census.json` | exit 0; 147 files / 656 candidates | `census.json` |
| `python3 -B scripts/h62/item2/audit-label-execution/serial_probe.py --lean /workspace/h62-audit-label-execution-evidence/toolchain/lean-4.35.0-linux/bin/lean --evidence /workspace/h62-audit-label-execution-evidence/final-map-probe --census /workspace/h62-audit-label-execution-evidence/census.json` | exit 1; all 147 mapped imports blocked | `final-map-probe/results.json`, per-module logs |
| `python3 -B scripts/h62/item2/audit-label-execution/blocked_report.py --census /workspace/h62-audit-label-execution-evidence/census.json --probe /workspace/h62-audit-label-execution-evidence/final-map-probe/results.json --output /workspace/h62-audit-label-execution-evidence/uncovered.json` | exit 1; 656 candidates uncovered / zero witnesses | `import-coverage-gate.log`, `uncovered.json` |
| `./run-lean.sh`, Bridge full gates and actual witness checks | pending; blocked before eligible final validation | owner tickets |

The final probe covers 738 closure modules: 39 pass, six direct compile failures,
693 blocked. Only official v4.35 sysroot artifacts and newly generated v4.35
outputs were consumed; the v4.24 master cache was not reused. The six failures:

- `Syntax/Raw.lean:597` and `:665`: application type mismatches.
- `Hash/CollisionBound.lean:407` and `:660`: unsolved proof goals.
- `Backend/Scalar/Slice.lean:303`: frozen axiom-message guard expects no axioms
  for `Scalar.ternary`; v4.35 reports `[propext]`.
- `Source/Ctor.lean:641` and `:715`: simplification/dependent-elimination failure.
- `Yul/ReservedNames.lean:43`: existing recursion budget exhausted.
- `Frontend/Checked/Token.lean:38`: changed String constructor API.

The Bridge manifest still pins v4.24 packages; provisioned v4.35 package overlays
are required. Tracked `Bridge/vendor` sources were resolved, rather than reported
as missing. Earlier `independent-probe/` and `full-map-probe/` are superseded
historical diagnostics. The early Lake diagnostic is not a final gate.

Final per-file checks held the repository writer lock, ran exactly one Lean
child at a time with `LEAN_NUM_THREADS=1`, `-j1`, 12 GiB address-space cap, a 4 GiB
cgroup reserve checked before/during spawning, and no swap. The VM cap was 16
GiB; observed peak Lean RSS 1,551,572,992 bytes; zero resource stops. Total
completed compilation elapsed sum was 86.377s. No systemd-run or proof-budget
increase was used. No meaningful before/after proof-performance delta exists:
the unchanged frozen dependencies do not pass the required toolchain, and this
checkpoint adds no Lean implementation or refactor. No slowdown claim is made.

## Proof and observation boundaries

There are zero new Lean declarations, sorrys, axioms or native_decide calls.
Failed elaboration logs can contain Lean error-recovery `sorryAx`; none is
accepted as a proof or consumed by a downstream audit witness.

The existing `LabelExec/Step.lean` slice explicitly excludes gas and EVM error
classification, and `Transient/Instructions.lean` excludes gas/stack/call-depth
correspondence. Those limitations remain frozen. Scanner negative controls test
report integrity only; they do not satisfy public compiler negative-control or
execution-observation obligations. No external differential test, gas/fork
boundary, totality theorem or simultaneous witness has been claimed.

## Resume and handoff

The local coordinator retrieves committed artifacts on this VM; no relay script
was discovered or external owner message sent. Deliver the saved owner tickets,
obtain compatible authorized migration overlays without changing frozen
interfaces, establish the missing owner reservations, then rerun the full mapped
prerequisite probe. Continue all four checkpoints; do not promote source hashes
or separate inhabitance facts to simultaneous witnesses.

The off-Git `handoff.json`, `original.patch`, `frozen-sources.tar.gz`, full evidence
logs and `SHA256SUMS` are exported in the evidence directory. The handoff records
the actual committed head and typed blockers. No registration fragment is needed
because no new Lean module was added. Required proof/final validation remains
outstanding; this is not RUNTIME_GATE_PASS or assignment completion.
