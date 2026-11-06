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
605 candidates. Eighteen files / 51 declarations have no exact H30 reservation
in that snapshot: 13 `Frontend/Yul` files and five `Lowering/G19` files. H70 source
reconciliation now attributes their producers to VY1 (24 declarations) and V17
(27 declarations), respectively. The import-only `Frontend/Yul/Parsing.lean` is
also attributed. No missing H30 reservation or original-file edit permission is
created by that attribution; migration overlays retain separate owners.

| Checkpoint | State | Remaining obligations |
|---|---|---|
| 1. Frozen inventory and owner | partial | Elaborated signatures and exact implicit/premise closure; source producer attribution is complete, H30 gaps remain explicit |
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

## Initial checkpoint toolchain, prerequisites and failed gates

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
interfaces, retain the explicit H30 reservation gaps, then rerun the full mapped
prerequisite probe. Continue all four checkpoints; do not promote source hashes
or separate inhabitance facts to simultaneous witnesses.

The off-Git `handoff.json`, `original.patch`, `frozen-sources.tar.gz`, full evidence
logs and `SHA256SUMS` are exported in the evidence directory. The handoff records
the actual committed head and typed blockers. No registration fragment is needed
because no new Lean module was added. Required proof/final validation remains
outstanding; this is not RUNTIME_GATE_PASS or assignment completion.


## H70 routed follow-up: source owners and premise bundles

The H70 router reported acceptance of the saved tickets by migrate-backend,
migrate-bridge, migrate-frontend, migrate-hash, migrate-source, migrate-syntax and
migrate-yul. This is routing acknowledgement, not a delivered migration overlay
or a new passing gate. `relay.sh` is host-only; no VM installation is requested.
The exact original goal, base, branch, scope and frozen statements remain intact.

`owner-reconciliation.json` attributes all 18 files / 51 declarations missing
from the H30 glob snapshot. Each record binds the frozen file hash/count, an
exact-file integration commit ancestor of the base, a frozen producer document,
the existing registry producer ID (`P16` or `G19`) and the separately validated
migration reservation. The VY1 parser-boundary integration is
`89bad2b29005bcc99f720369c3bc1bfdd114f1fd`. V17 integration receipts explicitly
list both ConditionalSequence files and all three AssignmentReturnFlag/WhileBreak
files. Registry `G19` and the original user mapping select V17; V07 dependencies
do not transfer ownership. Reconciliation rejects an injected wrong producer.
All 656 source candidates have a producer attribution; `owner_unresolved=51`
continues to count missing H30 matches, while `producer_attribution_unresolved=0`
counts source-attribution coverage. Neither field grants write authority.

The additive census now stores a source premise bundle for every candidate:
1,914 written header binder groups with raw syntax/type text, source routing
hints, inferred-parameter markers, and the entire separate result expression.
Result-level quantification is flagged in 87 statements; it is never silently
promoted to a header assumption or treated as a hypothesis-free statement.
Inherited variable commands remain source provenance, not inferred implicit
closure. Global-context carriers, relation parameters, quantified law/function
bundles, indexed/structured certificates, per-input source conditions and opaque
arguments remain distinguished as source hints. Every type-kind, global
inhabitance, per-input feasibility, witness and elaborated fidelity state remains
pending. Opaque hints are not premise exclusions or completed classifications.

`source-bundle-reviews.json` adds ten signature-bound manual source inspections
and seven frozen definition excerpts. These specifically preserve:

- `BoolSlot`, `Parsed`/`Prepared`, `InstrShape` and `StateRepr` hidden proof fields;
- global `Glob` context versus concrete map/state/compiler/capacity premises;
- supplying the relation `R` versus the universally quantified `boolReflect` law;
- the same-state nonzero divisor and the per-input fixed hash query;
- the all-result-level inputs of RawIntegerInitialization.correct;
- the input-heap law versus the allocated-heap conclusion in allocated_supported;
- result-level lets and the non-control `True` branch of control_capacity;
- `Nonempty` on the conclusion side of parse_iff, which supplies no witness.

Those ten inspections are not a manual semantic review of all 656 statements.
No global structure was proved inhabited and no joint hypothesis bundle was
proved satisfiable. Source notes cannot certify a witness and reject stale
signature hashes. All 656 original identities, raw signatures, original H30
records and context hashes match the initial census exactly.

The finder independently checked all exact ownership paths, signature retention,
seven definition excerpts and ten source notes. The skeptic found two real bugs:
`:=` inside named arguments falsely looked like an equality condition, and live
producer attribution was not validated against registry P16/G19. Both were fixed;
regressions reproduce and reject the original counterexamples. Both reviewers
rechecked read-only, without Lean/server use, and reported no remaining confirmed
finding. Detailed records are appended to `reviews.md`.

H70 gates use the same unchanged frozen Lean sources; no Lean compilation was
repeated while waiting for the accepted migration owners. Required final proof
and runtime gates retain their prior failed/pending status. The new checks are:

- `python3 -B tests/h62/item2/audit-label-execution/test_census.py`: exit 0,
  fifteen tests; H70 evidence `h70-scanner-tests.log`.
- `census.py --ownership /workspace/h62-coordinator-inputs/ownership.json
  --owner-reconciliation tests/h62/item2/audit-label-execution/owner-reconciliation.json
  --source-reviews tests/h62/item2/audit-label-execution/source-bundle-reviews.json`:
  656 retained source rows, zero elaborated/witnessed rows; deterministic replay.
- `blocked_report.py` with that enriched census and the retained
  `final-map-probe/results.json`: exit 1, every candidate retains owner/source
  annotations and actual import blockers. No compilation-success claim.

Current exports live under
`/workspace/h62-audit-label-execution-evidence/h70/`, with a new full patch,
checkpoint delta, bundle, handoff and checksum manifest. The initial checkpoint's
exports remain preserved. Runtime slowdown measurement is still inapplicable:
there is no Lean implementation/refactor change or passing migration baseline.
Resume proofs and final gates only after authorized compatible overlays arrive;
the full four-checkpoint goal remains blocked, not complete.


## H70 partial Hash receipt and complete module source partition

The next routed message reports no current-owner delivery pending. Host relay
journals determine delivery acceptance; this does not establish owner agreement,
validation, or permission to modify original files. The supplied partial Hash
patch is retained off Git under `h70r2/incoming/`; its receipt is committed under
`tests/h62/item2/audit-label-execution/owner-overlays/`. Exact patch context spaces
are preserved, rather than altered to satisfy source-file whitespace checks.
Its SHA256 exactly matches
`3aebc61f1a1979d4e36d669e3c33f5ae8c848d38a3ca0574c62329bdc154bbff`.
The owner reported head `78c110f83dc1a30700acd1b5bd34b19f61da6ccd` and source head
`2a18afcdba00a85645b0b3079704f78ffcd78860`; those heads are reported identifiers,
not independently authenticated local commits.

`inspect_overlay.py` reconstructs the Hash postimage in memory only. It checks
exact frozen hunk contexts, the preimage/postimage Git blob indices and all 64
ordered named raw source signatures. The original blob is
`b54c93a5b24340a19160c1fb378d057ccee60f84`, and the reconstructed blob is
`092971eda8c7d6997276a92ba19b25b7ce05844e`. No original file was written, no overlay
was applied, and no Lean command or proof check was run. This inspects a dependency
and adds no statements to the 656-candidate denominator. Hash full migration and
Syntax.Raw remain pending, alongside the other exact dependency overlays.

Source census schema 3 now separately partitions leading result quantifiers.
There are 88 groups across 86 statements, containing 513 written binder groups,
in addition to the original 1,914 header binder groups. Source slices and offsets
are exact; dependent binder order is retained. Unbracketed inferred types remain
unknown. `∀ n ∈ byteQuery bytes, ...` remains one opaque bounded source prefix;
its implicit membership guard is not invented as a separate proved/assumed fact.
Implication chains and local lets stay in the remaining result. The remaining
nested quantifier in P6CalldataHash.source_target_clipped_hash is explicitly
retained. Result records are never merged into the header assumptions, and no
new inhabitance, feasibility or witness status is inferred.

All 147 mapped files also have source summaries with exact statement identity
lists, original hashes, header/result role hints, explicit unresolved obligations
and zero verified witnesses. Their lists account for all 656 statements exactly
once. Six files have no direct named theorem: HashBridge Frame/QueryCut,
LabelExec Fragment/Step, UnsignedDiv Data, and Frontend/Yul Parsing. Those files
may contain definitions or only imports; zero direct theorems says nothing about
imported-interface feasibility or structure inhabitance. The uncovered report
retains these 147 module records as well as all 656 statement records.

Twenty-six scanner/overlay regressions pass. The skeptic found two malformed
patches that the first inspector accepted: an out-of-range zero-count insertion
and contradictory deleted-file metadata. The inspector now permits only the
exact single-file header and positive in-range hunks, and rejects both cases.
Ordered signature lists also prevent duplicate-name collapse. Finder/skeptic
read-only rechecks confirmed the actual partial patch, all module/statement
counts, quantifier slices and pending proof boundaries. The finder caught a
stale intermediate census after a wording fix; final evidence is regenerated
from current code before hashing. Reviews used no Lean/server or writes.

Current exports are under
`/workspace/h62-audit-label-execution-evidence/h70r2/`. Deterministic generation:

```sh
python3 -B scripts/h62/item2/audit-label-execution/census.py \
  --ownership /workspace/h62-coordinator-inputs/ownership.json \
  --owner-reconciliation tests/h62/item2/audit-label-execution/owner-reconciliation.json \
  --source-reviews tests/h62/item2/audit-label-execution/source-bundle-reviews.json \
  --output /workspace/h62-audit-label-execution-evidence/h70r2/source-census.json
python3 -B scripts/h62/item2/audit-label-execution/inspect_overlay.py \
  --receipt tests/h62/item2/audit-label-execution/owner-overlays/hash-partial-receipt.json \
  --output /workspace/h62-audit-label-execution-evidence/h70r2/hash-overlay-inspection.json
python3 -B tests/h62/item2/audit-label-execution/test_census.py
```

The source generation/inspection and 26 tests pass; enriched blocked-report
checking still exits 1 against the retained failed pinned-toolchain import
results. Every elaborated-signature, global premise inhabitance, per-input
feasibility, simultaneous-witness, totality, negative-compiler, failure/gas/fork
and final Lean gate remains pending or blocked. No original statements, budgets,
roots, pins or intrinsic representations changed. No runtime slowdown claim is
possible without a passing migration baseline. This is a fresh handoff after
receipt inspection, result/module source partition and test/review work; the
coordinator retains the same VM, branch and original unfinished goal.
