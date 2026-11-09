# Duplicated proofs: size study

**Verdict: GO for a declaration macro plus its source-scanner adapter; NO-GO
for a repository-wide deletion budget inferred from lexical clusters.** The
compatible pilot saves **679 net lines**: 1,419 → 740 (47.9%), including shared
macro and scanner costs. UTF-8 source bytes fall 62,451 → 31,628 (49.4%). All
**358 public theorem names and original sequents** remain proved. This compresses
source; it removes no proof obligations or kernel theorem declarations.
A mechanical extension to Derived1–12 projects **781 net lines**; later Derived
modules are excluded, and no larger saving is credited. This lane commits only
the study and reproduction tools; library and scanner changes remain patches.

## Inventory and reuse

The [reachability summary](direction-tools/reachability/summary.json) measures
`d4ad633a9624263a59b14fd2c520b9bc602f88f3`: 2,743 normalized-statement
clusters and 88 near-file clusters / 26,599 lines. These are candidate footprints,
not equivalent theorems or removable lines. The
[direction audit](direction.md#measurement-boundary-and-headline-facts) explains
numeric alpha-renaming, transitive clustering and lexical-reference limitations.

Excluding every cluster containing Backend, Lowering or Yul/Views leaves
1,313 statement clusters and 27 near-file clusters / 8,408 lines. The three
largest remaining clusters are:

| Cluster | Frozen physical lines | Decision |
|---|---:|---|
| Yul shift checks Part00 / Part03 | 1,901 | Leave to the test-vector lane; distinct input cases are not equal theorems |
| TestSuite Derived1–7, Derived9–10 | 1,188 | Pilot the repeated declaration shape |
| Frontend StatementGrammarH28 BoundaryHead / SyntaxHead | 748 | Distinct predicates; no direct theorem substitution |

The second cluster still has 1,188 lines at the assigned pilot base
`772806909ec30c93a85a95c01130a70b6bcc83ca`. The changed support file and
scanner are included in the measured denominator. The [reproducer](size-tools/duplicates/measure.py)
regenerates the frozen inventory separately from current-base pilot counts.

Reuse: [au.py](../../scripts/coord-tools/au.py) is the existing anti-unification
finder (`8d6f160a8`), unchanged at supplied reference `94f9862b6`, a merge commit.
It emits no candidates on this short family: its fifteen-constant-token minimum
filters out these declaration blocks. This pilot uses an exact declaration
pattern. No standalone measured t3 rollout artifact is available in the checkout;
no saving from it is imported. Pending t3-dedup-rollout and t1-yul-views-generic
work named in [direction](direction.md#making-it-smaller), and the translation
validation lanes in [size reduction](size-reduction.md#area-studies), retain their
scopes; this pilot does not repeat their compiler or layout abstractions.

## Ranked ideas

Only rank 1 has measured saving. Other rows are follow-up priority, not measured
productivity; their credited saving is zero. Effort estimates exclude cold cache
setup and downstream gates. Candidate ceilings are not expected deletions.

| Rank / mechanism | Files / expected saving | Measured net saving | Extrapolation | Effort | Strength risk | Go/no-go |
|---|---|---:|---|---|---|---|
| 1. Generate repeated declarations; enumerate each problem once, preserving the scanner's proof records | TestSuite Derived files plus scanner | **679 lines**, including 8-line adapter | 412 matching declarations in Derived1–12: `2×412 − 2×12 − 11 − 8 = 781` lines | 2–4 h rollout | Low: same names, sequents and `sol_prove`; malformed rows rejected | **Go as a coupled change** |
| 2. Anti-unify bodies into parameterized lemmas | Evm MemoryCompile / MemoryFixedCompile / MemoryStorageCopyCompile `stmt_sound`; expected gain unknown | Unpiloted, 0 credited | At most 564 candidate span lines; first prove a common simulation relation | 1–3 days feasibility | High: local predicates with the same spelling can differ | Go for one bounded pilot; no rollout yet |
| 3. Reuse Theory lemmas and redirect equivalent consumers | Evm compiler induction leaves and Theory; expected gain unknown | Unpiloted, 0 credited | No multiplier from 1,313 statement clusters: definitions can have different bodies | 1–2 days inventory | Medium: preserve dependent indices, hypotheses and acyclic imports | Go for elaborated type comparison first |
| 4. Share an induction over a description type, parameterizing the head predicate | Frontend StatementGrammarH28 BoundaryHead / SyntaxHead | Unpiloted, 0 credited | 0–748 footprint ceiling; count abstraction overhead before predicting gain | 2–4 days | High: boundary-start and syntax-head claims differ | No-go until a common invariant is demonstrated |
| 5. Alias exact duplicate proofs, retaining every public name | Same-statement candidates across Evm, Source and Semantics | Unpiloted, 0 credited | Unknown; exact elaborated types required, aliases retain declaration overhead | 1–2 days feasibility | Medium: source normalization is insufficient | Go only for confirmed pairs |
| 6. Kernel-checked certificates / translation validation | Shift checks and compiler scenario families | Unpiloted here, 0 credited | Owned by other lanes; nothing added to this study's 781-line projection | Separate lane | High if finite checks replace universal claims or completeness is omitted | No-go in this lane; reuse their measurements |
| 7. Delete exact duplicates or apparently unused modules | Remaining near-file / lexical-unreached candidates | Unpiloted, 0 credited | Zero authorized theorem deletion; absence of lexical uses is not a removal proof | Removal rebuild per family | Unacceptable if names or claims disappear | No-go under the preservation requirement |

## Pilot results and preservation

The [Lean patch](size-tools/duplicates/pilot.patch) adds an eleven-line macro to
ScopedProblems and replaces repeated declaration blocks in nine Derived files.
Every listed obligation still runs `sol_prove`; problem definitions, imports,
file splits and proof budgets are unchanged. The existing `decl` table and its
separate support module retain the timing boundary described in their comments.
No module is added, so generated roots need no changes.

The existing source scanner would see **0** of the 358 batched declarations.
The [eight-line adapter](size-tools/duplicates/consumer.patch) restores all 358
original records exactly, including body and option classification. Its tests
reject empty and manual rows. It changes no Lean input; the compatibility
profile checks this explicitly. Ship both patches together.

| Metric | Before | After |
|---|---:|---:|
| Derived files, physical lines | 1,188 | 490 |
| Support file, physical lines | 22 | 33 |
| Lean subtotal, physical lines | 1,210 | 523 |
| Source scanner, physical lines | 209 | 217 |
| All changed source, physical lines | **1,419** | **740** |
| All changed source, UTF-8 bytes | **62,451** | **31,628** |
| Existing public theorem names | 358 | 358 |
| Kernel theorem declarations, including auxiliaries | 716 | 716 |
| All kernel constants in the ten Lean modules | 1,280 | 1,282 |
| Lexical Lean theorem/lemma/def/abbrev/macro headers | 358 | 1 |
| Serial forced Lean checks, seconds per repetition | 286.9 / 283.3 / 286.0 | 284.0 / 284.5 / 284.9 |
| Median seconds | **286.0** | **284.5** |
| Maximum-process RSS, MiB | **5,092.6** | **5,102.4** |

The macro adds two support definitions; kernel theorem count does not shrink.
Its 687-line Lean saving minus the 8-line scanner cost yields **679 net lines**.
Likewise, 31,257 Lean bytes minus 434 scanner bytes yields **30,823 net bytes**.
Timing differences lie within the observed run variation; no speedup is credited.

All ten edited Lean files passed per-file MCP diagnostics. Three forced serial
checks of every file passed on each variant. An additional audit checks every
original sequent and compares all 358 transitive axiom sets: each is exactly
`propext`, `Classical.choice`, `Quot.sound` on both variants. No new axiom,
`sorry`, `native_decide` or heartbeat increase is introduced. The timing table
covers the ten Lean files, not cache setup, the extra axiom audit or Node checks.
Node scanner parity is external validation; it is not a replacement for a proof.
These proofs concern the intrinsic model, not deployed-EVM conformance.

## Execution proposal

1. Apply the macro and scanner adapter together. Preserve each
   `Solkey.TestSuite.<problem>.proved : ⊢ <problem>.problem` and its original
   automatic-proof record. Keep problem definitions and proof budgets unchanged.
2. Convert only the 54 exact matches in Derived8, Derived11 and Derived12;
   retain any exceptional bodies verbatim. This projects 102 further saved lines
   (781 net total, adapter counted once). Those three files have not been
   elaborated with the macro in this pilot; validate them before rollout.
3. Run TestSuite reporting, the automatic-proof consumer tests and all required
   integration gates before merging code. This investigation authorizes no code
   merge. Re-measure net savings if consumer or generator changes grow.
4. Next, consider one Evm anti-unification pilot after comparing the three actual
   `stmt_sound` types and import closures. Preserve each original simulation
   theorem without extra premises; count shared-lemma overhead and stop if
   checking regresses or the abstraction removes the saving. Lexical clusters
   never justify deleting a theorem or module.

## Reproduce

Use pinned Lean/Lake on PATH, Python 3 with Linux `wait4`, Node and Git. Outputs
must be on disk outside the lane checkout. A fresh worktree is created at the
exact base; existing trees are never reset. Each patch is below 1 MB.

```sh
python3 -B docs/audits/size-tools/duplicates/measure.py --out /workspace/duplicates-check --lean
python3 -B docs/audits/size-tools/duplicates/measure.py --out /workspace/duplicates-compatible --consumer --inventory
python3 -B docs/audits/size-tools/duplicates/measure.py --summarize /workspace/duplicates-check/measurement.json
```

Measured toolchain: Lean **4.24.0**, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake **5.0.0-src+797c613**. `LAKE_CACHE_DIR` is explicit (caller override or
resolved toolchain-local cache). Cache fetch/build and the repository artifact
restore run outside timing; restored output hard links are detached before
compilation. The measured run used the already-fetched cache (`--skip-cache`).
Lean uses `LEAN_NUM_THREADS=1`, `-j1`, `--tstack=131072`. Wall time uses
`perf_counter`; Linux `wait4.ru_maxrss` reports maximum-process RSS, not aggregate
VM/tree RSS. Three complete repetitions include support-file elaboration.
Ordered before/after runs retain filesystem-cache drift, so small differences
are not evidence of speedup.

Limitations: **no systemd scope on the cloud VM (H232)**; no swap. A single regular
declaration family does not represent arbitrary semantic duplication. The
781-line projection must not be scaled to the 26,599-line candidate footprint.
