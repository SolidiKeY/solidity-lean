# Duplicated proofs: size study

**Verdict: go for a small declaration macro; no-go for a repo-wide deletion
budget based on lexical clusters.** The pilot removes **687 physical lines**
(56.8%) from a 1,210-line slice, including its shared implementation cost.
It retains all **358** theorem names and their original sequents. This is
source compression, not fewer proof obligations or a generic soundness theorem.
A mechanical extension to the first twelve Derived files projects **789 lines**;
Later Derived modules include more matching declarations but fall outside this
projection; no larger saving is credited. The lane changes documentation and a pilot patch
only; the library is unchanged.

## Inventory and boundary

The [reachability summary](direction-tools/reachability/summary.json) measures
`d4ad633a9624263a59b14fd2c520b9bc602f88f3`: 2,743 normalized-statement
clusters and 88 near-file clusters / 26,599 lines. These are candidate footprints,
not duplicate semantic declarations or removable lines. The
[direction audit](direction.md#measurement-boundary-and-headline-facts) explains
numeric alpha-renaming, transitive clustering and lexical-reference limitations.

Filtering out every cluster containing Backend, Lowering or Yul/Views leaves
1,313 statement clusters and 27 near-file clusters / 8,408 lines. The three
largest remaining clusters are:

| Cluster | Frozen physical lines | Decision |
|---|---:|---|
| Yul shift checks Part00 / Part03 | 1,901 | Leave to the test-vector study; different input cases are not equal theorems |
| TestSuite Derived1–7, Derived9–10 | 1,188 | Pilot the repeated declaration shape |
| Frontend StatementGrammarH28 BoundaryHead / SyntaxHead | 748 | Distinct predicates; do not substitute one theorem for the other |

The pilot remeasures the second cluster at the assigned base
`772806909ec30c93a85a95c01130a70b6bcc83ca`; it still has 1,188 lines.
Its existing 22-line ScopedProblems dependency is included in both denominators.
The [reproducer](size-tools/duplicates/measure.py) checks the complete name list,
patch scope and source totals. Its optional inventory mode regenerates the frozen
cluster filter rather than silently assigning old counts to the newer base.

Reuse: [au.py](../../scripts/coord-tools/au.py) is the existing anti-unification
candidate finder (commit `8d6f160a8`); it is also present unchanged at the supplied
pilot reference `94f9862b6`, which is a merge commit. No standalone measured
t3-dedup rollout artifact is available in this checkout, so no saving from it
is imported. Running au.py on these nine files emits no candidates: its minimum
of fifteen constant tokens filters out the short declaration blocks. The batch
macro therefore uses an exact declaration pattern, not a claimed generic-lemma
pilot. The pending t3-dedup-rollout and t1-yul-views-generic work named in
[direction](direction.md#making-it-smaller), and the translation-validation
lanes named in [size reduction](size-reduction.md#area-studies), keep their scopes.
This pilot neither rolls out their abstractions nor repeats their compiler work.

## Ranked ideas

Only rank 1 has measured saving. Other rows are follow-up priority,
not a measured productivity ranking; their credited saving is zero. Effort is
an engineering estimate, excluding cold cache setup and downstream gate time.

| Rank / idea and mechanism | Files / expected saving | Measured net saving | Extrapolation | Effort | Theorem-strength risk | Go/no-go |
|---|---|---:|---|---|---|---|
| 1. Generate repeated declarations with a command macro; keep one explicit problem name per row | TestSuite Derived files; 789 lines across Derived1–12 | 687 lines | Exact shape count: 412 matching theorems; `2×412 − 2×12 − 11 = 789` lines | 2–4 h rollout | Low: expands to the same theorem and `sol_prove` invocation; inspect elaborated names/types | Go within this family |
| 2. Anti-unify proof bodies into parameterized lemmas | Evm MemoryCompile / MemoryFixedCompile / MemoryStorageCopyCompile `stmt_sound`; 564 candidate span lines | Unpiloted, 0 credited | At most 564 candidate lines; expected saving unknown until a common simulation relation is proved | 1–3 days feasibility | High: identically spelled local predicates need not be definitionally equal | Go only for a bounded second pilot; no rollout yet |
| 3. Reuse Theory lemmas and redirect equivalent consumers to a canonical proof | Evm compiler induction leaves and Theory; expected saving unknown | Unpiloted, 0 credited | No multiplier from 1,313 statement clusters: many are definitions with different bodies | 1–2 days inventory | Medium: preserve hypotheses, dependent indices and namespace resolution | Go for elaborated type comparison first |
| 4. Share induction over a description type, parameterizing the head predicate | Frontend StatementGrammarH28 BoundaryHead / SyntaxHead; 748 candidate lines | Unpiloted, 0 credited | 0–748 footprint ceiling, not a predicted gain; abstraction overhead must be included | 2–4 days | High: boundary-start and syntax-head claims differ | No-go until a common invariant is demonstrated |
| 5. Alias exact duplicate proofs, retaining every old public name | Same-statement candidates across Evm, Source and Semantics | Unpiloted, 0 credited | Unknown; exact elaborated types and acyclic imports required; aliases retain declaration overhead | 1–2 days feasibility | Medium: source normalization alone is insufficient | Go only for confirmed pairs |
| 6. Kernel-checked batch certificates / translation validation | Shift checks and compiler scenario families; expected saving owned by other lanes | Unpiloted here, 0 credited | No addition to this study's 789-line projection | Separate lane | High if finite checks replace universal statements or completeness is omitted | No-go in this lane; reuse their measured results |
| 7. Delete exact duplicates or apparently unused modules | The remaining near-file / lexical-unreached candidates | Unpiloted, 0 credited | Zero authorized theorem deletion; no-use scan is not a removal proof | Removal rebuild per family | Unacceptable if existing theorem names or claims disappear | No-go under this pilot's preservation requirement |

## Pilot and preservation

The [patch](size-tools/duplicates/pilot.patch) is below 1 MB and adds no module or
import edge. It adds an eleven-line macro to ScopedProblems and replaces repeated
three-line declaration blocks by one problem-name row in each of nine Derived
files. All 358 distinct obligations still run `sol_prove`; the macro does not
prove a conjunction, drop failing cases, replace problems or move a proof library
outside the counted slice. The source cost of every macro line is included.

| Metric | Before | After |
|---|---:|---:|
| Derived files, physical lines | 1,188 | 490 |
| Support file, physical lines | 22 | 33 |
| Total physical lines | 1,210 | 523 |
| Total UTF-8 bytes | 52,491 | 21,234 |
| Existing public theorem names | 358 | 358 |
| Lexical theorem/lemma/def/abbrev/macro headers | 358 | 1 |

The last row measures spelling only: the public theorems and their generated
auxiliary declarations remain. The baseline contains 716 kernel theorem
declarations and 564 support definitions; the final census also counts macro
helpers.
Timing and axiom validation are pending the matched serial measurement; no
runtime gate is claimed by these source totals.

## Execution proposal

1. Land the macro and the nine-file pilot only after its serial elaboration,
   original-sequent checks, axiom comparison and independent reviews pass.
   Preserve `Solkey.TestSuite.<problem>.proved : ⊢ <problem>.problem` for each
   of the 358 rows, with unchanged problem definitions and proof budgets.
2. Convert only the 54 exact matching declarations in Derived8, Derived11 and
   Derived12. Keep all exceptional proof bodies and every nonmatching theorem
   verbatim. This adds 102 projected saved lines (789 total); it is not measured
   elaboration coverage of those three files. Preserve each old theorem's type.
3. Re-run TestSuite's reporting/automatic-proof consumers and the required
   integration gates before any code rollout. The pilot patch alone authorizes
   no merge of library changes. No generated roots need updating for this patch.
4. Then consider one Evm anti-unification pilot, after comparing the actual
   local `stmt_sound` types and import closures. Preserve all three original
   simulation theorems; parameterize a common lemma only if it instantiates to
   each original statement without extra premises. Stop if abstraction overhead
   removes the gain or checking regresses. Do not use lexical clusters as proof
   that any theorem or module can be deleted.

## Reproduce

Use the pinned Lean toolchain on PATH, Python 3 with Linux `wait4`, and Git. Outputs must
be on disk outside the lane checkout. The script creates a fresh worktree at the exact
base and refuses to reset an existing directory. The runner makes `LAKE_CACHE_DIR` explicit (caller override or toolchain-local
cache). Cache setup is outside timed runs; a cache miss is compiled, never counted as a passing check.

```sh
python3 -B docs/audits/size-tools/duplicates/measure.py --out /workspace/duplicates-source
python3 -B docs/audits/size-tools/duplicates/measure.py --out /workspace/duplicates-check --lean
python3 -B docs/audits/size-tools/duplicates/measure.py --out /workspace/duplicates-inventory --inventory
python3 -B docs/audits/size-tools/duplicates/measure.py --summarize /workspace/duplicates-check/measurement.json
```

All Lean runs use `LEAN_NUM_THREADS=1`; forced per-file checks pass `-j1` and
`--tstack=131072`. Three complete serial repetitions include the support file;
peak RSS is Linux `wait4`’s maximum-process resident high-water mark, not aggregate
VM or process-tree RSS. Ordered before/after runs retain filesystem-cache drift;
small timing differences are not evidence of a speedup. Fetched artifacts are
materialized with the repository restore script; restored output hard links are
detached before compilation. The runner also checks every old sequent and compares all transitive axiom
reports. These are proofs about the repository's intrinsic model; neither the
macro nor an external solc test proves deployed-EVM conformance.

Limitations: no systemd scope on the cloud VM (H232); the VM has no swap.
A fetched cache from an older master needs matching imports rebuilt. The missing
portable earlier-pilot result does not support a saving estimate. This is a
single regular declaration family, not a representative sample of arbitrary
semantic proof duplication; the 789-line projection must not be scaled to the
26,599-line inventory.
