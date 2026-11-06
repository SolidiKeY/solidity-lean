# Architecture and code audit (2026-11-06)

Read-only audit of `solidity-lean` at base `c0228e0e` (lane
`cloud/audit-20261106/architecture`). No file outside `docs/audits/` was
changed. Every number below comes from a command listed in "Method"; the
scripts are in [`architecture-tools/`](architecture-tools/).

## 1. Verdict

The intrinsic core the docs describe (Syntax → Semantics → Theory → Calculus,
about 1,000 modules) is in good order: no module is unreachable from a root,
the core reaches no elaborator, docs cite almost no missing code, and the
proofs use no `native_decide`. The debt is in the **compiler side**, which
now holds most of the package (Backend 1,932 modules, Yul 1,776, Lowering
662, Evm 277: 4,647 of 6,454 modules, 598k of 1.08M lines). It is grown
**by copying per case**: 144 files are exact copies of one another up to
consistent renaming, seven EVM fragment compilers each redefine the same
fragment relation, fifteen Yul compilation files each declare their own
`Artifact`, and 207 `Yul.Views` modules form one serial import chain, the
longest in the package. Test fixtures (`*Controls`) have become
dependencies: 778 library modules import one transitively. The stated
layering is not what is checked: `docs/parallelism.md` says the core is
closed under imports, but 95 core imports leave it and its closure pulls in
398 compiler-side modules. Finally, the sanctioned cache seed silently fails
on cloud VMs, and once it works the per-file gate fails until a CI-only
restore step is run. The highest payoff for the least risk is in the
tooling (findings 1, 4) and in generic interfaces for the copied families
(2, 5, 6); renaming the `Roadmap`/milestone namespaces (7) pays but is the
riskiest.

## 2. Method

All commands from the repository root at `c0228e0e`, on a 4-core, 15 GB VM.

| What | Command | Sample |
|---|---|---|
| Sizes per area | `find Solidity/<area> -name '*.lean' \| xargs cat \| wc -l` | all 7,592 `.lean` files (6,454 modules in the import graph incl. `Bridge/SolidityBridge`) |
| Import graph, area matrix, roots, orphans | `python3 -I docs/audits/architecture-tools/imports.py {areas,roots,unreached,edges}` | every `import` line |
| Core closure | `python3 -I docs/audits/architecture-tools/core_closure.py -v` (reads `CORE`/`ELABORATOR` from `scripts/check-layers.mjs`) | 859 core modules |
| Fan-out, longest chain | `node scripts/import-fanout.mjs [--chain]` | whole graph |
| Duplicate statements | `python3 -I docs/audits/architecture-tools/dup_decls.py` and `dup_general.py` (statement text from name to top-level `:=`, whitespace/comments normalised, SHA-1) | 76,431 declarations with a statement ≥ 40 chars; 28,271 "general" theorems |
| Renamed copies of files | `python3 -I docs/audits/architecture-tools/near_files.py 0.8 300` (identifiers alpha-renamed by first occurrence, 10-token shingles, MinHash LSH, exact Jaccard check) | 5,892 files ≥ 300 tokens |
| Unreferenced declarations | `python3 -I docs/audits/architecture-tools/unreferenced.py` (last name component counted over `.lean/.md/.mjs/.py/.sh/.json`) | 106,971 declarations |
| Docs citing missing code | `bash scripts/check-doc-paths.sh`; `python3 -I docs/audits/architecture-tools/doc_names.py` | 2,190 dotted names in `docs/*.md` |
| Olean bytes per area | `python3 -I docs/audits/architecture-tools/olean_sizes.py <lake cache>` (trace `outputs.o` → artifact) | 6,443 modules, 5.60 GB |
| Gate | `./run-lean.sh` after seeding the cache | 6,461 jobs |
| Per-file elaboration | `scripts/coord-tools/gate.sh per-file` on a seeded random sample (seed 20261106) of 30 `*Controls` and 30 library files; then each again as an import-only copy, timed with bash `time` | 60 + 60 runs |
| Skeptic | one read-only agent (no Lean server) tried to refute each finding | §5 of each finding, and §6 |

Cache: `fetch-lake-cache.sh` failed on this VM (finding 4). The pack was
installed by running its own `install.sh` with `elan which` resolved from the
repository (a shim on `PATH`; `LAKE_CACHE_DIR` not set), then
`restore-lake-artifacts.py` placed 12,892 files.

## 3. Top 10

| Rank | Finding | Evidence | Estimated payoff | Effort | Risk |
|---|---|---|---|---|---|
| 1 | The "core" is not closed under imports, contrary to `docs/parallelism.md` P1; the checker never tests closure | 95 direct core→non-core imports; closure adds 398 modules / 86,664 lines (115 Backend, 109 Evm); doc says 123 core modules, checker matches 859 | Restores the property P1 relies on (a compiler edit rebuilding the calculus); stops a silent drift that grows each lane | S (report) / M (fix 95 edges) | Low |
| 2 | `Yul/Views` is a 868-file directory of renamed copies on one serial chain | 207 of the 212 modules of the longest import chain; 144 files in 49 exact alpha-renamed groups, 137 of 202 near-copy files | Cold-build critical path; ~6k lines of `*Ownership*` collapse to ~1k; one fix instead of 7 | M | Medium |
| 3 | Test fixtures are dependencies, and cost ~28% of elaboration CPU | 394 edges library→Controls; 778 library modules depend on a Controls module; `Roadmap` (core) imports Backend Controls; Controls elaborate at 8.4 s/kline vs 4.5 (sample of 30+30) | Controls editable/deletable without rebuilding the compiler; ~0.6 CPU-h per cold build if halved | M | Low |
| 4 | The cache seed silently fails on cloud VMs, and the per-file gate needs a CI-only restore step | `install.sh` → `elan which lean` panics "no active toolchain"; per-file gate 59/60 FAIL ("object file … does not exist") until `restore-lake-artifacts.py`; 60/60 PASS after | Every cloud lane: cold build (~24 min, `lean-lsp` instructions) instead of seconds; per-file gate usable | S | Low |
| 5 | Seven EVM fragment compilers redefine the same fragment relation | 7 × `inductive StmtFrag`/`ProgFrag` over `Stmt C Γ Δ` in `Evm/Memory*Compile.lean` (3,615 lines); `ProgFrag.pushes_zero` ×7, private `run_cons_revert` ×7; Evm is 97 of 485 redundant lemma copies | A new memory feature is one constructor, not an eighth file; ~1–2k lines | M–L | Medium |
| 6 | Yul compilation correctness is restated per statement shape | 15 `structure Artifact`; `Artifact.source_to_model`, `normal_to_model` with identical statements in 10 files each; 42 redundant copies in `Yul/Compilation` | One interface theorem, consumers stop depending on a shape file | M | Medium |
| 7 | Project-history names are foundations: `Roadmap.*` types and milestone-tagged modules | `Roadmap.Pipeline` 3,671 uses, `Roadmap.Word` 1,733; `Roadmap.Contracts` 3,423 dependents; `Yul/Words.lean:15` `abbrev Word := Solidity.Roadmap.Word`; 846 module paths with V07/P8/G18/H24/V3 tags | Readability, onboarding; names stop lying when milestones close | L | High (rename churn, merge conflicts with live lanes) |
| 8 | P2's size limit is not enforced | 20 files > 1,800 lines (max 3,977); `Source/Horizon.lean` 2,305 lines → largest olean, 95 MB | Worker memory, re-check size | S each | Low |
| 9 | Duplicated general lemmas, many private | 340 groups, 485 redundant copies, 177 private; Yul/Views 128, Evm 97, Yul/Compilation 42 | Fewer places to fix; mostly falls out of 2, 5, 6 | S–M | Low |
| 10 | Unreferenced library declarations | 1,553 library theorems (5%) never named elsewhere, 803 in Yul | Small; candidates for deletion after review | S | Low |

## 4. Findings

### 1. The core is not closed under imports

**Evidence.** `docs/parallelism.md` P1: "The list is closed under imports: no
core module imports a module outside it", and under P2, "123 modules now".
`scripts/check-layers.mjs:14-169` has 174 patterns matching 859 modules;
it checks only that core reaches no elaborator (`:205-226`), never closure.
`core_closure.py -v`:

```
CORE patterns: 174; modules matched: 859
direct core -> non-core imports: 95
  into Source: 30, Backend: 29, Yul: 11, Calculus: 10, Lowering: 6, Frontend: 3, Syntax: 2, Evm: 2, Language: 1, Stipend: 1
transitive closure of core: 1257 modules; 398 non-core, 86664 lines
  non-core in closure by area: Backend 115, Evm 109, Yul 56, Source 55, Lowering 40, Calculus 11, …
```

Representative edges (from the `-v` list): `Semantics.Nondeterminism.SourceWitness → Source.SemanticsExamples`
(a core module importing an examples module); `Theory.Progress.Program → Lowering.P9.FunctionCatalog`
(the data-structure Theory depends on a lowering pass); `Theory.Progress.Controls → Source.SoundnessExamples`;
`Roadmap.V16.CreationLibrarySpec → Backend.Executable.CreationReturnProducerControls`;
`Calculus.Blocks → Calculus.LexDiamond` (a rule module outside the listed rules).
The `Roadmap/**` pattern alone (`check-layers.mjs`, `^Solidity\.Roadmap\.`)
makes every roadmap statement "core", and roadmap statements import the
compiler.

**Why it matters.** P1's purpose is that an edit to the compiler or the
elaborator does not rebuild the calculus. With 398 compiler-side modules in
the core's closure, an edit to e.g. a Backend Controls file rebuilds core
modules; the document reports a property the code lost.

**First step.** Add a closure report to `check-layers.mjs` (print the 95
edges, fail only on new ones via a checked-in allow-list), and correct the
module count in `docs/parallelism.md`. Then move the Semantics/Theory
modules that import `Source`/`Lowering` (`Semantics/Nondeterminism/*`,
`Semantics/CtxEquiv/Source`, `Theory/Progress/*`) out of the core
namespace, since they are bridges, not foundations.

### 2. `Yul/Views`: renamed copies on one serial chain

**Evidence.** `ls Solidity/Yul/Views | wc -l` → 868 files, 74,110 lines,
one directory. `node scripts/import-fanout.mjs` → "longest import chain 212
modules"; `--chain` → 207 of them are `Yul.Views.*`, ending at
`Yul.Views.RetainedLoopBatchRefreshControls`. `near_files.py`: 49 groups /
144 files are exact copies after alpha-renaming; 202 files in near-copy
clusters (Jaccard ≥ 0.8), 137 of them in Yul. Example:
`{,Int,Member,Packed,Primitive,Recursive,Scalar}OwnershipPlan.lean`, 101
lines each; `diff` of `PackedOwnershipPlan` against `ScalarOwnershipPlan`
after stripping the prefix differs only in the path type, the inventory
function (`…SourceInventory?`), the snapshot function (`…Snapshot`) and the
separation check. The same 7–8-way pattern repeats for `OwnershipFrame`,
`Following`, `Reads`, `Batch`, `Banks`, `Inventory` (76 `*Ownership*`
files, 5,976 lines). `dup_general.py`: Yul/Views holds 128 of the 485
redundant general-lemma copies.

**Why it matters.** A serial chain bounds a cold build's wall time
regardless of cores; seven copies mean seven fixes, and the next variant is
an eighth copy.

**First step.** Define one `OwnershipPlan` structure parameterised by a
record `{Path, inventory?, snapshot, check}` and re-express
`ScalarOwnershipPlan` as an `abbrev` instance; keep the old names as
abbreviations so no consumer changes. Repeat per family once that
elaborates at the same speed (time it with `gate.sh per-file`).

### 3. Controls on the library's path

**Evidence.** 1,412 `*Controls.lean` files, 205,003 lines (19% of
`Solidity/`), 16,475 theorems, 13,923 `by decide`, 5,874 `#guard`.
Edges from a non-Controls, non-root module into a Controls module: 394
(`awk` over `imports.py edges`). Library modules (not Controls, Examples or
Checks) that depend transitively on some Controls module: 778 of 4,357
(Yul 365, Backend 357, Lowering 39, Frontend 11, Roadmap 4, Source 2). E.g.
`Backend.FunctionValues.RuntimeConstruction → Backend.FunctionValues.Controls`,
`Roadmap.V16.RelationalGuardSpec → Backend.FailurePaths.RelationalGuardControls`.
Olean bytes: Controls are 0.47 of 5.60 GB (8%), but they are not cheap to
elaborate. Timed sample (`timing-sample.tsv`, 30 + 30 files, each run
also as an import-only copy):

| Sample | Files | Total | Imports only | Body | Body per 1,000 lines | Median file |
|---|---|---|---|---|---|---|
| `*Controls` | 30 | 47.0 s | 13.0 s (28%) | 34.1 s | 8.38 s | 1.28 s |
| library | 30 | 36.0 s | 13.7 s (38%) | 22.4 s | 4.51 s | 0.70 s |

Extrapolated by lines and module counts, Controls take about 2,330 of
8,390 CPU-seconds of elaboration (28%; the whole estimate, 2.3 CPU-hours,
matches the ~24-minute 4-core build the `lean-lsp` instructions quote).
With a sample of 30 the share is ±10 points; the order of magnitude holds.
So Controls cost both coupling and about a quarter of build CPU; a data
table checked by one `decide` per family (they hold 13,923 `by decide`)
would recover part of the latter.

**First step.** Rename the 706 Controls modules that something imports
into what they are (fixtures or witnesses, e.g. `…Witness`), or move the
imported definitions out; add a check that a `*Controls` module has no
importer other than a root, with the current list as an allow-list.

### 4. Cache seed and per-file gate on cloud VMs

**Evidence.** `bash scripts/ci/fetch-lake-cache.sh` downloaded and verified
the pack, then printed `::warning::lake-cache install failed; building cold`
after an elan panic. The pack's `install.sh` runs `cd "$(dirname "$0")"`
(the temporary directory) and then `elan which lean`; outside the repository
there is no `lean-toolchain` and this VM has no default toolchain:
`cd <scratch> && elan which lean` → `panicked … no active toolchain`, while
from the repository root it prints the v4.24.0 path. With the pack installed,
`./run-lean.sh` passed in 8.4 s (6,461 jobs fetched), but
`gate.sh per-file` failed 59 of 60 sampled files with `object file
'.lake/build/lib/lean/…olean' … does not exist`: Lake 4.24 leaves fetched
modules in its cache (`scripts/ci/restore-lake-artifacts.py` docstring).
CI runs that restore step (`.github/workflows/lean.yml:94-95`); `gate.sh`
and `fetch-lake-cache.sh` do not. After running it, 60/60 passed.

**First step.** In `fetch-lake-cache.sh`, resolve the toolchain from the
repository before calling `install.sh` (or export the resolved cache path to
it), and run `restore-lake-artifacts.py` after a successful install.

### 5. Seven EVM fragment compilers

**Evidence.** `grep -rn '^inductive \(StmtFrag\|ProgFrag\)' Solidity` → one
pair each in `Evm/MemoryCompile.lean:165,381`, `MemoryObjectCompile.lean:9,37`,
`MemoryObjectConstructionCompile.lean:9,60`, `MemoryRefArrayCompile.lean:10,27`,
`MemoryFixedCompile.lean:62,104`, `MemoryStorageConstructionCompile.lean:9,15`,
`MemoryStorageCopyCompile.lean:26,237`, all `… → Stmt C Γ Δ → List Instr →
Prop`. Each restates `ProgFrag.pushes_zero` and a `private theorem
run_cons_revert` (e.g. `MemoryCompile.lean:861`, `MemoryObjectCompile.lean:104`),
the latter a fact about `Prog.run` alone. The 249 `Evm/Memory*` files hold
33,683 lines; `dup_general.py` puts 97 redundant general lemmas in `Evm`, and
15 between `MemoryCompile` and `MemoryStorageCopyCompile` alone.

**First step.** Move `run_cons_revert` (and the other `Prog.run` facts in
the duplicate list) to one public lemma in `Semantics` and delete the seven
private copies. Then measure whether one `ProgFrag` indexed by a feature
set elaborates as fast; if it does not (G0), keep the relations and share
their lemmas through a common interface.

### 6. Yul compilation restated per shape

**Evidence.** `ls Solidity/Yul/Compilation | wc -l` → 230. `structure
Artifact` is declared in 15 of them (e.g. `Artifact.lean:10`,
`ConditionalCompilation.lean:9`, `ForCompilation.lean:52`,
`LetBranchCompilation.lean:45`); `Artifact.source_to_model` and
`Artifact.normal_to_model` have identical statements in 10 files each
(`dup_decls.py`, e.g. `SwitchCompilation.lean:153`). 42 redundant general
lemma copies in the directory.

**First step.** A structure `ArtifactSpec` carrying `code`, `profile` and the
two model theorems as fields; make each shape file produce one, so
consumers depend on the structure rather than on a shape file.

### 7. `Roadmap` and milestone names as foundations

**Evidence.** `grep -rho 'Roadmap\.[A-Z][A-Za-z]*' Solidity | sort | uniq -c`:
`Roadmap.Pipeline` 3,671, `Roadmap.Word` 1,733, `Roadmap.Bytes` 1,452,
`Roadmap.Address` 753; 1,290 files mention `Roadmap.`. `import-fanout.mjs`:
`Roadmap.Contracts` has 3,423 transitive dependents, `Roadmap.Evm` 3,475.
`Yul/Words.lean:15` `abbrev Word := Solidity.Roadmap.Word`;
`Roadmap/Contracts.lean:55` `abbrev Word := Fin (2 ^ 256)`, while
`Semantics.lean:71` has its own `abbrev Word := PrimTy.uint.Denote`. 846
module paths carry a milestone tag (`V07/`, `P8/`, `G18…`, `H24…`,
`RuntimeFrameV3…`).

**First step.** Move `Word`, `Bytes`, `Address`, `Pipeline` from
`Roadmap/Contracts.lean`/`Roadmap/Evm.lean` into a neutral module (e.g.
`Solidity/Machine/Basic.lean`) with `export` aliases left in `Roadmap`, so
no consumer changes at once. Do module renames only between lane batches.

### 8. P2's size limit is not enforced

**Evidence.** `find Solidity -name '*.lean' -exec wc -l {} +` → 20 files over
1,800 lines: `Backend/StorageOps/TargetNestedArrayTransportControls.lean`
3,977, `Frontend/ExpressionUniqueness/AxiomPins.lean` 3,905,
`Calculus/ArrayProperty.lean` 3,142, `Calculus/QuotientCut.lean` 3,081, …,
`Typing/CleanTailRun.lean` 1,802. `Source/Horizon.lean` (2,305 lines) builds
the largest olean, 95 MB (`find .lake/build -name '*.olean' -printf '%s'`).

**First step.** A size check in `run-lean.sh`'s pre-steps with the current
20 as an allow-list; split `Source/Horizon.lean` first.

### 9. Duplicated general lemmas

**Evidence.** `dup_general.py`: 28,271 theorems whose statement opens with a
binder (outside Controls/Examples/Checks); 340 statement groups appear in
more than one file, 485 redundant copies, 177 of them `private`. By
directory: Yul/Views 128, Evm 97, Yul/Compilation 42, Backend/InternalFlow
29, Calculus 27 (`CloseScoped/Leaf.lean` and `SoundArms.lean` share 11).
`dup_decls.py` overall: 2,185 groups / 4,428 redundant copies, but most are
in Controls where equal text reads different local constants and is not a
duplicate.

**First step.** Work the `dup_general.py` pair list top-down after findings
2, 5 and 6 (which remove most of it); `Calculus/CloseScoped/Leaf.lean` vs
`Calculus/SoundArms.lean` is the core instance.

### 10. Unreferenced library declarations

**Evidence.** `unreferenced.py`: 1,553 of 33,380 library theorems (5%) and
136 of 19,284 defs (1%) whose name occurs nowhere else; Yul 803, Calculus
247, Backend 245. Top files: `Lowering/V07/RegisteredScalarClients.lean` 17,
`Calculus/CloseScoped/Steps.lean` 17, `SolcValidation/IrCensusUnique.lean`
16. Many are end results (a terminal theorem need not be cited), so this is
an upper bound.

**First step.** Review the 17-per-file clusters; delete or cite.

## 5. Things that look bad but are fine

- **No orphan modules.** `imports.py unreached` finds no `Solidity/` module
  outside a root; the 110 unreached files are all in `Bridge/` (vendored
  packages, tests, `SolidityVelvet`), which has its own lakefile.
- **Many small files.** 6,454 modules look like a per-module overhead
  problem, but an import-only copy of a sampled file loads in 0.43–0.46 s
  on average (`timing-sample.tsv`), about a third of a file's time; module
  count alone is not the bottleneck. (Retracted during the audit: olean
  bytes suggested Controls were cheap; timing shows they are not, finding 3.)
- **Docs cite code that exists.** `check-doc-paths.sh`: 5 missing paths, all
  in one `tests/h62/…/registration.md`; `doc_names.py`: 17 of 2,190 dotted
  names in `docs/*.md` have no Lean match, and most are solkey (Java) names
  or compiler-generated symbols (`___redArg`).
- **Two Solidity semantics.** `Semantics/` (KeY's fragment, intrinsic) and
  `Source/` (the full 0.8.38 grammar, `Source/Syntax.lean:1-40`) both define
  states and values; the module map calls `Source` "independent source
  definitions", and independence is the point (a cross-check). Its leaks into
  the core are finding 1.
- **No `native_decide`.** The 6 files that mention it say they do not use it.
- **"untyped" in docstrings** (60 hits) are statements that a module avoids an
  untyped layer; no untyped statement/state type was found outside the
  documented boundaries (`docs/intrinsic.md`, "What stays extrinsic").
- **The elaborator split holds.** `node scripts/check-layers.mjs`: "859 core
  modules, 0 reach the elaborator".

## 6. Open questions for the user

None blocks this report. Two decisions shape the fixes:

- Should `Roadmap/**` stay in `CORE`? It is the main route by which compiler
  modules enter the core's closure (finding 1); dropping the pattern is the
  one-line alternative to moving 95 edges.
- Are `*Controls` meant to be importable? If yes, finding 3 is a naming fix;
  if no, it is a dependency fix.
