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
consistent renaming (137 of the 202 near-copies are in Yul), twenty Yul
compilation files each declare their own `Artifact` while a generic one sits
unused, and 207 `Yul.Views` modules form one serial import chain, the
longest in the package. `*Controls` modules (19% of lines) cost about 28% of
elaboration CPU in a timed sample, and about 117 library imports reach into
them. The stated layering is not what is checked: `docs/parallelism.md`
says the core is closed under imports, but 95 core imports leave it and its
closure pulls in 398 compiler-side modules. Finally, the sanctioned cache
seed silently fails on cloud VMs, and once it works the per-file gate fails
until a restore step that only CI runs. The highest payoff for the least
risk is in the tooling (ranks 1, 2), then generic interfaces for the copied
families (ranks 3–5). Renaming `Roadmap` and the milestone namespaces pays
least for its risk.

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
| Skeptic | one read-only agent (no Lean server, no builds) re-ran the tools and tried to refute each finding | §7 |

Cache: `fetch-lake-cache.sh` failed on this VM (finding 4). The pack was
installed by running its own `install.sh` with `elan which` answered for the
repository's toolchain (a shim on `PATH`; `LAKE_CACHE_DIR` not set for Lake),
`./run-lean.sh` then fetched every module, and `restore-lake-artifacts.py`
(given the cache path for that one run) placed 12,892 files.

## 3. Top 10

Ranked after the skeptic pass (§4 numbers are finding IDs and keep
their order of discovery; the rank is payoff against risk).

| Rank | Finding (§4) | Evidence | Estimated payoff | Effort | Risk |
|---|---|---|---|---|---|
| 1 | The "core" is not closed under imports, contrary to `docs/parallelism.md` P1; the checker never tests closure (§1) | 95 direct core→non-core imports (57 from exact-name Yul entries, 13 via `^Solidity\.Roadmap\.`); closure adds 398 modules / 86,664 lines (115 Backend, 109 Evm) | Restores what P1 promises (a compiler edit does not rebuild the calculus); stops drift that grows each lane | S (report) / M (fix edges) | Low |
| 2 | The cache seed fails on cloud VMs, and the per-file gate needs a restore step only CI runs (§4) | `install.sh` leaves the repo, `elan which lean` panics ("no active toolchain") → "building cold"; per-file gate 59/60 FAIL until `restore-lake-artifacts.py`, 60/60 after | Every cloud lane: seconds instead of a ~24-min cold build; per-file gate usable | S | Low |
| 3 | `Yul/Views`: an 868-file directory of renamed copies on one serial chain (§2) | 207 `Yul.Views` modules in the 211-module longest chain; 137 of 202 near-copy files; 7-way exact families (`OwnershipPlan`, `Frame`, `Following`, …) | Cold-build critical path; ~6k lines of `*Ownership*` → ~1k; one fix instead of 7 | M | Medium |
| 4 | Controls are on the library's path and cost ~28% of elaboration CPU (§3) | ~117 genuine library→Controls edges; ~780–800 library modules depend on one; Controls elaborate at 8.4 s/kline vs 4.5 (sample 30+30) | Fixtures editable without rebuilding the compiler; ~0.6 CPU-h per cold build if halved | M | Low |
| 5 | Yul compilation restated per shape, while a generic `Artifact` sits unused (§6) | 20 `structure Artifact`; `source_to_model` in 15 files; `Yul/Compilation/Artifact.lean` imported by none, an "unvalidated draft" of retired lane H55 | One interface; shape files stop being API | M | Medium (needs the `vy2-physical` owner) |
| 6 | Seven private byte-identical `run_cons_revert` in the EVM fragment compilers (§5) | 7 × `inductive StmtFrag`/`ProgFrag` in `Evm/Memory*Compile.lean`; `run_cons_revert` equal (md5) in all 7 | Small (7 copies → 1) | S | Medium: home is `Semantics/Run.lean`, ~3,550 dependents |
| 7 | P2's size limit is not enforced (§8) | 20 files > 1,800 lines (max 3,977); `Source/Horizon.lean` 2,305 lines → largest olean, 95 MB | Worker memory, re-check size | S each | Low |
| 8 | Duplicated general lemmas (§9) | 340 groups / 485 copies / 177 private, about half real (166 groups name file-local constants) | Mostly falls out of ranks 3, 5, 6 | S–M | Low |
| 9 | `Roadmap.*` types and milestone tags as names of foundations (§7) | `Roadmap.Pipeline` 3,671 uses, `Roadmap.Word` 1,733; `Roadmap.Contracts` 3,423 dependents; two `Word`s; ~846 tagged paths | Readability; placement itself is by design (G01) | L | High (near-full rebuild, conflicts with live lanes) |
| 10 | Unreferenced library declarations (§10) | 1,553 library theorems (5%) named nowhere else, 803 in Yul; upper bound | Small | S | Low |

## 4. Findings

### 1. The core is not closed under imports

**Evidence.** `docs/parallelism.md:46` (P1): "The list is closed under imports: no
core module imports a module outside it". (The "123 modules now" at
`:105-107` is a stale count in a historical P2 pitfall, not a contract.)
Of the 95 leaks, 57 come from Yul modules that `CORE` names exactly and 13
from the `^Solidity\.Roadmap\.` pattern (skeptic count).
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
module count in `docs/parallelism.md`. The check already runs in CI
(`lean.yml:44`), `run-lean.sh:23` and `gate.sh`, so a report-only step
costs nothing new. Then move the Semantics/Theory
modules that import `Source`/`Lowering` (`Semantics/Nondeterminism/*`,
`Semantics/CtxEquiv/Source`, `Theory/Progress/*`) out of the core
namespace, since they are bridges, not foundations.

### 2. `Yul/Views`: renamed copies on one serial chain

**Evidence.** `ls Solidity/Yul/Views | wc -l` → 868 files, 74,110 lines,
one directory. `node scripts/import-fanout.mjs` → "longest import chain 212
modules" (211 plus the `Solidity` root); `--chain` → 207 of them are
`Yul.Views.*`, ending at `Yul.Views.RetainedLoopBatchRefreshControls`.
`near_files.py`, package-wide: 49 groups / 144 files are exact copies after
alpha-renaming (also `TestSuite/Derived*`, `Backend/Passes/*Pins`); 202
files in near-copy clusters (Jaccard ≥ 0.8), 137 of them in Yul. Example:
`{,Int,Member,Packed,Primitive,Recursive,Scalar}OwnershipPlan.lean`, 7
files of 101 lines (`RetainedOwnershipPlan`, 118 lines, adds history and
length fields and is not a copy); `diff` of `PackedOwnershipPlan` against `ScalarOwnershipPlan`
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
abbreviations so no consumer changes. The parameters are intrinsic
functions, so this keeps `docs/intrinsic.md`'s rules. Repeat for each
family (Plan, Frame, Following, Reads, Batch, Banks, Inventory; seven
chained conversions, not one), each once the first elaborates at the same
speed (time it with `gate.sh per-file`).

### 3. Controls on the library's path

**Evidence.** 1,412 `*Controls.lean` files, 205,003 lines (19% of
`Solidity/`), 16,475 theorems, 13,923 `by decide`, 5,874 `#guard`.
Edges from a non-Controls module other than the `Solidity` root into a
Controls module: 394, but 158 come from the generated `SolidityBridge` root
and 3 from `SolidityExamples`; of the remaining 237, 120 come from check-like
modules (`*Pins`, `*Audit`, `*Axioms`, `*Checks`), leaving **about 117
genuine library→Controls edges** (skeptic recount). Library modules (not
Controls, Examples or Checks) that depend transitively on some Controls
module: 778 of 4,357 by my filter, 803 by the skeptic's (Yul 365–367,
Backend 357–363, Lowering 39, Frontend 11, Roadmap 4, Source 2). "Controls"
does not mean test-only: 1,411 of 1,412 declare theorems or defs that other
modules may use as witnesses (Roadmap V16 opens
`CreationReturnProducerControls`). E.g.
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

**First step.** A check, with the ~117 current library edges as an
allow-list, that no new library module imports a `*Controls` module; then
move the witnesses those 117 edges use into modules named for what they are
(e.g. `…Witness`). Downgraded by the skeptic from "forbid" to "allow-list":
some imports are deliberate witness reuse.

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

This is not an elan bug: `install.sh` leaves the repository, so elan has no
`lean-toolchain` to read. (The first run's panic was reported as "binary not
found"; reproduced from a scratch directory, it reads "no active toolchain".)

**First step.** (Corrected by the skeptic.) Two separate fixes:
(a) in `fetch-lake-cache.sh`, give `install.sh` the toolchain, e.g.
`ELAN_TOOLCHAIN=$(cat lean-toolchain)` or the cache path resolved from the
repository root; (b) run `restore-lake-artifacts.py` in `gate.sh per-file`
(or at the end of `run-lean.sh`), **after** a build, with the cache path
resolved as `scripts/coord-tools/ship-cache.sh:151` does. Running it inside
the fetch script would do nothing: it walks `.lake/build/**/*.trace`, which
only a build writes, and it exits on an unset `LAKE_CACHE_DIR` off CI.
Check that its hard links cannot be overwritten in place by a later local
build (that would corrupt the shared cache); copying instead of linking
avoids the question at ~6 GB of disk.

### 5. Seven EVM fragment compilers

**Evidence.** `grep -rn '^inductive \(StmtFrag\|ProgFrag\)' Solidity` → one
pair each in `Evm/MemoryCompile.lean:165,381`, `MemoryObjectCompile.lean:9,37`,
`MemoryObjectConstructionCompile.lean:9,60`, `MemoryRefArrayCompile.lean:10,27`,
`MemoryFixedCompile.lean:62,104`, `MemoryStorageConstructionCompile.lean:9,15`,
`MemoryStorageCopyCompile.lean:26,237`, all `… → Stmt C Γ Δ → List Instr →
Prop`. Each has a `private theorem run_cons_revert` (e.g.
`MemoryCompile.lean:861`, `MemoryObjectCompile.lean:104`) whose statement
and proof are byte-identical across all seven (skeptic: equal md5), a fact
about `Prog.run`/`Stmt.run` alone. `ProgFrag.pushes_zero` is restated too,
but each copy is about its own file's relation, so those are not redundant
(skeptic downgrade). The relations cover different fragments
(`MemoryStorageConstructionCompile` reuses `Fixed`'s pieces). The 249
`Evm/Memory*` files hold 33,683 lines.

**First step.** Put `run_cons_revert` once, public, beside
`Prog.run_cons_ok` (`Semantics/Run.lean:1349`), and delete the seven
private copies. **Warning:** `Semantics/Run.lean` has about 3,550
dependents, so this edit rebuilds most of the package; batch it with
another core edit or accept one cold rebuild. Whether one `ProgFrag`
indexed by a feature set is as fast as seven relations (G0) is open; measure
before merging relations.

### 6. Yul compilation restated per shape

**Evidence.** `ls Solidity/Yul/Compilation | wc -l` → 230. `structure
Artifact` is declared in 20 of them (`grep -l '^structure Artifact'`; e.g.
`ConditionalCompilation.lean:9`, `ForCompilation.lean:52`,
`LetBranchCompilation.lean:45`); `Artifact.source_to_model` is stated in 15
files, one statement six times and another four (`dup_decls.py`, e.g.
`SwitchCompilation.lean:153`). 42 redundant general-lemma copies in the
directory.

**Already started, then stopped (found by the skeptic).**
`Solidity/Yul/Compilation/Artifact.lean` is a generic intrinsic `Artifact`
with `profile`, `code`, `source_to_model`, `model_to_source` and
`normal_to_model`. It is registered in `Solidity.lean`, but no file imports
it. `docs/feature-work/h55-yul-artifact.md:3-17` records it as an
"unvalidated additive draft" of the retired H55 lane. Its successor is
`vy2-physical`, and interface changes "still need the owner".

**First step.** Do not write a second interface. Ask the `vy2-physical`
owner whether to validate the H55 draft, then write one adapter (for
`SwitchCompilation`'s `Artifact` → the generic one) and time it.

### 7. `Roadmap` and milestone names as foundations

**Evidence.** `grep -rho 'Roadmap\.[A-Z][A-Za-z]*' Solidity | sort | uniq -c`:
`Roadmap.Pipeline` 3,671, `Roadmap.Word` 1,733, `Roadmap.Bytes` 1,452,
`Roadmap.Address` 753; 1,290 files mention `Roadmap.`. `import-fanout.mjs`:
`Roadmap.Contracts` has 3,423 transitive dependents, `Roadmap.Evm` 3,475.
`Yul/Words.lean:15` `abbrev Word := Solidity.Roadmap.Word`;
`Roadmap/Contracts.lean:55` `abbrev Word := Fin (2 ^ 256)`, while
`Semantics.lean:71` has its own `abbrev Word := PrimTy.uint.Denote`. About
846 module paths carry a milestone tag (`V07/`, `P8/`, `G18…`, `H24…`,
`RuntimeFrameV3…`); the regex in §2's history is approximate (a simple
variant also catches `Precompiles/P256.lean`, the curve).

**Skeptic downgrade: intentional.** `Roadmap/Contracts.lean`'s docstring
calls these the G01 "final theorem contracts", placed at the base on purpose
(`docs/feature-work/roadmap-g01-interfaces.md`). The base placement is by
design; what is wrong is the name, and two `Word` types (`Fin (2^256)` and
`PrimTy.uint.Denote`).

**First step.** Move `Word`, `Bytes`, `Address`, `Pipeline` from
`Roadmap/Contracts.lean`/`Roadmap/Evm.lean` into a neutral module (e.g.
a new `Solidity.Machine.Basic` module) with `export` aliases left in `Roadmap`, so
no consumer changes at once. **Warning (AGENTS.md):** `Roadmap.Contracts`
has ~3,400 dependents, so this is a near-full rebuild; do it between lane
batches. Do module renames only then too.

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

**Skeptic downgrade: an upper bound.** The hash ignores namespace, `open`
and `variable` context. In 166 of the 340 groups (240 copies), the statement
names a declaration that is local to each of at least two of its files (like
`ProgFrag.pushes_zero`, finding 5). Those are statements about different
constants. About half the 485 copies are real, and most of those fall out of
findings 2, 5 and 6.

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

None blocks this report. Three decisions shape the fixes:

- Should `Roadmap/**` stay in `CORE`? The pattern brings 13 of the 95
  leaks directly and the compiler-side Roadmap V16 statements with them
  (finding 1). Dropping it is the cheap alternative to moving edges; keeping
  it means moving the Roadmap V16 consumers out.
- Are `*Controls` meant to be importable witnesses? If yes, finding 3 is a
  naming fix plus an allow-list; if no, it is a dependency fix.
- Should the H55 generic `Yul/Compilation/Artifact.lean` draft be validated
  and adopted (finding 6), or deleted? Its lane is retired, its successor is
  `vy2-physical`, and its doc says interface changes need the owner.

## 7. Skeptic pass

One read-only agent (no Lean server, no builds) re-ran the tools and tried
to refute each finding. Its verdicts, and what changed here:

| § | Verdict | Change made |
|---|---|---|
| 1 | Survives; numbers reproduced | "123 modules" identified as a stale P2 pitfall, not P1; leak breakdown (57 Yul exact names, 13 Roadmap) added |
| 2 | Downgrade on counts | Chain is 211 modules + root; `OwnershipPlan` family is 7 files, not 8; 144-file count marked package-wide; fix is seven chained conversions |
| 3 | Downgrade | 394 edges → ~117 genuine library edges after removing generated roots and check-like modules; "forbid" → allow-list; Controls can be deliberate witnesses. (The CPU share was added after this pass, from my timing.) |
| 4 | Downgrade: fix in the wrong place | Restore needs a prior build and a cache path, so it goes in `gate.sh`/`run-lean.sh`, not the fetch script; root cause stated as a missing toolchain outside the repo, not an elan bug; hard-link hazard noted |
| 5 | Survives for `run_cons_revert`, downgrade for `pushes_zero` | `pushes_zero` copies are about distinct relations; rank lowered to 6; rebuild warning for `Semantics/Run.lean` added |
| 6 | Downgrade; known, stopped work | Counts corrected (20 `Artifact`s, 15 `source_to_model`); proposed new `ArtifactSpec` withdrawn in favour of the existing H55 draft, owner-gated |
| 7 | Downgrade: intentional placement | G01 design noted; complaint narrowed to names and two `Word` types; tag count marked approximate; rebuild warning added; rank lowered to 9 |
| 8 | Survives | Two of 22 > 1,800-line files are exempt (generated corpus, vendored), as already excluded |
| 9 | Downgrade: upper bound | About half the copies name file-local constants and are not redundant |
| 10 | Survives as an upper bound, low value | none |

The skeptic found nothing structurally larger than findings 1–3.
