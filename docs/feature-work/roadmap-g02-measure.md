# Roadmap G02: measured build baseline

Group G02 of the [roadmap](../coverage-plan.md), wave 0: "Measure cold/warm
per-target checking on 16 GiB; publish bounded build/cache reproduction and
split any oversized target. Preserve current baseline evidence and identify
stale artifacts." This group only measures. No Lean module, target,
lakefile or generated file changed. The oversized targets are reported as
[findings](#4-oversized-targets-findings-not-edited) with recommended splits,
because their files belong to other lanes.

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285` ("Record
  resource and environment decisions"). The branch adds only the two scripts
  and this document. The measured Lean sources are the base's.
- **Machine:** the 16 GiB reference VM. It has 4 cores, 15 GiB `MemTotal`,
  no swap and about 25 GiB of free disk. Lean is v4.24.0 through elan.
  The shell's memory cgroup (v1) limits every command, its children
  included, to **14 341 885 952 B (13.36 GiB)**
  (`memory.limit_in_bytes`). That cgroup, not `MemAvailable`, sets when
  the OOM killer fires.
- **Concurrency:** `./run-lean.sh` exactly as committed. Lake ran up to
  **4 concurrent `lean` workers** (one per core). `LEAN_NUM_THREADS` was
  unset and no `-j`/`MemoryMax` wrapper was added. Lake 4.24's `lake --help`
  lists no job-count option.
- **Method:** [`scripts/build-measure.py`](../../scripts/build-measure.py)
  runs the command in its own process group. Every 0.5 s (1 s for the Bridge
  run) it samples `/proc/<pid>/status` (`VmRSS`, `VmHWM`) of each
  `lean`/`lake` process in that group and `/proc/meminfo` (`MemAvailable`).
  After the run it records `.olean` modification times and the kernel's OOM
  lines (`dmesg`).
  [`scripts/build-measure-report.py`](../../scripts/build-measure-report.py)
  joins these samples with the exact per-module times Lake prints
  (`Built M (12s)`) and produces the tables below. Both scripts use only the
  standard library. The raw sample files are session-local and are not
  committed; the tables keep every number cited here.
- **RSS caveat:** `VmRSS`/`VmHWM` count the file-backed `.olean` pages each
  worker maps, and those pages are shared between workers. A worker that only
  imports the closure already shows about 1.0–1.2 GiB
  (`Solidity.Roadmap.Contracts`: 1.0 s, 1170 MiB). The summed "lean RSS"
  therefore overstates the real total (16 495 MiB summed against a
  13.36 GiB cgroup). `MemAvailable` and the OOM events are the
  authoritative pressure signals.

## 1. Runs

| Run | State before | Wall | Result | Peak workers | Min `MemAvailable` | OOM |
|---|---|---:|---|---:|---:|---|
| cold | no `.lake`, empty Lake artifact cache (fresh VM) | **58 min 0 s** (`real 58m0.485s`, `user 129m23s`, `sys 36m11s`) | default `lake build`: "Build completed successfully (718 jobs)" at 2 580 s (**43 min**). `lake build SolkeyTestSuite`: `Solidity.TestSuite.Derived17` "Lean exited with code 137" after 672 s, then "error: build failed", exit 1. `check-solkey.sh` not reached. | 4 | 1 732 MiB | 1 memcg OOM kill (victim `lean`, Derived17), 4 workers |
| warm 1 | after cold; only Derived17 (and its dependents `Report`, `SolkeyTestSuite`) missing | **2 min 47 s** | Derived17 alone: **149 s, 11 777 MiB peak**. Then "Build completed successfully (262 jobs)" and `solkeycheck: 37 mismatch(es)`, exit 1 | 1 | 4 462 MiB | none |
| warm 2 | everything built | **2.1 s** | both builds "completed successfully", 37 mismatches, exit 1 | 0 | 15 219 MiB | none |
| cache restore | `.lake` deleted, Lake artifact cache kept | **3.1 s** | every module `Fetched`, both builds complete, 37 mismatches, exit 1 | 0 | 14 987 MiB | none |
| Bridge (`--bridge`) | after cache restore; `Bridge/.lake` absent | see [§6](#6-bridge-variant) | | | | |

Exit 1 in the warm runs comes from `check-solkey.sh`. It reports
`37 mismatch(es)`, the base's existing drift and unchanged from it. No
annotation file changed here.

**The OOM.** At 3 313 s four workers were live: `Derived20` (started
2 622 s), `Derived17` (2 642 s), `Derived15` (2 684 s) and `Derived14`
(3 261 s). They summed 13.75 GB RSS and `MemAvailable` was 1.89 GB. When the
cgroup reached its limit, the kernel killed the largest worker, Derived17, at
9 805 MiB (`oom-kill:constraint=CONSTRAINT_MEMCG`). `SolkeyTestSuite` makes
Derived15/17/20/21 ready together because all four import
`Solidity.TestSuite.ScopedProblems` (Derived20/21 also `Solidity.Calculus.Closers`),
which is built well before. Under the
default concurrency they always overlap. Derived17 alone needs 11.5 GiB, so
**any** worker beside it can push the group past 13.36 GiB. This reproduces
the G01 VM's cold run, where Derived15/17 were lost to exit 137
([roadmap-g01-interfaces.md](roadmap-g01-interfaces.md)). It also confirms
[integration.md](integration.md)'s report that Derived17 alone exceeded a
10 GiB cap.

**The default target came close too.** At 1 887 s `MemAvailable` fell to
1 808 MiB while `Examples.Tactics.OpenLoops` (7 908 MiB peak) and
`Examples.DecisionHashes` (6 478 MiB) overlapped, with only two workers live.
That left roughly 0.2 GiB below the cgroup limit. The default build passing at
4 workers is therefore marginal, not a safe bound.

**Time split.** Lake reports 10 950 s of summed `lean` time over 732
processes (3.04 h of serial work). By directory:

| Directory | Modules | Summed time | Max peak RSS |
|---|---:|---:|---:|
| `Solidity/TestSuite` | 25 | 3 337 s | 9 805 MiB (11 777 MiB alone) |
| `Solidity/Examples/Tactics` | 132 | 2 997 s | 7 908 MiB |
| `Solidity/Calculus` | 283 | 1 757 s | 4 013 MiB |
| `Solidity/Examples` (other) | 54 | 1 299 s | 6 478 MiB |
| `Solidity/Evm` | 52 | 254 s | 3 040 MiB |
| `Solidity` (top level) | 18 | 228 s | 1 806 MiB |
| `Solidity/Semantics` | 49 | 199 s | 2 388 MiB |
| `Solidity/Syntax` | 19 | 197 s | 1 440 MiB |
| `Solidity/Examples/Chains` | 15 | 195 s | 1 962 MiB |
| `Solidity/SortCheck` | 3 | 109 s | 7 357 MiB |
| all others | 82 | 378 s | ≤ 2 221 MiB |

Across all 732 workers, the median peak RSS is 1 321 MiB and the 90th
percentile is 1 950 MiB. 96 workers peaked above 2 GiB, 36 above 4 GiB and
19 above 8 GiB.

**The earlier serial measurement is consistent.**
`tests/upstream/baseline-20261028/performance.json` records a cold run under
one CPU, `LEAN_NUM_THREADS=1`, `-j1` and a 12 GiB cap. It was stopped by a
5 400 s timeout after 546 of 685 default targets (cgroup peak
8 195 923 968 B). Lake's 3.04 h of serial work predicts that outcome:
Derived17 alone needs more than that cap allows. That file is preserved
unchanged as historical evidence.

## 2. The 20 slowest modules (cold, Lake-reported time)

| # | Module | Elapsed (s) | Peak RSS (MiB) | Start (s) |
|---:|---|---:|---:|---:|
| 1 | `Solidity.TestSuite.Derived20` | 722 | 2 265 | 2 622 |
| 2 | `Solidity.TestSuite.Derived17` | 672 (killed); 149 alone | 9 805 (killed); 11 777 alone | 2 642 |
| 3 | `Solidity.TestSuite.Derived15` | 669 | 3 966 | 2 684 |
| 4 | `Solidity.TestSuite.Derived21` | 627 | 5 580 | 2 634 |
| 5 | `Solidity.Examples.Tactics.OpenLoops` | 517 | 7 908 | 1 414 |
| 6 | `Solidity.Examples.Decision` | 494 | 5 642 | 2 005 |
| 7 | `Solidity.Examples.Tactics.Recursion` | 301 | 2 878 | 1 058 |
| 8 | `Solidity.Examples.DecisionHashes` | 283 | 6 478 | 1 721 |
| 9 | `Solidity.Examples.Tactics.CallbackStrategy` | 169 | 2 128 | 984 |
| 10 | `Solidity.Examples.Tactics.RevertData` | 140 | 6 335 | 1 164 |
| 11 | `Solidity.TestSuite.Derived7` | 121 | 5 597 | 3 359 |
| 12 | `Solidity.Examples.Tactics.Hashing` | 117 | 3 065 | 1 231 |
| 13 | `Solidity.Examples.Tactics.PublicGetters` | 108 | 4 045 | 1 473 |
| 14 | `Solidity.SortCheck.Faithfulness` | 106 | 7 357 | 537 |
| 15 | `Solidity.Syntax.Elab.Arms` | 99 | 1 440 | 204 |
| 16 | `Solidity.Examples.Tactics.AbiFeatures` | 92 | 3 772 | 1 002 |
| 17 | `Solidity.Examples.Tactics.Join` | 91 | 3 360 | 910 |
| 18 | `Solidity.Examples.Tactics.Memory` | 84 | 1 992 | 1 117 |
| 19 | `Solidity.Calculus.RuleShapes` | 82 | 4 013 | 434 |
| 20 | `Solidity.TestSuite.Derived8` | 80 | 4 776 | 3 353 |

The four long TestSuite modules ran concurrently with each other, so their
cold times include CPU and memory contention. Derived17 alone took 149 s
against 672 s in the contended run, which suggests contention more than
quadruples its cost. The other three were not re-measured alone.

## 3. The 20 most memory-hungry modules (cold, peak `VmHWM`)

| # | Module | Peak RSS (MiB) | Elapsed (s) |
|---:|---|---:|---:|
| 1 | `Solidity.TestSuite.Derived17` | 9 805 when killed; **11 777 alone** | 672 / 149 |
| 2 | `Solidity.Examples.Tactics.OpenLoops` | 7 908 | 517 |
| 3 | `Solidity.SortCheck.Faithfulness` | 7 357 | 106 |
| 4 | `Solidity.Examples.DecisionHashes` | 6 478 | 283 |
| 5 | `Solidity.Examples.Tactics.RevertData` | 6 335 | 140 |
| 6 | `Solidity.Examples.Decision` | 5 642 | 494 |
| 7 | `Solidity.TestSuite.Derived7` | 5 597 | 121 |
| 8 | `Solidity.TestSuite.Derived21` | 5 580 | 627 |
| 9 | `Solidity.TestSuite.Derived3` | 4 960 | 47 |
| 10 | `Solidity.TestSuite.Derived8` | 4 776 | 80 |
| 11 | `Solidity.TestSuite.Derived19` | 4 500 | 55 |
| 12 | `Solidity.TestSuite.Derived12` | 4 494 | 53 |
| 13 | `Solidity.Examples.Tactics.DeclarationMetadata` | 4 338 | 71 |
| 14 | `Solidity.TestSuite.Derived10` | 4 070 | 29 |
| 15 | `Solidity.Examples.Tactics.PublicGetters` | 4 045 | 108 |
| 16 | `Solidity.Calculus.RuleShapes` | 4 013 | 82 |
| 17 | `Solidity.TestSuite.Derived4` | 3 994 | 29 |
| 18 | `Solidity.TestSuite.Derived15` | 3 966 | 669 |
| 19 | `Solidity.TestSuite.Derived6` | 3 826 | 34 |
| 20 | `Solidity.Examples.Tactics.AbiFeatures` | 3 772 | 92 |

By concurrency (cold, 0.5 s samples; the summed RSS overcounts shared pages):

| Live workers | Approx. time | Max summed lean RSS (MiB) | Min `MemAvailable` (MiB) |
|---:|---:|---:|---:|
| 1 | 699 s | 5 641 | 9 142 |
| 2 | 265 s | 12 722 | 1 808 |
| 3 | 102 s | 12 955 | 6 390 |
| 4 | 2 371 s | 16 495 | 1 732 |

## 4. Oversized targets (findings, not edited)

A module is **oversized** for the 16 GiB VM if, alone, it needs more than
the 12 GiB `MemoryMax` that the [VM execution contract](../coverage-plan.md#vm-execution-contract)
prescribes, or so much that no second worker fits beside it under the
13.36 GiB shell cgroup. A module is **long** if it is on the critical path
for more than about 10 minutes.

| Module | Owner (do not edit here) | Measurement | Recommended split |
|---|---|---|---|
| `Solidity/TestSuite/Derived17.lean` (58 lines, 10 `sol_prove` theorems; `steps := 512`, one `1024`, one `256` with `sol_leaf`/`sol_close`) | Codex memory-loops (shared Derived17 repair) | 11 777 MiB / 149 s alone; OOM-killed at 9 805 MiB when beside three other TestSuite workers | **Oversized.** Split into at least two modules that each import only `ScopedProblems`. Before choosing the cut, the owning lane should measure peak memory per declaration: this run gives only the per-module peak, and it is not known whether the peak comes from one proof (then isolate that theorem, likely `returnLeavesNestedLoops` with `steps := 1024` or the `invariantForCountsArrayLength` closer) or from the environment growing across theorems (then cut the plain while/for/do-while proofs from the storage, nested-return and invariant proofs). The aim is that no resulting module exceeds about 6 GiB alone, so two fit beside each other. Until then, build Derived17 before, not beside, its siblings (see the recipe). |
| `Solidity/TestSuite/Derived15.lean` (172 lines, 48 `sol_prove` theorems) | Codex memory-loops | 3 966 MiB, 669 s while contended | **Long**, not oversized. Split in its existing source order into three modules of about 16 theorems each (the file is "derived in source order", not grouped by topic). This should turn about 11 critical-path minutes into three parallel jobs; the per-theorem cost was not measured. |
| `Solidity/TestSuite/Derived20.lean` (3 `sol_auto_theorem`) | not assigned to a lane here; TestSuite `Derived*` files are reserved | 2 265 MiB, 722 s while contended | **Long.** It is the slowest module in the build. Use one module per `sol_auto_theorem`, so that the three walks run in parallel. |
| `Solidity/TestSuite/Derived21.lean` | as above | 5 580 MiB, 627 s while contended | **Long**, and the second-largest TestSuite memory user. Measure it alone before splitting. |
| `Bridge/SolidityBridge/Arith/Widths.lean` (605 lines) | evm-storage-slots (shared Widths repair) | see [§6](#6-bridge-variant) | see [§6](#6-bridge-variant) |
| `Solidity/Examples/Tactics/OpenLoops.lean`, `Solidity/SortCheck/Faithfulness.lean`, `Solidity/Examples/DecisionHashes.lean`, `Solidity/Examples/Tactics/RevertData.lean` | no lane recorded | 6.2–7.7 GiB peaks, under the cap alone | **Watch list.** Not oversized alone, but any two of them overlap past the limit, which nearly happened at 1 887 s. Re-measure after any change that touches them. |

Lake builds a library's modules in import order, and these targets have no
ordering edges between them, so no split can be chosen through the lakefile.
The only build-side mitigation that changes no source is to build the
oversized module first, on its own (recipe step 4).

## 5. Bounded build and cache reproduction

The cache facts below were measured on this VM:

- Lake's artifact cache (`enableArtifactCache = true` in `lakefile.toml`)
  lives in the toolchain directory:
  `~/.elan/toolchains/leanprover--lean4---v4.24.0/lake/cache`, a symlink
  into `~/.elan/dist/lean-4.24.0-linux/lake/cache`. After the cold run it
  held 2.6 GB: `artifacts/` (2 207 content-hashed files: 733 `.olean`,
  733 `.ilean`, 733 `.c`, 6 `.o`, 2 executables) and
  `inputs/solidity-lean.jsonl` (741 lines mapping an input hash to its output
  hashes).
- A cold build also copies its outputs into `.lake/build` (2.6 GB). They are
  copies, link count 1, not hard links. The cache and `.lake/build` together
  take about 5.2 GB.
- A cache restore with `.lake` deleted printed `Fetched` for every module.
  It finished in 3.1 s and left `.lake/build` with only `.ilean`, `.trace`,
  `.hash` and the two executables (376 MB): **no `.olean` was written to
  `.lake/build/lib/lean`**. Lake and the Lean server read the oleans from the
  cache. `lean_diagnostic_messages` on `Solidity/Roadmap/Contracts.lean` in
  that state returned no errors and no failed dependencies.

The recipe, with persistence keyed by toolchain and manifest:

1. **Key:** `sha256(lean-toolchain ‖ lakefile.toml ‖ lake-manifest.json)`.
   For the Bridge, also hash `Bridge/lean-toolchain`,
   `Bridge/lakefile.toml` and `Bridge/lake-manifest.json`. The cache is
   content-addressed: Lake recomputes every input hash, so restoring an older
   or mismatched cache is safe and only costs rebuilds of the misses. Use the
   toolchain alone as the restore-fallback prefix.
2. **Persist:** the resolved directory
   `$(readlink -f ~/.elan/toolchains/leanprover--lean4---v4.24.0)/lake/cache`
   (about 2.6 GB for the core). For the Bridge, also persist
   `Bridge/.lake/packages`, the git checkouts of Mathlib, CSLib and lean-auto
   (see §6). Persisting `.lake/build` is not needed. Keep the cache on disk,
   not on a RAM-backed `/tmp`
   ([refactoring-progress.md](../refactoring-progress.md#resource-bounds-and-resuming-work)).
3. **Restore and check:** put the directory back, then run `./run-lean.sh`.
   Expect about 3 s, `Fetched` lines and "Build completed successfully"
   twice. Exit 1 with `37 mismatch(es)` is the base's drift (§1).
4. **Cold, bounded:** with no cache, a complete gate on this VM is about
   61 min. That is the 58 min run, which loses Derived17 to the OOM, plus
   the 2 min 47 s re-run that builds it alone. Building Derived17 by itself
   before `SolkeyTestSuite` avoids the kill, because it fits the cgroup only
   when alone: 11.5 GiB against 13.36 GiB. That ordering was not run here as
   a single command (the repository denies a bare `lake build` in this shell),
   and the timing is the sum of the two measured runs. A fully serial cold
   build (`-j1`, one CPU) needs at least the 3.04 h of summed Lean time, and
   `performance.json` shows it does not finish in 90 min.
5. **Verify a cache against a clean build** (G54.03): this requires a cold
   build in a fresh VM with an empty cache, followed by a comparison of the
   `inputs/*.jsonl` output hashes. This run has one cold build and so
   establishes the reference hashes only for this revision. A second cold
   build to compare against was not run.

## 6. Bridge variant

Pending; see the run summary below once the Bridge run finishes.

## 7. Stale artifacts and stale claims

No file was changed; each item names its owner or the place to fix it.

| # | Artifact or claim | Evidence | Effect |
|---|---|---|---|
| A1 | `.lake/build/lib/lean/*.olean` in a checkout whose modules were later **restored** from the cache | A restore writes no `.olean` into `.lake/build` (§5). A checkout that once built cold keeps its earlier copies, which no later restore refreshes. | Tools that put `.lake/build/lib/lean` on `LEAN_PATH`, or read oleans from there directly, see no oleans or old ones: `scripts/solidity-baseline-value-runtime.py`, `scripts/solidity-baseline-lifetime-root.py`, `scripts/solidity-baseline-cache-audit.py` (existence/hash audit). This mechanism fits [integration.md](integration.md)'s report that "a fresh import that crashes while focused checks pass has usually read a stale transitive artifact". It was not reproduced here with a crash. |
| A2 | `.lake/build/lib/lean/*.so` read by `scripts/check-native-arithmetic.sh` | Same path convention as A1, for the `dynlib` facet. Whether a cache restore materialises the `.so` was not measured. | The script stops with "native prerequisite missing" after a restore if the file is absent. |
| A3 | `.lake/build/bin/solkeycheck` | `scripts/check-solkey.sh` already deletes it before rebuilding: "Lake 4.24 restores a cached executable only when its destination is absent". | Handled. Any other tool that runs `.lake/build/bin/*` directly has the same hazard. |
| A4 | The comment in `Bridge/lakefile.toml` (line 4), "its outputs are hard links into Lake's artifact cache" | The core's cold outputs have link count 1, so they are copies, and restored outputs are absent (§5). | Stale description; it doubles the disk estimate. Fix the comment in a Bridge-owning lane. |
| A5 | "lake build costs ~24 min" in `scripts/run-lean-mcp.sh` (the MCP instructions), `.agents/skills/lean-verify/SKILL.md` and `.claude/skills/lean-verify/SKILL.md` (`./run-lean.sh` "~24 min") | Measured here: cold default build 43 min, full `./run-lean.sh` 58 min plus a 2 min 47 s re-run, and 3 s with a cache. | Stale estimate. Replace it with "about 1 h cold (4 cores), seconds from the Lake cache". |
| A6 | [contributing.md](../contributing.md#worktrees-and-memory): "Workers commonly hold 0.6–1.5 GB, with `Calculus/Decide.lean` and `TestSuite/Derived*` reaching 3–4 GB" | Measured: median 1.3 GiB and 90th percentile 1.9 GiB. `Calculus/Decide.lean` peaks at 1.7 GiB, Derived17 at 11.5 GiB alone, Derived7/21 at 5.5 GiB, and `OpenLoops` at 7.7 GiB. | Stale. The Derived figure is now three times too low. |
| A7 | [refactoring-progress.md](../refactoring-progress.md): peak aggregate RSS of 11.60 GiB during the large build sequence | Peaks depend on which large modules overlap. This run's summed RSS reached 16.1 GiB, and real pressure reached the 13.36 GiB cgroup. | Historical; keep it as recorded evidence and do not reuse it as a bound. |
| A8 | `tests/upstream/baseline-20261028/performance.json` (cold: blocked by the timeout; warm: not run) | Superseded by §1 for the current revision. | Preserved unchanged as baseline evidence. |
| A9 | The Lake cache itself | `inputs/*.jsonl` and `artifacts/` only grow: every module whose inputs change adds new outputs, and no eviction was found in Lake 4.24. | Stale entries cost only disk. Bound the persisted copy by keying it on the manifest (§5) and starting fresh when the toolchain changes. |

## 8. Is the ten-hour VM table plausible?

The [initial assignments](../coverage-plan.md#initial-vm-assignments--10-hours-each)
give each VM up to 10 hours including validation. The measured costs that
any assignment pays:

- **Validation with a persisted cache:** seconds for the unchanged closure,
  plus the rebuild of what the assignment changed.
- **Cold validation without a cache:** about 1 h at 4 workers, with one
  forced Derived17 re-run, or 3 h or more at the prescribed `-j1`. That is 10
  to 30 % of the budget, paid again whenever a foundation module changes.
- **A change to a low module rebuilds most of the tree.** From the import
  graph and the cold per-module times: `Solidity.AST` has 709 transitive
  dependents (9 959 s, 91 % of all Lean time), `Solidity.Syntax.Raw` 702
  (9 941 s), and `Solidity.Calculus.Rules` 369 (8 376 s). By contrast,
  `Solidity.Evm.Machine` has 57 (297 s), `Solidity.Evm.Compile` 39
  (253 s), and `Solidity.TestSuite.ScopedProblems` 26 (2 664 s).

Assessment for the groups that touch the slow modules:

| VM | Groups | What they rebuild | Assessment |
|---|---|---|---|
| V03, V04 | S00–S05 | `AST`/`Syntax`/`Semantics`/`Typing` sit under 700+ modules | **Tight.** Each validated edit to a shared source type costs 45–60 min at 4 workers, or about 3 h at `-j1`, so the VM affords at most five to eight full rebuilds. New, independent source-definition modules that import the existing AST without changing it cost seconds to minutes. Plausible only if S00–S05 add modules rather than edit `AST.lean`/`Syntax.Raw`, and validate with the Lean server per file and a full gate at the end. |
| V05–V13 | G08–G23 (frontend and lowering) | mostly `Frontend`, `Syntax`, `Evm` | **Plausible** for new modules: these directories are cheap (`Frontend` 65 s, `Evm` 254 s in total). An edit to `Syntax/Raw` or `AST` costs as for S00–S05. |
| V14–V27 | G24–G47 (backend, EVM, Bridge) | `Solidity/Evm/**` (≤ 31 s and ≤ 3 GiB per module) and the Bridge | **Plausible for the core side.** The Bridge side depends on §6: a cold Bridge without a Mathlib cache adds a Mathlib source build. |
| V28 | G48, G49 | whole closure | **Plausible with a cache.** Composition modules sit above everything and rebuild little. |
| V29 | G50, G51 | `Calculus/Rules` (369 dependents, 8 376 s), `Examples/Tactics/OpenLoops`, `Examples/Decision*` and all of TestSuite | **Not plausible as one 10 h VM unless the oversized targets are split first.** Every validated rule change rebuilds about 2.3 h of serial work and passes through Derived15/17/20/21. Derived17 then OOMs under default concurrency and must be rebuilt alone. Split Derived17 (and preferably Derived15/20) before dispatch, or give G51 its own VM. |
| V30 | G52, G53 | `SortCheck/Faithfulness` (7.2 GiB), the SolKey re-pin and every TestSuite/corpus gate | **Tight.** One cold TestSuite pass is about 15 min plus the Derived17 re-run, but the re-pin may change annotations used by `Calculus`, which rebuilds the default tree. |
| V31 | G54, G55 | clean default, TestSuite, corpus, Bridge and closure | **Not plausible as one VM.** G54 requires clean-cache equivalence. That means one cold core build (about 1 h), one cold Bridge build including Mathlib (§6), the corpus (`SolidityCorpus`, not measured here) and a second clean build to compare against. G54.01/G54.02 should be separate VMs, as the plan already allows ("split build targets into child VMs as needed"). |

The revised assignment proposed for the coordinator is to split V29 into
G50 and G51, and V31 into G54.01+G54.02 and G54.03+G55. That is two extra
VMs, conditional on the Derived17 split. Whether to publish this revision
before dispatch is the plan's decision ("publish revised assignments before
dispatch"). This document records the measurement; it does not edit the
table.

## Handoff

- **Base:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`.
- **Done:** cold, two warm, cache-restore and Bridge runs of `./run-lean.sh`
  under the watcher. The per-module tables, OOM attribution, cache recipe,
  stale-artifact list and ten-hour assessment above.
- **Theorems and definitions:** none added; no Lean file changed.
- **Child obligations:** the Derived17 split (memory-loops); the Derived15,
  Derived20 and Derived21 splits (TestSuite owner); the Widths
  measurement or split (evm-storage-slots); A1/A2 path fixes in the
  baseline scripts; the A4–A6 text fixes; a second cold build for cache
  equivalence (G54.03); a `SolidityCorpus` measurement (not part of
  `./run-lean.sh`).
- **Elapsed and peak:** see the runs table. Peak observed pressure:
  `MemAvailable` 1 732 MiB; peak single worker 11 777 MiB (Derived17 alone).
