# Roadmap G02: measured build baseline

Group G02 of the [roadmap](../coverage-plan.md), wave 0: "Measure cold/warm
per-target checking on 16 GiB; publish bounded build/cache reproduction and
split any oversized target. Preserve current baseline evidence and identify
stale artifacts." This group only measures. No Lean module, target,
lakefile or generated file changed. The oversized targets are reported as
[findings](#4-oversized-targets-findings-not-edited) with recommended splits,
because their files belong to other lanes.

- **Base revision:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285` ("Record
  resource and environment decisions"). The branch adds two scripts and this
  document, plus one row in `docs/README.md` and one status line in
  `docs/coverage-plan.md`. The measured Lean sources are the base's.
- **Machine:** the 16 GiB reference VM. It has 4 cores, `MemTotal`
  16 477 352 kB (15.71 GiB), no swap, and about 25 GiB of free disk at the
  start. Lean is v4.24.0 through elan. The shell's memory cgroup (v1) limits
  every command, its children included, to **14 341 885 952 B (13.36 GiB)**
  (`memory.limit_in_bytes`). That cgroup, not `MemAvailable`, decides when
  the OOM killer fires. A VM without such a cgroup would hit the global OOM
  killer only at about 15.7 GiB.
- **Concurrency:** `./run-lean.sh` exactly as committed. Lake ran up to
  **4 concurrent `lean` workers**, one per core. `LEAN_NUM_THREADS` was
  unset, and no `MemoryMax` scope was added. Lake 4.24's `lake --help` lists
  no job-count option. The `-j1` that the
  [VM execution contract](../coverage-plan.md#vm-execution-contract)
  prescribes is Lean's thread flag, passed through `weakLeanArgs` from an
  alternate lakefile
  ([refactoring-progress.md](../refactoring-progress.md#resource-bounds-and-resuming-work)).
  It does not limit how many workers Lake runs at once.
- **Method:** [`scripts/build-measure.py`](../../scripts/build-measure.py)
  runs the command in its own process group. Every 0.5 s (1 s for the Bridge
  run) it samples `/proc/<pid>/status` of each `lean`/`lake` process in that
  group, `/proc/meminfo` (`MemAvailable`) and, since the review, the cgroup's
  usage. After the run it records `.olean` modification times and the
  kernel's OOM lines (`dmesg`).
  [`scripts/build-measure-report.py`](../../scripts/build-measure-report.py)
  joins these samples with the exact per-module times Lake prints
  (`Built M (12s)`). It produces the tables below, and with `--deps`, the
  transitive-dependent costs in [§8](#8-is-the-ten-hour-vm-table-plausible).
  Both scripts use only the standard library. The raw sample files are
  session-local and are not committed; the tables keep every number cited
  here. The runs below used the first version of the watcher, which recorded
  `VmRSS`/`VmHWM` only. The `RssAnon`, cgroup and PID-reuse fields were
  added after the review ([Review](#review)).
- **RSS caveat:** `VmRSS`/`VmHWM` include the file-backed `.olean` pages
  that each worker maps, and those pages are shared between workers. A worker
  that only imports the closure already shows about 1.0–1.2 GiB
  (`Solidity.Roadmap.Contracts`: 1.7 s, 1 170 MiB). Peak RSS figures are
  therefore upper bounds on a worker's own memory, and the summed "lean RSS"
  overstates the total. The kernel's OOM report below gives the anonymous
  (private) memory at the one moment that mattered.

## 1. Runs

| Run | State before | Wall | Result | Peak workers | Min `MemAvailable` | OOM |
|---|---|---:|---|---:|---:|---|
| cold | no `.lake`, empty Lake artifact cache (fresh VM) | **58 min 0 s** (`real 58m0.485s`, `user 129m23s`, `sys 36m11s`) | default `lake build`: "Build completed successfully (718 jobs)" at 2 580 s (**43 min**). `lake build SolkeyTestSuite`: `Solidity.TestSuite.Derived17` "Lean exited with code 137" after 672 s, then "error: build failed", exit 1. `check-solkey.sh` not reached. | 4 | 1 732 MiB | 1 memcg OOM kill (victim `lean` = Derived17), with 4 workers live |
| warm 1 | after cold; only Derived17 (and its dependents `Report`, `SolkeyTestSuite`) missing | **2 min 47 s** | Derived17 alone: **149 s, 11 777 MiB peak `VmHWM`**. Then "Build completed successfully (262 jobs)" and `solkeycheck: 37 mismatch(es)`, exit 1 | 1 | 4 462 MiB | none |
| warm 2 | everything built | **2.1 s** | both builds "completed successfully", 37 mismatches, exit 1 | 0 | 15 219 MiB | none |
| cache restore | `.lake` deleted, Lake artifact cache kept on local disk | **3.1 s** | every module `Fetched`, both builds complete, 37 mismatches, exit 1 | 0 | 14 987 MiB | none |
| Bridge (`--bridge`) | after cache restore; `Bridge/.lake` absent | **17 min 25 s** | core `Fetched`; Mathlib closure built from source; `SolidityBridge.Arith.Widths` fails to elaborate (proof errors, not memory), exit 1 ([§6](#6-bridge-variant)) | 4 | 12 382 MiB | none |

Exit 1 in the warm runs comes from `check-solkey.sh`. It reports
`37 mismatch(es)`, the base's existing drift and unchanged from it. No
annotation file changed here.

**The OOM.** The kernel's report (`dmesg`) reads `Memory cgroup out of
memory: Killed process 8536 (lean) ... anon-rss:10030164kB,
file-rss:2312kB`, with `oom-kill:constraint=CONSTRAINT_MEMCG` on the shell's
cgroup. Its task table at that moment lists four `lean` processes with
anonymous RSS of **9 797, 1 845, 1 051 and 734 MiB (13.1 GiB in total)**,
with almost no file pages left resident. The watcher's samples identify the
four: at 3 313 s the live workers were `Derived20` (started 2 622 s),
`Derived17` (2 642 s), `Derived15` (2 684 s) and `Derived14` (3 261 s).
Derived17's row ends at 3 313.4 s, and the summed RSS drops in the next
sample. Just before the kill, the summed sampled RSS was 13 427 MiB and
`MemAvailable` was 1 833 MiB.

The OOM was therefore driven by anonymous memory, and the victim was
Derived17 at about 9.6 GiB of its own memory. About 20 `Derived*` modules
import `Solidity.TestSuite.ScopedProblems` and become ready together once it
is built. The four long ones (Derived15/17/20/21) started within 62 s of
each other, so under Lake's scheduling they can, and in this run did,
overlap.

Derived17 alone peaked at 11 777 MiB `VmHWM`. In warm 1 the whole system
used at most about 11.3 GiB (`MemTotal` minus the 4 462 MiB minimum
`MemAvailable`), so Derived17's own memory was probably about 10.3–10.8 GiB.
That leaves roughly 2.5–3 GiB under the cgroup limit for any sibling. Small
siblings fit; Derived21 (5.5 GiB peak) or two medium ones do not.

This reproduces the G01 VM's cold run, where Derived15/17 were lost to exit
137 ([roadmap-g01-interfaces.md](roadmap-g01-interfaces.md)). It is
consistent with [integration.md](integration.md)'s report that Derived17
alone exceeded a 10 GiB cap.

**The cgroup ran at its limit for long stretches.** `MemAvailable` stayed
around 1.7–1.9 GiB through much of the run: 1 808 MiB at 1 887 s, while
`Examples.Tactics.OpenLoops` (7 908 MiB peak) and `Examples.DecisionHashes`
(6 478 MiB) overlapped, and 1 732 MiB at 2 710 s, with no kill at either
point. Because `MemAvailable` is system-wide, it is not a cgroup margin.

The cgroup's cumulative counters after the runs were `memory.failcnt`
140 194 490 and about 227 M file refaults. Together with 36 min of `sys`
time, these indicate that the cgroup repeatedly hit its limit and survived
by evicting `.olean` page cache, which the workers then re-read. The
counters are not split by phase, so how much of the slowdown this explains
is not established. The large modules' cold times (Derived17: 672 s
contended against 149 s alone) include this reclaim as well as CPU sharing.
The watcher now samples the cgroup usage so that a future run can attribute
it.

**Time split.** Lake reports 10 292 s for the 733 modules it built, plus
672 s for the killed Derived17: **10 964 s (3.05 h) of summed, contended
`lean` time**. Of this, the default target accounts for 7 590 s and
`SolkeyTestSuite` for 3 374 s. These are wall times of concurrently running,
partly thrashing workers, not single-threaded costs. By directory:

| Directory | Modules | Summed time | Max peak RSS |
|---|---:|---:|---:|
| `Solidity/TestSuite` | 25 | 3 338 s | 9 805 MiB (11 777 MiB alone) |
| `Solidity/Examples/Tactics` | 132 | 2 997 s | 7 908 MiB |
| `Solidity/Calculus` | 283 | 1 757 s | 4 013 MiB |
| `Solidity/Examples` (other) | 55 | 1 302 s | 6 478 MiB |
| `Solidity/Evm` | 52 | 254 s | 3 040 MiB |
| `Solidity` (top level) | 18 | 228 s | 1 806 MiB |
| `Solidity/Semantics` | 49 | 199 s | 2 388 MiB |
| `Solidity/Syntax` | 19 | 197 s | 1 440 MiB |
| `Solidity/Examples/Chains` | 15 | 195 s | 1 962 MiB |
| `Solidity/SortCheck` | 3 | 109 s | 7 357 MiB |
| all others (incl. `LeanTeX`, the executables' roots) | 83 | 388 s | ≤ 2 221 MiB |

The watcher sampled 732 `lean` workers; two very short ones were not seen.
Their median peak RSS is 1 321 MiB and the 90th percentile 1 950 MiB.
59 workers peaked above 2 GiB, 13 above 4 GiB, and only Derived17 above
8 GiB.

**The earlier serial measurement is consistent.**
`tests/upstream/baseline-20261028/performance.json` records a cold run under
one CPU, `LEAN_NUM_THREADS=1`, `-j1` and a 12 GiB cap. It was stopped by a
5 400 s timeout after 546 of 685 default targets (cgroup peak
8 195 923 968 B). The default target's 7 590 s of contended time here, about
2.1 h, is compatible with that: a serial default build does not finish in
90 min. That file is preserved unchanged as historical evidence.

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

The four long TestSuite modules ran concurrently with each other while the
cgroup was reclaiming page cache. Their cold times therefore include CPU
sharing and re-reads of evicted `.olean` pages. Derived17 took 149 s alone
against 672 s contended. Derived15, Derived20 and Derived21 were not
re-measured alone, so their single-worker cost is unknown and may be much
lower.

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

By concurrency (cold, 0.5 s samples; the summed `VmRSS` overcounts shared pages):

| Live workers | Approx. time | Max summed lean RSS (MiB) | Min `MemAvailable` (MiB) |
|---:|---:|---:|---:|
| 1 | 699 s | 5 641 | 9 142 |
| 2 | 265 s | 12 722 | 1 808 |
| 3 | 102 s | 12 955 | 6 390 |
| 4 | 2 371 s | 16 495 | 1 732 |

## 4. Oversized targets (findings, not edited)

A module is **oversized** for the 16 GiB VM if, alone, it needs more than the
12 GiB `MemoryMax` that the
[VM execution contract](../coverage-plan.md#vm-execution-contract) prescribes,
or if it needs so much that a typical sibling cannot run beside it under the
13.36 GiB shell cgroup. A module is **long** if it keeps one worker busy for
more than about 10 minutes. The times behind "long" below are contended cold
times (§2).

| Module | Owner (do not edit here) | Measurement | Recommended split |
|---|---|---|---|
| `Solidity/TestSuite/Derived17.lean` (58 lines, 10 `sol_prove` theorems; `steps := 512`, one `1024`, one `256` followed by `sol_leaf`/`sol_close`) | Codex memory-loops (shared Derived17 repair) | Alone: 11 777 MiB `VmHWM` (about 10.3–10.8 GiB of its own memory) in 149 s. Contended: OOM-killed at 9.6 GiB anonymous memory beside three siblings. | **Oversized** by the second criterion: alone it fits under 12 GiB, but it leaves only about 2.5–3 GiB for siblings. Split it into at least two modules that each import only `ScopedProblems`. Before choosing the cut, the owning lane should measure peak memory per declaration, because this run gives only the per-module peak. If one proof dominates, isolate that theorem; the candidates are `returnLeavesNestedLoops` (`steps := 1024`) and the `invariantForCountsArrayLength` closer. If memory instead grows across theorems, cut the plain while/for/do-while proofs from the storage, nested-return and invariant proofs. Aim for no resulting module above about 6 GiB alone. Until then, build Derived17 before its siblings, not beside them (§5, step 4). |
| `Solidity/TestSuite/Derived15.lean` (172 lines, 48 `sol_prove` theorems) | Codex memory-loops | 3 966 MiB; 669 s contended; alone not measured | **Possibly long.** First measure it alone. If it stays over about 10 min, split it in its existing source order into three modules of about 16 theorems each; the file is "derived in source order", not grouped by topic. |
| `Solidity/TestSuite/Derived20.lean` (3 `sol_auto_theorem`) | TestSuite `Derived*` files are reserved for the memory-loops lane | 2 265 MiB; 722 s contended; alone not measured | **Possibly long.** Measure it alone. If it stays long, use one module per `sol_auto_theorem`, so that the three walks can run in parallel. |
| `Solidity/TestSuite/Derived21.lean` | as above | 5 580 MiB; 627 s contended | Measure it alone before splitting. At 5.5 GiB it is the sibling that cannot fit beside Derived17. |
| `Bridge/SolidityBridge/Arith/Widths.lean` (605 lines) | evm-storage-slots (shared Widths repair) | Fails to elaborate at the base: errors at lines 21, 47, 79, 111 and 501 after 6.9 s, 1 816 MiB (§6). | **Not oversized.** No split is needed for resources; it needs the owning lane's proof repair. Its 12 transitive dependents in the Bridge were not built, so their cost is unmeasured. |
| `Solidity/Examples/Tactics/OpenLoops.lean`, `Solidity/SortCheck/Faithfulness.lean`, `Solidity/Examples/DecisionHashes.lean`, `Solidity/Examples/Tactics/RevertData.lean` | no lane recorded | 6.2–7.7 GiB `VmHWM` peaks, under the cap alone | **Watch list.** None is oversized alone. Two of them overlapped at 1 887 s (OpenLoops with DecisionHashes) while the cgroup was reclaiming. Re-measure after any change that touches them. |

**Splitting has a cost.** Every extra parallel worker maps its own view of
the import closure, about 1 GiB resident when memory is not tight. Splitting
Derived15 or Derived20 shortens the critical path only while memory allows
more workers. Lake starts a module as soon as its imports are built, and
these modules have no ordering edges between them, so the lakefile cannot
order them. The only mitigation that changes no source is to build the large
module first and on its own (§5, step 4).

## 5. Bounded build and cache reproduction

The following cache facts were measured on this VM:

- **Location.** Lake's artifact cache (`enableArtifactCache = true` in
  `lakefile.toml`) is the directory `lake/cache` inside the toolchain:
  `~/.elan/toolchains/leanprover--lean4---v4.24.0` is a symlink to
  `~/.elan/dist/lean-4.24.0-linux`, so the cache is
  `~/.elan/dist/lean-4.24.0-linux/lake/cache`. Installing or removing the
  toolchain with elan replaces or removes it.
- **Size and contents.** After the cold run the cache held 2.6 GB.
  `artifacts/` had 2 207 content-hashed files: 733 `.olean`, 733 `.ilean`,
  733 `.c`, 6 `.o` and 2 executables. `inputs/solidity-lean.jsonl` had 741
  lines, each mapping an input hash to its output hashes.
- **Cold-build outputs.** A cold build also copies its outputs into
  `.lake/build` (2.6 GB). These are copies with link count 1, not hard links,
  so the cache and `.lake/build` together take about 5.2 GB.
- **Restore.** With `.lake` deleted, a restore printed `Fetched` for every
  module and finished in 3.1 s, with the cache already on local disk. It left
  `.lake/build` with only `.ilean`, `.trace` and `.hash` files and the two
  executables (376 MB). **No `.olean` was written to
  `.lake/build/lib/lean`.** Lake and the Lean server read the oleans from the
  cache: `lean_diagnostic_messages` on `Solidity/Roadmap/Contracts.lean` in
  that state returned no errors and no failed dependencies.
- **Not measured:**
  - a restore over an existing, older `.lake/build`;
  - a restore of a cache from a different revision;
  - copying the cache onto a fresh VM (2.6 GB);
  - a rebuild after a restore.

The recipe:

1. **Key.** Use the source revision as the primary key, so that each save
   adds that revision's artifacts. As fallback prefixes use
   `sha256(lean-toolchain ‖ lakefile.toml ‖ lake-manifest.json)`, and then
   the toolchain alone. For the Bridge, also hash `Bridge/lean-toolchain`,
   `Bridge/lakefile.toml` and `Bridge/lake-manifest.json`. Lake recomputes
   every input hash and fetches an artifact only when its input hash matches,
   so an older cache can only miss, and a miss is rebuilt. That is the
   design; it was not tested across revisions here.
2. **Persist.**
   - The core: the resolved cache directory
     `$(readlink -f ~/.elan/toolchains/leanprover--lean4---v4.24.0)/lake/cache`,
     about 2.6 GB.
   - The Bridge: all of `Bridge/.lake`, about 2.0 GB (§6). Its dependency
     packages build into their own `.lake` directories, not into the artifact
     cache.

   `.lake/build` is not needed for Lake itself, but see A1/A2 below. Keep
   everything on disk, not on a RAM-backed `/tmp`
   ([refactoring-progress.md](../refactoring-progress.md#resource-bounds-and-resuming-work)).
3. **Restore and check.** Restore into a checkout with **no** `.lake`, then
   run `./run-lean.sh`. Expect about 3 s plus the copy time, `Fetched` lines,
   and "Build completed successfully" twice. Exit 1 with `37 mismatch(es)` is
   the base's drift (§1). An existing `.lake/build` should be deleted first:
   Lake 4.24 does not overwrite an existing executable (A3), and old oleans
   there are not refreshed (A1).
4. **Cold.** With no cache, the complete gate on this VM took 58 min. It lost
   Derived17 to the OOM, so a 2 min 47 s re-run, which builds it alone, was
   needed: about 61 min in all. The ordering that avoids the kill is to build
   `Solidity.TestSuite.Derived17` by itself (`lake build
   Solidity.TestSuite.Derived17`) before `./run-lean.sh`. Alone it peaked
   11.5 GiB `VmHWM` with no kill. This ordering was not run as one command
   here, because this shell denies a bare `lake build`. The timing is the sum
   of the two measured runs, and the ordering still leaves Derived17's
   siblings free to start during the rest of `SolkeyTestSuite`.
5. **Bound.** The VM contract asks for a process-group `MemoryMax=12G` and
   `MemorySwapMax=0`. This VM has no systemd (`systemd-run` reports "System
   has not been booted with systemd as init system"), so the only bound in
   force was the shell's 13.36 GiB cgroup. On a VM with systemd, the bounded
   form is `systemd-run --scope -p MemoryMax=12G -p MemorySwapMax=0
   ./run-lean.sh`; it is unmeasured. Under 12 GiB, Derived17 alone (about
   10.3–10.8 GiB of its own memory, plus page cache that can be reclaimed)
   probably fits, but with little margin. A worker beside it is likely to
   be killed. A run that may be killed this way needs the step-4 ordering.
6. **Verify a cache against a clean build** (G54.03). This needs a second
   cold build with an empty cache, in a fresh VM, followed by a comparison of
   the output hashes in `inputs/*.jsonl`. This VM ran one cold build, so it
   has only one set of hashes to compare.

## 6. Bridge variant

`./run-lean.sh --bridge` ran after the cache restore, with `Bridge/.lake`
absent, at 1 s sampling.

| Measure | Value |
|---|---|
| Wall | **17 min 25 s** (`real 17m24.517s`, `user 50m37s`, `sys 9m1s`) |
| Result | The core builds were all `Fetched` ("Build completed successfully" twice). The vendor checksums were `OK`. Lake cloned lean-auto, CSLib and Mathlib (`v4.24.0`, `f897ebcf…`) and **built the Mathlib closure from source**: no Mathlib cache was fetched, because `scripts/check-bridge.sh` runs no `lake exe cache get`. The build then ended "Some required targets logged failures: `SolidityBridge.Arith.Widths`", exit 1. `check-solkey.sh` was not reached. |
| Modules built | 1 538 modules (1 400 sampled `lean` workers), plus the failed Widths. Dependency packages: 1 399 modules, 3 020 s summed (Mathlib 979 / 2 448 s, Aesop 130, Batteries 168, Auto 77, Qq 13, ProofWidgets 10, Plausible 9, Cslib 7, LeanSearchClient 4, ImportGraph 2). Bridge's own and vendored modules: 139 modules, 351 s summed (EvmYul 52, SolidityBridge 40, Loom 22, CaseStudies 12, CslibBackport 6, SolidityVelvet 6, Conform 1). |
| Time split | git clones up to about 58 s; dependencies 58–1 011 s; Bridge modules from 385 s on. |
| Memory | Peak worker 2 387 MiB (`Auto.Embedding.LamPrep`, 30 s, the slowest module). The largest Bridge module was `SolidityBridge.LoomExamples` at 1 931 MiB, then `Arith.Widths` at 1 816 MiB. Minimum `MemAvailable` was 12 382 MiB. No OOM, peak 4 workers. |
| Disk | `Bridge/.lake` 2.0 GB: `packages/mathlib/.lake` 717 MB, `auto` 225 MB, `aesop` 102 MB, `batteries` 85 MB, `Bridge/.lake/build` 123 MB. The core cache grew from 2.6 to 2.7 GB. |
| Widths | `SolidityBridge.Arith.Widths` **fails to elaborate at the base**: unsolved goals at 21:99 and 501:82, and `rewrite` "Did not find an occurrence" at 47:6, 79:6 and 111:6, after 6.9 s. This is the proof breakage that the evm-storage-slots lane's shared Widths repair owns, not a resource limit. Its 12 transitive dependents (among them `SolidityBridge.Arith`, `Arith.Lowering` and `Arith.CheckedExecution`, the `SolidityBridge` root and `SolidityBridge.Checks`) were not built and are unmeasured. |

The Bridge is cheap in memory and moderate in time: the 17 min are mostly
the Mathlib source build, which a persisted `Bridge/.lake` removes. A cold
Bridge gate is therefore about 18 min, plus the core's hour if the core
cache is also cold. This holds until Widths is repaired and its dependents
can be measured.

## 7. Stale artifacts and stale claims

No file was changed here; each row names where the fix belongs.

| # | Artifact or claim | Evidence | Effect |
|---|---|---|---|
| A1 | `.lake/build/lib/lean/*.olean` | A restore from the cache writes no `.olean` into `.lake/build` (§5). That a restore over an existing `.lake/build` leaves older copies in place is inferred from this, not observed. | Tools that put `.lake/build/lib/lean` on `LEAN_PATH`, or read oleans from there directly, see no oleans after a restore into a fresh checkout. If the inference holds, they may also see stale ones. Affected: `scripts/solidity-baseline-value-runtime.py`, `scripts/solidity-baseline-lifetime-root.py`, `scripts/solidity-baseline-cache-audit.py` (an existence/hash audit). This mechanism would explain [integration.md](integration.md)'s observation that "a fresh import that crashes while focused checks pass has usually read a stale transitive artifact"; it was not reproduced here. |
| A2 | `.lake/build/lib/lean/*.so`, read by `scripts/check-native-arithmetic.sh` | Same path convention as A1, for the `dynlib` facet. Whether a restore materialises the `.so` was not measured. | If the file is absent after a restore, the script stops with "native prerequisite missing". |
| A3 | `.lake/build/bin/solkeycheck` | `scripts/check-solkey.sh` already deletes it before rebuilding ("Lake 4.24 restores a cached executable only when its destination is absent"). | Handled for that script. Any other tool that runs `.lake/build/bin/*` directly, or a cache restore over an existing `.lake`, has the same hazard. |
| A4 | `Bridge/lakefile.toml` line 4: "its outputs are hard links into Lake's artifact cache" | The core's cold outputs have link count 1 (copies), and restored outputs are absent (§5). | Stale description that understates disk use. The fix belongs to a lane that owns the Bridge. |
| A5 | "lake build costs ~24 min" in `scripts/run-lean-mcp.sh` (the MCP instructions); `./run-lean.sh` "~24 min" in `.agents/skills/lean-verify/SKILL.md` and `.claude/skills/lean-verify/SKILL.md` | Measured here: cold default build 43 min; full `./run-lean.sh` 58 min plus a 2 min 47 s re-run; 3 s from the cache. | Stale estimate. Suggested wording: "about 1 h cold on 4 cores, seconds from the Lake cache". |
| A6 | [contributing.md](../contributing.md#worktrees-and-memory): "Workers commonly hold 0.6–1.5 GB, with `Calculus/Decide.lean` and `TestSuite/Derived*` reaching 3–4 GB" | Measured peak `VmHWM`: median 1.3 GiB, 90th percentile 1.9 GiB, `Calculus/Decide.lean` 1.7 GiB, Derived17 11.5 GiB alone, Derived7/21 5.5 GiB, `OpenLoops` 7.7 GiB. | Stale: Derived17 is about three times the stated figure. |
| A7 | [refactoring-progress.md](../refactoring-progress.md): "peak aggregate RSS of 11.60 GiB during the large build sequence" | Peaks depend on which large modules overlap. Here the anonymous memory at the kill alone was 13.1 GiB. | Historical. Keep it as recorded evidence, but do not reuse it as a bound. |
| A8 | `tests/upstream/baseline-20261028/performance.json` (cold blocked by the timeout; warm not run) | Superseded by §1 for the current revision. | Preserved unchanged as baseline evidence. |
| A9 | The Lake cache itself | `inputs/*.jsonl` and `artifacts/` only grow, because every module whose inputs change adds new outputs. No eviction mechanism was found in Lake 4.24. | Stale entries cost only disk. Start the persisted copy fresh when the toolchain changes. |
| A10 | `scripts/check-bridge.sh` has no Mathlib cache step | The Bridge run built 979 Mathlib modules from source (§6). | A persisted `Bridge/.lake` avoids this. Adding `lake exe cache get` would be a Bridge-owning lane's decision, and it needs the Mathlib cache host to be reachable. |

## 8. Is the ten-hour VM table plausible?

*Since this measurement, the roadmap sizes VMs as lanes of four to ten
hours; the costs below apply per lane.*

The [initial assignments](../coverage-plan.md#vm-assignments-revised-2026-10-29)
give each VM up to 10 hours including validation. These are the measured
costs that any assignment pays:

- **Validation with a persisted cache:** seconds for the unchanged closure,
  plus the rebuild of what the assignment changed.
- **Cold validation without a cache:** about 1 h at 4 workers, including the
  forced Derived17 re-run, plus about 18 min for the Bridge. A cold build
  with Lean's `-j1` thread flag was not measured; Lake still runs 4 workers.
  On one CPU, the earlier run did not finish the default target in 90 min,
  and this run's 7 590 s of contended default-target time suggests about
  2 h (an estimate).
- **A change to a low module rebuilds most of the tree.** These numbers come
  from `scripts/build-measure-report.py --deps`. They count the transitive
  dependents among the modules the cold run built, using the sources'
  `import` lines, and add their contended cold times, with the killed
  Derived17 at 672 s.

  | Module | Dependents | Summed time |
  |---|---:|---:|
  | `Solidity.AST` | 698 | 10 623 s (97 % of all Lean time) |
  | `Solidity.Syntax.Raw` | 691 | 10 610 s |
  | `Solidity.Calculus.Rules` | 365 | 9 031 s |
  | `Solidity.TestSuite.ScopedProblems` | 23 | 3 334 s |
  | `Solidity.Evm.Machine` | 57 | 295 s |
  | `Solidity.Evm.Compile` | 39 | 249 s |

  No incremental rebuild after touching a low module was measured. For
  `AST`, the rebuild is essentially the cold build, so about 1 h of wall
  time.

Assessment for the groups that touch the slow modules:

| VM | Groups | What they rebuild | Assessment |
|---|---|---|---|
| V03, V04 | S00–S05 | `AST`/`Syntax`/`Semantics`/`Typing` sit under about 700 modules | **Tight.** Each validated edit to a shared source type costs about 1 h at 4 workers, so a VM affords about 10 such rebuilds if it does nothing else. New, independent source-definition modules that import the existing AST without changing it cost seconds to minutes. Plausible if S00–S05 mostly add modules, check per file with the Lean server, and run a full gate rarely. |
| V05–V13 | G08–G23 (frontend and lowering) | mostly `Frontend`, `Syntax`, `Evm` | **Plausible** for new modules. These directories are cheap: `Frontend` 65 s and `Evm` 254 s in total. An edit to `Syntax/Raw` or `AST` costs as for S00–S05. |
| V14–V27 | G24–G47 (backend, EVM, Bridge) | `Solidity/Evm/**` (≤ 31 s and ≤ 3 GiB per module) and the Bridge | **Plausible.** A cold Bridge adds about 18 min. Widths and its 12 dependents are unmeasured until the Widths repair lands. |
| V28 | G48, G49 | whole closure | **Plausible with a cache.** Composition modules sit above everything and rebuild little. |
| V29 | G50, G51 | `Calculus/Rules` (365 dependents, 9 031 s), `Examples/Tactics/OpenLoops`, `Examples/Decision*` and all of TestSuite | **Tight.** Each validated rule change is close to a full rebuild (under 1 h at 4 workers). Each such rebuild goes through Derived15/17/20/21, where Derived17 is OOM-killed under the default concurrency unless it is built first. That costs a re-run of about 3 min, plus the risk of another kill. Plausible with the step-4 ordering; more comfortable once Derived17 is split. |
| V30 | G52, G53 | `SortCheck/Faithfulness` (7.2 GiB), the SolKey re-pin and every TestSuite/corpus gate | **Tight.** One cold TestSuite pass is about 15 min plus the Derived17 re-run. If the re-pin changes annotations that `Calculus` uses, the default tree rebuilds too. |
| V31 | G54, G55 | clean default, TestSuite, corpus, Bridge and closure | **Plausible only if nothing fails.** G54 asks for clean-cache equivalence. That means a cold core build (about 1 h), a cold Bridge build including Mathlib (about 18 min), the corpus (`SolidityCorpus`, not measured here), a second clean build to compare against (about 1.3 h) and the audits. About 3–4 h are measured or estimated, but one failure that forces repeated clean builds consumes the budget. The plan already allows splitting G54.01/G54.02 into child VMs ("split build targets into child VMs as needed"). |

The measurements support the ten-hour table with two conditions: a
persisted cache, and a Derived17 build order (or split) that avoids the OOM.
They do not show that any row needs an extra VM. The `SolidityCorpus`
target, the Widths dependents and per-declaration memory remain unmeasured.
This document records the measurement; it does not edit the table.

## Review

The finder and skeptic reviews were run as read-only subagents on the first
pushed draft; neither used the Lean server or a build. Their findings and
the fixes:

- **Units, counts and totals** (finder):
  - The OOM-moment figures had been read as GB instead of KiB. They are now
    13 427 MiB summed and 1 833 MiB available.
  - The over-2, over-4 and over-8 GiB counts were wrong (96/36/19). They are
    59/13/1.
  - The report's regex missed Lake's `ℹ` jobs and took the larger of the
    `:c.o` and `.olean` job times. The total is now 10 964 s, including the
    killed Derived17's 672 s, and the "others" row is 388 s.
  - `Roadmap.Contracts` is 1.7 s, the time Lake prints.
  - The symlink is the toolchain directory, not `lake/cache`.
- **The 12 GiB cap** (both): Derived17 alone (11.5 GiB) is under 12 GiB. The
  false claim about `performance.json` is removed, and Derived17 is now
  classified as oversized by the second criterion only.
- **Dependent counts** (finder): these were not reproducible. They are now
  computed by the committed `build-measure-report.py --deps` over the
  modules the run built, and the killed Derived17 is included.
- **OOM evidence** (skeptic): the watcher's case-sensitive `dmesg` filter
  missed the kernel's kill line. The kernel's task table (anonymous RSS per
  process) is now quoted. The filter is case-insensitive and also matches
  "killed process".
- **Cgroup margin** (skeptic): the "0.2 GiB below the cgroup limit" claim
  rested on the system-wide `MemAvailable` and is removed. The text now
  reports the reclaim counters, and the watcher now samples the cgroup's
  usage.
- **Derived17's own memory and the overlap wording** (both): the 11 777 MiB
  `VmHWM` includes shared olean pages, so Derived17's own memory is given as
  an estimate. "Always overlap" is now "can, and in this run did, overlap".
  The import argument now notes that about 20 `Derived*` modules share
  `ScopedProblems`.
- **`-j1` and the time estimates** (both):
  - 3.04 h was a sum of contended times, not a floor. The text now says so,
    and the serial estimate is about 2 h for the default target.
  - Lean's `-j1` is a thread flag, not a Lake job limit.
  - The arithmetic for V03/V04 (about 10 rebuilds per 10 h) is corrected.
  - V29 is downgraded to "Tight", consistent with V03/V04, and the proposal
    for two extra VMs is withdrawn.
- **Derived15/20/21** (skeptic): their "long" times are contended, and a
  split adds concurrent workers. These are now "possibly long; measure
  alone".
- **Cache safety and key** (skeptic):
  - Restoring a mismatched cache is now described as the design, untested.
  - Restore into a checkout with no `.lake` (A3).
  - A1's stale-copy case is marked as inferred.
  - The primary key is now the source revision, with the manifest and the
    toolchain as fallbacks.
  - The restore time excludes copying the cache onto a fresh VM.
- **Bound** (skeptic): this VM has no systemd. The `systemd-run` form is
  given as unmeasured, and the only bound in force (the 13.36 GiB shell
  cgroup) is stated.
- **Watcher** (both): records are now keyed by PID and start time, which
  survives PID reuse. A process first seen under Lake's name before its
  `exec` is re-read. `RssAnon` and cgroup usage are sampled. Modules that
  Lake timed but the watcher never sampled are listed with Lake's time. The
  module names of Bridge dependency packages are mapped, and the dead
  minutes unit is gone.
- **Not re-run:** single-worker times for Derived15/20/21, an incremental
  touch-and-rebuild, the step-4 ordering as one command, and a restore over
  an existing `.lake`. These are listed under the remaining obligations.

## Handoff

- **Base:** `caf52ecd4dde5d37cbc0098d47de1a01aa218285`.
- **Done:** under the watcher, cold, two warm, cache-restore and Bridge runs
  of `./run-lean.sh`; the per-module tables, the OOM attribution, the cache
  recipe, the stale-artifact list and the ten-hour assessment above.
- **Theorems and definitions:** none added; no Lean file changed.
- **Remaining obligations:**
  - The Derived17 split (memory-loops).
  - Single-worker measurements, then possible splits, of Derived15, Derived20
    and Derived21.
  - The Widths repair, then a measurement of its 12 dependents
    (evm-storage-slots).
  - Path fixes for A1/A2 in the baseline scripts, and the text fixes for
    A4–A6.
  - A second cold build for cache equivalence (G54.03).
  - A `SolidityCorpus` measurement (not part of `./run-lean.sh`).
  - An incremental rebuild after touching `Solidity.AST`.
  - A `MemoryMax=12G` run on a VM with systemd.
- **Elapsed:**
  - The runs: about 1 h 23 min (cold 58 min, warm 2 min 47 s, warm 2 s,
    restore 3 s, Bridge 17 min 25 s).
  - The session: about 2 h, from 12:30 UTC.
- **Peak memory:** one OOM kill, at 13.1 GiB of anonymous `lean` memory
  under the 13.36 GiB cgroup. Minimum `MemAvailable` 1 732 MiB. Peak single
  worker 11 777 MiB `VmHWM` (Derived17 alone).
