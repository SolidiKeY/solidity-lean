# Audit: build and check speed (2026-11-06)

Read-only audit of where Lean build/check time and memory go, at base
`c0228e0e` (branch `cloud/audit-20261106/build-speed`). Scripts are in
[`build-speed-tools/`](build-speed-tools/); nothing outside `docs/audits/` was changed.

## 1. Verdict

A whole module is rarely the problem. The cost sits in a few constructs, and
three of them dominate. **(a) In-file axiom pins**
(`#guard_msgs in #print axioms X`, 22,928 of them in 2,420 modules) cost up to
47 % of a module's wall time. Of their expected outputs, 12,795 could be
parsed, and every one of those names only the three standard axioms, which
`scripts/AxiomAudit.lean` already checks in CI for every declaration. **(b)
Three worked examples** (`Examples/Tactics/OpenLoops`, `Examples/DecisionGaps`,
`Examples/Tactics/RevertData`) take 600 s, 215 s and 163 s on one core. Commits
outside these files rebuild them 16–61 times a week. In OpenLoops, 77 % of the
time is kernel checking of `sol_prove (chunk := 128)` chunks, and each chunk
costs more than the one before. In DecisionGaps, 81 % is two interpreted
`#eval … verdict` lines. **(c) Peak memory**: OpenLoops reaches 9.2 GB,
`Source/Horizon` 7.5 GB and RevertData 6.3 GB. None of the three imports
another, so on a 15 GB VM any two of them running at once can exhaust memory.
A chunk-512 variant of OpenLoops was killed by the OOM killer at 13.9 GB
anonymous RSS. Some things look bad but measure cheap: the 211-deep import
chain (about 0.4 s per tiny module), the 6,038-import library root (6.3 s
warm) and the most-touched modules. The base commit's cache seeding failed on
this VM, so every module would have been built cold. Master fixed that today
(`f160e517f`).

## 2. Method

* **Graph**: `build-speed-tools/import_graph.py` parses the `import` lines
  reachable from the roots `Solidity`, `SolidityExamples`, `SolkeyTestSuite`
  and `SolidityCorpus`. That gives 6,460 modules and 1,082,220 lines. A module
  belongs to the first root that reaches it.
* **Churn**: `build-speed-tools/churn.py` reads `git log --since=7.days
  --name-only` (2026-10-30 to 11-06, after `git fetch --deepen=2000`). A
  module's *rebuild* count is the number of commits that change its file or
  anything it imports. That count is reported two ways. The **upper** figure
  counts every non-merge commit: 1,974 commits touching Lean, which is about
  how often some lane rebuilds the module. The **lower** figure counts only
  master's first-parent history (`--first-parent`): 488 commits, which is
  about how often integration/CI rebuilds it. In this report, hours per week
  means rebuilds × measured single-module wall time. It is an exposure
  estimate, not a measured saving.
* **Timing**: `build-speed-tools/measure.sh` runs one cold elaboration per
  file, one at a time, through `scripts/coord-tools/gate.sh per-file` (that
  is, `lake env lean --tstack=131072 FILE`). It records wall and user+sys time
  with bash `time`, and peak RSS by sampling `/proc/<lean>/status` VmHWM every
  0.2 s. Host: 4 cores, 15 GB RAM, nothing else running. There are 41 files:
  the 15 largest, the 13 largest by lines × rebuilds, 11 named in the docs or
  most touched, `Solidity.lean`, and one failure (`Corpus.TestSuite`: its
  library is not built by `run-lean.sh`, so it was not measured).
* **Profiles**: `build-speed-tools/profile.sh` copies a module to
  `Solidity/Scratch/` at the same directory depth, so relative `solc_import`
  paths still resolve. It adds `set_option profiler true` after the imports,
  elaborates the copy with the same gate, keeps the log in the scratchpad and
  deletes the copy. With `STRIP_PINS=1` it removes every axiom pin; with
  `SED=` it applies an edit (used for chunk sizes). Profiled modules: the top
  8, plus pin A/B runs on 5 modules, alternated, with 2 runs per variant.
* **Static counts**: `build-speed-tools/scan.py` counts `decide`, `#eval`,
  `#print axioms` and similar constructs per module and per area.
* **Cache**: `scripts/ci/fetch-lake-cache.sh`, then `run-lean.sh` (warm: 12.3 s
  wall, 6,461 jobs, all but 9 fetched). `gate.sh per-file` then failed with
  "object file … Decision.olean does not exist" until
  `scripts/ci/restore-lake-artifacts.py` had been run (it placed 12,892
  files).
* **Noise**: two runs of the same file differ by up to 20 % (TargetNested:
  41.9, 35.2 and 35.5 s). The first run after a container restart was 5–30×
  slower because the page cache was cold (§5). Figures are wall seconds
  unless marked CPU.

### Inventory

| Area | Modules | Lines |
|---|---:|---:|
| Backend | 1,932 | 267,090 |
| Yul | 1,777 | 189,998 |
| Lowering | 662 | 96,303 |
| Frontend | 500 | 98,500 |
| Calculus | 386 | 169,660 |
| Examples | 355 | 61,452 |
| Evm | 277 | 45,082 |
| Source | 199 | 41,245 |
| Semantics | 83 | 25,844 |
| all others | 289 | 87,046 |

* Libraries: `Solidity` has 6,046 modules, `SolidityExamples` 355,
  `SolkeyTestSuite` 50 and `SolidityCorpus` 9. Modules whose name ends in
  `*Controls` number 1,408 (205,004 lines). Of those, 740 (122,488 lines) are
  leaves: nothing but the root imports them.
* **Depth** is 211 (`Yul.Views.RetainedLoopPayloadReadbackControls`), and 207
  links of that chain are `Yul.Views` modules averaging about 85 lines.
* **Critical path by lines**: 52,771 lines over 82 modules, from `KeySort` →
  `Syntax.*` → `Semantics.*` → `Calculus.*` → `Examples.DecisionResidue`.
* **Top transitive fan-in** (number of modules a change rebuilds):

| Module | Rebuilds | Module | Rebuilds |
|---|---:|---|---:|
| `Keccak` | 6,043 | `Scope` | 4,461 |
| `KeySort` | 4,506 | `Syntax.Scoped` | 4,460 |
| `AST` | 4,504 | `Syntax.Checked` | 4,447 |
| `SpecSyntax` | 4,499 | `Semantics` | 4,431 |
| `Syntax.Raw` | 4,498 | `Semantics.Value` | 3,813 |
| `Syntax.Grammar` | 4,478 | `Eqns` | 3,703 |
| `Syntax.Contract` | 4,477 | `Semantics.Storage.Values` | 3,702 |
| `Syntax` | 4,475 | `Semantics.Storage.Ops` | 3,701 |
| `RevertBytes` | 4,470 | `Hashes` | 3,690 |
|  |  | `Secp256k1` | 3,684 |
|  |  | `Semantics.Storage.Anon` | 3,682 |

* **20 largest files** (lines): `Backend.StorageOps.TargetNestedArrayTransportControls`
  3,977; `Frontend.ExpressionUniqueness.AxiomPins` 3,905;
  `Calculus.ArrayProperty` 3,142; `Calculus.QuotientCut` 3,081;
  `Backend.MemoryOps.SourceReferenceReadControls` 3,006;
  `Calculus.HashKinds` 2,852; `Calculus.FlattenTotality` 2,777;
  `Frontend.SolcJson.Body` 2,687; `Corpus.TestSuite` 2,624;
  `Backend.MemoryOps.PhysicalStructChildControls` 2,456;
  `Source.Horizon` 2,306; `Calculus.MemSwap` 2,208;
  `Frontend.SolcJson.Contract` 2,177; `Syntax.Elab.Arms` 2,151;
  `Syntax.Elab.Values` 2,142; `Calculus.Decision` 2,072;
  `Calculus.ArrayCut` 2,021; `Source.Unique` 1,965;
  `Backend.MemoryOps.SourceUintReadAssignmentControls` 1,915;
  `Typing.CleanTailRun` 1,802.

### Measured modules (cold, one at a time)

| Module | Wall s | CPU s | Peak RSS GB | Rebuilds/wk (lower–upper) |
|---|---:|---:|---:|---:|
| `Examples.Tactics.OpenLoops` | 599.6 | 595.1 | **9.0** | 21–61 |
| `Source.Horizon` | 222.8 | 700.5 | **7.3** | 1–14 |
| `Examples.DecisionGaps` | 215.4 | 213.9 | 2.2 | 21–57 |
| `Examples.Tactics.RevertData` | 163.4 | 162.8 | **6.2** | 16–48 |
| `Syntax.Elab.Arms` | 86.3 | 96.8 | 1.3 | 11–18 |
| `Examples.Tactics.Bytes` | 75.0 | 77.6 | 1.9 | 16–48 |
| `Examples.Decision` | 61.6 | 61.2 | 1.9 | 21–57 |
| `Backend.MemoryOps.SourceReferenceReadControls` | 48.3 | 70.9 | 1.5 | 12–48 |
| `Backend.StorageOps.TargetNestedArrayTransportControls` | 41.9 | 68.1 | 1.4 | 10–11 |
| `Examples.ProofTree` | 40.4 | 39.0 | 2.1 | 17–50 |
| `Backend.MemoryOps.PhysicalResolvedDeleteControls` | 36.3 | 41.4 | 1.5 | –34 |
| `Calculus.ArrayProperty` | 34.9 | 54.0 | 1.6 | 15–31 |
| `Frontend.SolcJson.Contract` | 31.8 | 33.1 | 1.2 | –15 |
| `Lowering.V08.PrefixControls` | 31.5 | 33.6 | 1.3 | 18–55 |
| `Backend.MemoryOps.PhysicalStructChildControls` | 30.3 | 42.7 | 1.4 | –37 |
| `Backend.MemoryOps.SourceUintReadAssignmentControls` | 29.3 | 40.6 | 1.4 | –55 |
| `Calculus.FlattenTotality` | 28.9 | 44.6 | 1.6 | –31 |
| `Calculus.Decision` | 28.3 | 31.4 | 1.8 | 18–51 |
| `Yul.Checks.LocalBlock` | 28.1 | 30.2 | 2.4 | 22–63 |
| `Solidity` (root; first run / warm) | 25.8 / 6.3 | 7.5 / 6.3 | 3.4 | 482–1,958 |
| `Frontend.ExpressionUniqueness.AxiomPins` | 23.2 | 22.8 | 0.4 | –6 |
| `Yul.Checks.RawContinueLoop` | 18.7 | 31.6 | 1.2 | –98 |
| `Calculus.QuotientCut` | 16.3 | 34.9 | 1.7 | –31 |
| `Calculus.HashKinds` | 16.2 | 40.8 | 1.7 | –9 |
| `Calculus.Decide` | 15.4 | 27.6 | 1.6 | –9 |
| `Frontend.SolcJson.Body` | 14.5 | 18.3 | 1.1 | –9 |
| `Backend.MemoryOps.SourceCalldataUintCopyControls` | 14.4 | 22.1 | 1.3 | –42 |
| `Calculus.CloseScoped.Steps` | 12.7 | 15.6 | 1.2 | –31 |
| `Syntax.Elab.Values` | 11.2 | 15.8 | 1.1 | –14 |
| `Calculus.MemSwap` | 10.6 | 23.0 | 1.5 | –23 |
| `Calculus.ArrayCut` | 9.5 | 21.9 | 1.7 | –31 |
| `Lowering.V08.WorldImageAccessControls` | 7.8 | 9.6 | 1.1 | –53 |
| `Semantics.RunWk` | 7.7 | 14.9 | 1.2 | –9 |
| `Frontend.Import` | 7.7 | 8.5 | 1.1 | –35 |
| `Frontend.Testing` | 7.1 | 7.8 | 1.5 | –70 |
| `Tools.Counterexample` | 6.9 | 10.9 | 1.4 | –36 |
| `Calculus.Close` | 2.5 | 2.6 | 1.0 | –19 |
| `Examples.DecisionHashes` | 1.2 | 1.4 | 1.4 | –53 |
| `Yul.Interfaces.P16` | 1.0 | 0.7 | 1.0 | –120 |
| `Semantics.RevertData` | 0.8 | 0.8 | 0.9 | –5 |

A dash before a number means only the upper figure is shown.

## 3. Top 10 findings

| Rank | Finding | Evidence | Estimated payoff | Effort | Risk |
|---|---|---|---|---|---|
| 1 | In-file axiom pins cost 0–47 % of a module's wall time, and every parsed pin checks only what CI's `AxiomAudit` already checks | Pins removed in 5 modules: −19.9 s (−47 %), −9.3 s (−26 %), −3.9 s, −1.9 s, 0 s; all 12,795 parsed pins ⊆ {propext, Classical.choice, Quot.sound} | ≈ 9 h/wk (lower churn × 0.10 s/pin; range 0–30 h) | M (mechanical, but G07 policy) | Low: CI keeps the audit; pins no longer fail locally |
| 2 | `Examples/Tactics/OpenLoops` takes 600 s single-threaded; 77 % is kernel checking of chunks that each cost more than the last | profile: type checking 461 s over 17 checks growing 3.6 s → 89 s; interpretation 100 s | 3.5–10 h/wk if moved off the per-lane path | S | Low |
| 3 | Peak memory: OpenLoops 9.2 GB, Horizon 7.5 GB, RevertData 6.3 GB, and none imports another | VmHWM samples; chunk-512 variant killed by the OOM killer at 13.9 GB anonymous RSS | prevents OOM-killed builds on 15 GB VMs | S | Removes risk |
| 4 | `Examples/DecisionGaps`: two `#eval … verdict` lines take 179 s of 222 s, run serially | profile: `interpretation of _eval took 117s` (line 83) and `62.3s` (line 113); `Elab.async false` (line 19) | 1.0–2.8 h/wk | S | Low |
| 5 | 740 leaf `*Controls` modules (122 k lines) sit in the `Solidity` library that every checkpoint builds | graph; line-based estimate (±50 %) | 7.7–17.3 h/wk taken off the checkpoint loop (still built at lane end) | M | Medium (later detection) |
| 6 | `Source/Horizon`: 693 s of CPU in `below_go` (`repeat' first` over about 31 lemmas); 7.5 GB | profile: tactic execution 693 s, `refine` 183 s over 276 calls of ≥ 300 ms, `split` 65 s | 0.06–0.9 h/wk wall; memory risk | M | Low |
| 7 | `Syntax/Elab/Arms`: 75 s of 87 s is LCNF code generation, and 779 modules wait on it | profile: `compilation (LCNF base) 75.3s`, single largest 38.2 s | 0.2–0.4 h/wk, plus about 75 s of critical-path latency per edit | M | Low |
| 8 | `Examples/Tactics/RevertData`: 163 s with CPU ≈ wall; kernel checking 127 s, 6.3 GB | profile: type checking 46.7, 25.1, 15.4, 8.6 s; `blocked 122s` | 0.7–2.2 h/wk | S–M | Low |
| 9 | Base cache seeding silently failed, and `gate.sh per-file` failed after a fetched build | `elan which lean` panicked (no default toolchain); "object file … does not exist" | cold vs 12.3 s warm `run-lean.sh`; first half fixed on master `f160e517f` | done / S | Removes risk |
| 10 | 67 files set `Elab.async false`; measured ones run on one core | DecisionGaps CPU/wall = 0.99, Decision 0.99, vs Horizon 3.1 | not measured (needs a stack-overflow test) | M | Medium |

## 4. Findings

### F1. Axiom pins: a large, mostly redundant tax

**Evidence.**
* `scan.py`: 22,928 `#print axioms` in 2,420 modules. The 12,795 whose
  `/-- info: … -/` text parses list only `[propext, Classical.choice,
  Quot.sound]` or a subset; the other 10,133 use other layouts and were not
  classified.
* `scripts/AxiomAudit.lean`, run in CI since `f9791d442`, audits every
  `Solidity` constant against exactly that set.
* A/B runs with `STRIP_PINS=1 profile.sh`, wall s with → without pins:

| Module | Pins | With pins | Without | Saved per pin |
|---|---:|---|---|---:|
| `SourceReferenceReadControls` | 59 | 43.9, 40.5 | 22.9, 21.6 | 0.34 s |
| `TargetNestedArrayTransportControls` | 92 | 35.2, 35.5 | 26.4, 25.7 | 0.10 s |
| `Lowering.V08.SourceMemoryKeccak` | 16 | 16.9 | 13.0 | 0.24 s |
| `Lowering.V07.SignedEnumControls` | 25 | 5.6 | 3.6 | 0.08 s |
| `Semantics.Nondeterminism.Fork` | 10 | 0.84 | 0.85 | 0 s |

* Wall time drops more than CPU time (SourceReferenceReadControls: CPU
  62.6 → 48.2 s, wall −20 s). Each `#print axioms` runs on the command thread
  and must wait for the proof it audits. So the pins both repeat
  axiom-collection work and serialize the end of a module.
* Weighted by churn, there are 316,784 pin rebuilds a week on master's
  history (693,271 per-commit). At the median 0.10 s per pin that is about
  8.8 h/wk; the measured range is 0–30 h/wk.

**First step.** Decide whether per-theorem pins are still required (G07,
`scripts/g07-axiom-pins.json`) now that `AxiomAudit` covers every
declaration (Q1). If not, strip the pins whose set is the standard three,
module by module, and regenerate the pin inventory. As a smaller step, keep
one pin per module on its headline theorem.

### F2. OpenLoops: chunk kernel checks grow with each chunk

**Evidence.**
* `Examples/Tactics/OpenLoops.lean:36-37` (`binomialRowsNine`,
  `sol_prove (chunk := 128)`): 599.6 s wall, 595.1 s CPU, so one core.
* Profile: type checking 461 s, interpretation 100 s, IR compilation 22 s.
* The 17 kernel checks, in order: 15.2, 3.6, 5.4, 7.2, 10.6, 15.0, 18.7, 22.0,
  23.3, 26.1, 31.5, 24.9, 38.1, 43.1, 45.2, 41.5 and 89 s. The interpreter
  steps before them grow the same way (0.35 s → 3.7 s, last 79.2 s). Each
  chunk restarts from a sequent whose state grows with the rows already
  written.
* The file has not changed since 2026-10-24, but edits in its imports rebuild
  it 21–61 times a week (`Frontend.Import` 13 times, `Syntax.Elab.Arms` 9,
  `SolcJson.Contract` 9).
* Its docstring says "about four minutes"; this VM took ten.
* Chunk 512 did not reduce the cost: it was OOM-killed after 360 s at 13.9 GB
  anonymous RSS (dmesg). A chunk-64 run was cut off by a container restart at
  ≥ 6.25 GB with no timing.

**First step.** Move `binomialRowsNine` into its own module in a non-default
"slow examples" library. Build that library in CI/nightly and in
`run-lean.sh --slow`, not at each lane end. Then investigate why later chunks'
kernel terms grow: the state is re-checked inside each chunk. Raising the
chunk size does not help (OOM).

### F3. Memory: three modules can exhaust a 15 GB VM

**Evidence.**
* Peak VmHWM: OpenLoops 9,198 MB, Horizon 7,475 MB, RevertData 6,316 MB, the
  root 3,459 MB; every other measured module is under 2.5 GB.
* None of the three imports another: their closures are 277, 279 and 22
  modules, and none contains another of the three. Lake can therefore start
  any two together on a 4-worker VM, and 9.2 + 6.3 > 15 GB.
* OOM kills are already recorded in `docs/parallelism.md` (P5 table: "3
  killed by the host's OOM killer").
* This audit's chunk-512 run was killed by the cgroup OOM killer.

**First step.** Give these modules a Lake job weight, or build the slow
examples library (F2) with `-j1` after the rest. Record peak RSS next to the
times in docs/parallelism.md so that growth is noticed.

### F4. DecisionGaps: two interpreted `#eval`s are 81 % of the module

**Evidence.**
* `Examples/DecisionGaps.lean:83` (`[gapLedgerWrite, ledgerWriteOk,
  payBalanceOk, payBalanceBad].map verdict`): 117 s.
* `:113` (`[gapColumn, …].map verdict`): 62.3 s.
* Both are `interpretation of _eval` in the profile. The whole file takes
  222 s, and `:19` sets `Elab.async false`, so the time is serial.
* The same file proves each formula's fragment coverage for the kernel
  (`*_covered` by `decide +kernel`, e.g. `:93-95`). The `#eval`s are the only
  pins of the concrete verdict values, computed by the decision procedure
  ("the `#eval` pins the compiled ones", `Examples/Decision.lean:26`). Moving
  them out of the default build therefore delays, but does not lose, that
  check.
* Rebuilt 21–57 times a week.

**First step.** Move those two `#eval` pins into a controls module outside
the default targets, or shrink them to one goal each. Alternatively,
precompile the decision modules so `#eval` runs native code; this was not
measured.

### F5. Leaf controls in the checkpoint library

**Evidence.**
* There are 1,408 `*Controls` modules: 205 k lines, 20 % of the library.
  Of them, 740 (122 k lines) are imported by nothing but the root.
* `gate.sh checkpoint` builds `lake build Solidity`, which includes them.
* Estimate from the 8 measured controls (0.0137 s/line + 0.4 s; individual
  errors ±50 %): leaf controls are 17 % of the library's rebuild time,
  7.7–17.3 h/wk.
* The same move for the examples cut the checkpoint gate from 1,476 s to
  188 s (`docs/parallelism.md`, P5).

**First step.** Have `register.sh` emit a `SolidityControls` root for leaf
`*Controls`, kept as a default target, and have `gate.sh checkpoint` skip it
unless `GATE_CONTROLS=1`.

### F6. Horizon: `below_go` search

**Evidence.**
* `Source/Horizon.lean:135-147`: `below_go` is `repeat' (first | … | (first
  $[| with_reducible apply $ls]*) | (refine Below.bind ?_ ?_) | … | split |
  dsimp only)`.
* `:491-512` and onward pass it the same list of 31 lemmas at every step.
* Profile: tactic execution 693 s of CPU (wall 223 s on 4 cores);
  `refine` ≥ 300 ms 276 times (183 s); `split` 65 s; one declaration's
  elaboration 92.4 s; attribute application 90 s.
* Peak RSS 7.5 GB (F3). It is rebuilt rarely (1–14 times a week).

**First step.** For each `*_step` theorem, pass only the lemmas for the
callees of that function, and try `Below.bind` before the `apply` list. Check
that the profiler's `refine` total drops.

### F7. `Syntax/Elab/Arms`: code generation on the critical path

**Evidence.**
* Profile: `compilation (LCNF base) 75.3s` of 86.9 s wall; elaboration is
  only 7.9 s. The largest single compilation (38.2 s) follows the first
  definition, consistent with `hoistWith` (`:82-675`, 594 lines). Mapping the
  later ones (16.6, 8.9, 8.4 s) to `elabStmt1With` (`:1629-2148`) and the
  others is likely but not certain.
* Fan-in 779 modules; touched 6–9 times a week. Each edit puts about 86 s of
  serial work in front of all of them.

**First step.** Split `hoistWith` and `elabStmt1With` into per-constructor
helper definitions, and re-profile LCNF base time.

### F8. Tactics/RevertData: kernel checks, serial

**Evidence.**
* 163 s wall, 162.8 s CPU. Profile: type checking 127 s, mostly four
  declarations (46.7, 25.1, 15.4 and 8.6 s); simp 24 s; `blocked 122s`.
* Candidates by size are `symbolicCustom` (`:191-193`, `sol_prove (steps :=
  2048)`) and `externalReason` (`:207-209`). The profiler prints no positions,
  so this mapping is not confirmed.
* 6.3 GB peak; rebuilt 16–48 times a week.

**First step.** Profile with `trace.profiler` to attach declaration names,
then split the top two theorems into their own module (as P2 did for
`Decision`).

### F9. Cache seeding and per-file checks after a fetch

**Evidence.**
* At the base, `fetch-lake-cache.sh` printed `binary not found` (an elan
  panic) and `::warning::lake-cache install failed; building cold`. The pack's
  `install.sh` `cd`s into the pack directory and calls `elan which lean`, which
  needs a default toolchain; this VM has none (`elan which lean` from `/tmp`:
  "no active toolchain").
* Installing with the path that `install.sh` would have computed gave
  `+6446 module entries`, and `run-lean.sh` then took 12.3 s.
* Master's `f160e517f` fetch script ran successfully on this VM
  (`+0 module entries; pack master f160e517fd`).
* Separately, after a fetched build, `gate.sh per-file` failed (`object file
  '…/Solidity/Calculus/Decision.olean' … does not exist`) until
  `scripts/ci/restore-lake-artifacts.py` had run. CI runs that script; the
  lanes' instructions do not. `f160e517f` switched per-file to `lake lean`;
  whether that removes the need was not verified.

**First step.** Run `restore-lake-artifacts.py` at the end of
`fetch-lake-cache.sh` (with the cache path resolved in the repository root),
and have the fetch fail loudly for lanes instead of warning.

### F10. `Elab.async false` serializes 67 modules

**Evidence.**
* `grep -l 'Elab.async false'`: 67 files, mostly `Examples/Decision*`.
* Measured ones use one core: DecisionGaps CPU/wall 0.99, Decision 0.99,
  against Horizon 3.1 and SourceReferenceReadControls 1.5.
* The stated reason (`DecisionGaps.lean:17-18`) is that parallel evaluations
  overflow the stack (exit 135).

**First step.** On one file, try `--tstack` (or a per-task stack size)
together with `Elab.async true`. If it is stable, the payoff is up to
(cores − 1)/cores of these files' wall time. Not measured: listed as an open
question.

## 5. Things that look bad but are fine

* **Depth 211, a chain of 207 `Yul.Views` modules.** A tiny module costs
  about 0.4 s: `Yul.Views.PrimitiveOwnershipPreservation` (33 lines, 217
  imports) 0.55 and 0.36 s; `RetainedLoopSourceWrite` 0.37 s; `Keccak` 0.43 s;
  the chain's end, `RetainedLoopPayloadReadbackControls`, 3.1 s. That is about
  1.5–2 min of serial latency at most.
* **Root `Solidity.lean` (6,038 imports, touched by 1,211 of 1,974
  commits).** It takes 6.3 s warm (25.8 s on the first run, when the page
  cache was cold) and 3.4 GB. Lower figure: 482 rebuilds × 6.3 s ≈ 0.8 h/wk.
  The docs say 1.5–4.3 s at 3,487 modules, so the cost grows roughly with the
  import count. Nothing imports the root except `scripts/AxiomAudit.lean`.
* **Most-touched modules are cheap.** `Yul.Interfaces.P16` (43 touches, 120
  rebuilds) 1.0 s; `Frontend.Testing` 7.1 s; `Frontend.Import` 7.7 s.
* **Huge fan-in at the bottom.** `Keccak` (6,043 dependents) and `KeySort`
  (4,506) are rarely edited (0 and 0 touches in 7 days).
* **The largest files are not the slowest.**
  `Frontend.ExpressionUniqueness.AxiomPins` (3,905 lines) takes 23 s and is
  rebuilt 6 times; `Examples.DecisionHashes` (formerly 417 s) now takes 1.2 s
  after the P5 split.
* **First-run timings after a container restart** were 5–30× higher (Fork:
  27.1 s, then 0.84 s; SourceMemoryKeccak: 85.0 s, then 16.9 s). This comes
  from the page cache, not Lean, so those runs were discarded.

## 6. Skeptic pass

A read-only pass, without the Lean server, tried to refute each finding;
outcomes are in [§6a](#6a-skeptic-results).

## 7. Open questions for the user

* **Q1 [Axiom pins]** Are per-theorem `#guard_msgs in #print axioms` pins
  still required now that `scripts/AxiomAudit.lean` audits every declaration
  in CI? Options:
  * Drop the pins with the standard set (largest saving; the pins stop
    failing locally).
  * Keep one headline pin per module.
  * Keep all of them (no saving).
* **Q2 [Slow examples]** May the three slowest examples (OpenLoops,
  DecisionGaps' two `#eval`s, RevertData's large theorems) move to a
  non-default library built only by CI or nightly? Options:
  * Yes, CI-only.
  * Yes, but also at lane end with `--slow`.
  * No, keep them in the default targets.
