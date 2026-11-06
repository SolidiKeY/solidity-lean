# Audit: build and check speed (2026-11-06)

Read-only audit of where Lean build/check time and memory go, at base
`c0228e0e` (branch `cloud/audit-20261106/build-speed`). Scripts are in
[`build-speed-tools/`](build-speed-tools/); nothing outside `docs/audits/` was changed.

## 1. Verdict

A whole module is rarely the problem. The cost sits in a few constructs, and
three of them dominate. **(a) In-file axiom pins**
(`#guard_msgs in #print axioms X`, 22,928 of them in 2,420 modules) cost
0–47 % of a module's wall time in five A/B tests. Of the 12,795 whose expected
output parses, 9,403 already list all three standard axioms
(`propext, Classical.choice, Quot.sound`). Such a pin cannot grow without
leaving the set that `scripts/AxiomAudit.lean` enforces in CI for every
declaration, so it checks nothing that CI does not. The other pins (subsets,
"no axioms", the 23 `requiredPins`) add real checks, because
`scripts/check-axiom-pins.mjs` keeps sets exact and non-growing. Dropping the
9,403 is a policy decision (Q1). **(b)
Three worked examples** (`Examples/Tactics/OpenLoops`, `Examples/DecisionGaps`,
`Examples/Tactics/RevertData`) take 600 s, 215 s and 163 s on one core. Commits
outside these files rebuild them 16–61 times a week. In OpenLoops, 75 % of the
time is kernel checking of 16 `sol_prove (chunk := 128)` chunks, whose cost
roughly grows chunk by chunk (3.6 s → 89 s). In DecisionGaps, 81 % is two interpreted
`#eval … verdict` lines. **(c) Peak memory**: OpenLoops reaches 9.0 GiB
VmHWM, `Source/Horizon` 7.3 GiB and RevertData 6.2 GiB. None of the three
imports another, so Lake may run two at once on a 15 GB VM; VmHWM includes
shared `.olean` mappings (about 1 GiB even for a trivial module), so whether
two together exhaust memory is near the margin, not certain. Some things look bad but measure cheap: the 211-deep import
chain (about 0.4 s per tiny module), the 6,038-import library root (6.3 s
warm) and the most-touched modules. The base commit's cache seeding failed on
this VM, so every module would have been built cold; master's `f160e517f`
(today) no longer fails here, though re-seeding a fresh cache with it was not
re-verified.

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
  `#print axioms` and similar constructs per module and per area;
  `build-speed-tools/pins.py` classifies the pins' expected axiom sets and
  weighs them by churn.
* **Cache**: `scripts/ci/fetch-lake-cache.sh`, then `run-lean.sh` (warm: 12.3 s
  wall, 6,461 jobs, all but 9 fetched). `gate.sh per-file` then failed with
  "object file … Decision.olean does not exist" until
  `scripts/ci/restore-lake-artifacts.py` had been run (it placed 12,892
  files).
* **Noise**: repeated profiler runs agree within about 10 % (TargetNested
  35.2 and 35.5 s; SourceReferenceReadControls 43.9 and 40.5 s); the plain
  `measure.sh` run of TargetNested gave 41.9 s. The first run after a
  container restart was 3.5–32× slower because the page cache was cold (§5).
  Figures are wall seconds unless marked CPU; memory is VmHWM in GiB.

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
  leaves: nothing but the root imports them. (Name filters differ slightly;
  a looser suffix match finds 1,412.)
* **Depth** is 211 (`Yul.Views.RetainedLoopPayloadReadbackControls`), and 207
  links of that chain are `Yul.Views` modules averaging about 79 lines.
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

| Module | Wall s | CPU s | Peak RSS GiB | Rebuilds/wk (lower–upper) |
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
| 1 | In-file axiom pins cost 0–47 % of a module's wall time; 9,403 of 12,795 parsed pins list all three standard axioms and so check nothing CI's `AxiomAudit` does not | Pins removed in 5 modules: −19.9 s (−47 %), −9.3 s (−26 %), −3.9 s, −1.9 s, 0 s | ≈ 9 h/wk (lower churn × median 0.10 s/pin; range 0–30 h; extrapolated from 5 pin-heavy modules) | M (mechanical, but G07 policy) | Low if limited to full-set pins and not `requiredPins`; payoff then scales by about 9.4/12.8 of the parsed pins |
| 2 | `Examples/Tactics/OpenLoops` takes 600 s single-threaded; 75 % is kernel checking of 16 chunks whose cost roughly grows | profile: 16 chunk checks 3.6 s → 89 s (446 s); interpretation 100 s | lane-end time only: ≤ 61 × 600 s ≈ 10 h/wk (upper, per-commit); CI keeps building it | S | Low; needs Q2 |
| 3 | Peak memory: OpenLoops 9.0 GiB, Horizon 7.3 GiB, RevertData 6.2 GiB, and none imports another | VmHWM samples (include ~1 GiB shared .olean maps) | margin against OOM on 15 GB VMs | S | Reduces risk |
| 4 | `Examples/DecisionGaps`: two `#eval … verdict` lines take 179 s of 222 s, run serially | profile: `interpretation of _eval took 117s` (line 83) and `62.3s` (line 113); `Elab.async false` (line 19) | ≤ 2.8 h/wk of lane time (upper); CI keeps the check | S | Low; needs Q2 |
| 5 | 740 leaf `*Controls` modules (122 k lines) sit in the `Solidity` library that every checkpoint builds | graph; line-based estimate fitted on large controls | ≤ 17 h/wk of checkpoint time (upper; still built at lane end and CI) | M | Medium: audits must import the new root |
| 6 | `Source/Horizon`: 700 s CPU / 223 s wall, dominated by tactic execution (`below_go`'s `repeat' first` over 31 lemmas is the likely source); 7.3 GiB | profile: `refine` 183 s over 276 calls ≥ 300 ms, `split` 65 s | 0.06–0.9 h/wk wall; memory | M | Low–medium |
| 7 | `Syntax/Elab/Arms`: 75 s of 87 s is LCNF code generation, and 779 modules wait on it | profile: `compilation (LCNF base) 75.3s`, single largest 38.2 s | 0.2–0.4 h/wk, plus about 75 s of critical-path latency per edit | M | Low |
| 8 | `Examples/Tactics/RevertData`: 163 s with CPU ≈ wall; kernel checking 127 s, 6.2 GiB | profile: type checking 46.7, 25.1, 15.4, 8.6 s; `blocked 122s` | 0.7–2.2 h/wk | S–M | Low |
| 9 | Base cache seeding silently failed, and `gate.sh per-file` failed after a fetched build | `elan which lean` panicked (no default toolchain); "object file … does not exist" | cold vs 12.3 s warm `run-lean.sh`; master `f160e517f` no longer panics (seeding itself not re-verified) | done / S | Removes risk |
| 10 | 67 files set `Elab.async false` (stack overflow, exit 135) | DecisionGaps and Decision run at CPU/wall 0.99 (but so do OpenLoops/RevertData without it) | not measured | M | Medium |

## 4. Findings

### F1. Axiom pins: a large, mostly redundant tax

**Evidence.**
* `pins.py`: 22,928 `#print axioms` in 2,420 modules. Of the 12,795 whose
  `/-- info: … -/` text parses, 9,403 list exactly `[propext,
  Classical.choice, Quot.sound]`, 2,500 a proper subset and 892 "does not
  depend on any axioms";
  the other 10,133 use other layouts and were not classified.
* `scripts/AxiomAudit.lean`, run in CI since `f9791d442`, audits every
  `Solidity` constant against that set. The pins check more:
  `scripts/check-axiom-pins.mjs` requires a recorded pin to stay and its set
  not to grow (`docs/feature-work/roadmap-g07-gates.md:244`), so an
  axiom-free theorem gaining `propext` is caught only by a pin; and
  `scripts/g07-baseline.json` lists 23 `requiredPins`. A pin that already
  lists all three cannot grow without breaking `AxiomAudit`, so for those
  9,403 the pin is redundant.
* A/B runs with `STRIP_PINS=1 profile.sh`, wall s with → without pins:

| Module | Pins | With pins | Without | Saved per pin |
|---|---:|---|---|---:|
| `SourceReferenceReadControls` | 59 | 43.9, 40.5 | 22.9, 21.6 | 0.34 s |
| `TargetNestedArrayTransportControls` | 92 | 35.2, 35.5 | 26.4, 25.7 | 0.10 s |
| `Lowering.V08.SourceMemoryKeccak` | 16 | 16.9 | 13.0 | 0.24 s |
| `Lowering.V07.SignedEnumControls` | 25 | 5.6 | 3.6 | 0.08 s |
| `Semantics.Nondeterminism.Fork` | 10 | 0.84 | 0.85 | 0 s |

* Wall time drops more than user CPU in 3 of 4 modules
  (SourceReferenceReadControls: CPU 62.6 → 48.2 s, wall −20 s). This is
  consistent with each `#print axioms` waiting on the command thread for the
  proof it audits, which serializes the end of a module; it was not shown
  directly.
* Weighted by churn, there are 316,784 pin rebuilds a week on master's
  history (693,271 per-commit); 83,696 of them are in leaf controls, which
  overlaps F5. At the median 0.10 s per pin that is about 8.8 h/wk; at
  0.34 s, 30 h/wk. The five modules were chosen for having many pins, so the
  figure is an extrapolation.

**First step.** Decide whether exact, non-growing per-theorem pins are
still wanted (G07, `scripts/g07-axiom-pins.json`) now that `AxiomAudit`
bounds every declaration (Q1). If not, strip the 9,403 pins whose set is the
full standard three (they add nothing beyond `AxiomAudit`'s bound), never
`requiredPins`, subset or "no axioms" pins, then regenerate the inventory
with `check-axiom-pins.mjs --write`. A
cheaper alternative keeping the guarantee: move the pins into one
`*AxiomPins` module per area, off the checkpoint path, as
`Frontend.ExpressionUniqueness.AxiomPins` already does (23 s for its whole
area).

### F2. OpenLoops: chunk kernel checks grow with each chunk

**Evidence.**
* `Examples/Tactics/OpenLoops.lean:36-37` (`binomialRowsNine`,
  `sol_prove (chunk := 128)`): 599.6 s wall, 595.1 s CPU, so one core.
* Profile: type checking 461 s, interpretation 100 s, IR compilation 22 s.
* Kernel checks in order: 15.2 s (follows an interpretation in a different
  hygiene context, so almost certainly `binomialFaithfulRowsSmall`), then 16
  chunks of `binomialRowsNine`: 3.6, 5.4, 7.2, 10.6, 15.0, 18.7, 22.0, 23.3,
  26.1, 31.5, 24.9, 38.1, 43.1, 45.2, 41.5 and 89 s (446 s, 75 %). The
  interpreter steps before them grow likewise (0.35 s → 3.7 s, last 79.2 s).
  That the growth comes from the state carried between chunks is a
  hypothesis.
* The file has not changed since 2026-10-24, but edits in its imports rebuild
  it 21–61 times a week (`Frontend.Import` 13 times, `Syntax.Elab.Arms` 9,
  `SolcJson.Contract` 9).
* Its docstring says "about four minutes"; this VM took ten.
* Chunk 512 was no escape: the variant was OOM-killed after 360 s at 13,865,132 kB
  anonymous RSS (cgroup OOM message in dmesg). A chunk-64 run was cut off by a
  container restart at ≥ 6.0 GiB with no timing.
* Payoff caveat: lanes already skip examples at checkpoints unless they touch
  Syntax/Semantics/Calculus (`gate.sh` checkpoint, `docs/parallelism.md` P5),
  and CI would keep building it, so the saving is lane-end time only; 61 × 600 s
  is an upper bound.

**First step.** First instrument: find which term grows between chunks
(profile with `trace.profiler` and print the chunk's sequent size). Moving
`binomialRowsNine` to a non-default library would reverse the documented
decision that examples stay default targets (`docs/parallelism.md` P5,
`322212cf7`), so it waits on Q2. Raising the chunk size does not help.

### F3. Memory: three modules near the limit of a 15 GB VM

**Evidence.**
* Peak VmHWM: OpenLoops 9,198 MiB, Horizon 7,475 MiB, RevertData 6,316 MiB,
  the root 3,459 MiB; every other measured module is under 2.5 GiB. VmHWM
  includes shared `.olean` mappings: a trivial module already peaks near
  1 GiB (`Yul.Interfaces.P16`, `Calculus.Close`), so two of these together
  are near, not clearly over, a 15 GB VM.
* None of the three imports another (closures: OpenLoops 277, RevertData
  279, Horizon 22 modules), so Lake can schedule them together.
* The OOM kills in `docs/parallelism.md` P5 happened while another session
  built, not from these modules together; this audit saw no OOM in normal
  builds (only the chunk-512 variant).

**First step.** Record peak RSS next to module times (as `measure.sh` does)
so growth is noticed, and check whether Lake can limit concurrency for
selected modules; the fallback is building the heavy examples last with
`-j1`. Lake per-module job weights were not verified to exist.

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
* Estimate from the 8 measured controls (0.0137 s/line + 0.4 s, fitted on
  files of 1,448–3,977 lines and applied to smaller leaves; individual errors
  ±50 %): leaf controls are 17 % of the library's rebuild time, up to
  17.3 h/wk on the per-commit figure. The 7.7 h first-parent figure is CI's,
  which would keep building them, so it is not a checkpoint saving.
* The same move for the examples cut the checkpoint gate from 1,476 s to
  188 s (`docs/parallelism.md`, P5).

**First step.** Have `register.sh` emit a `SolidityControls` root for leaf
`*Controls`, kept as a default target, and have `gate.sh checkpoint` skip it
unless `GATE_CONTROLS=1`. `scripts/AxiomAudit.lean` and `TrustAudit.lean`
must then import the new root, or 740 modules drop out of the audit; the
orphan check, `register.sh` and the root list in AGENTS.md change too.

### F6. Horizon: `below_go` search

**Evidence.**
* `Source/Horizon.lean:135-147`: `below_go` is `repeat' (first | … | (first
  $[| with_reducible apply $ls]*) | (refine Below.bind ?_ ?_) | … | split |
  dsimp only)`.
* `:491-512` and onward pass it the same list of 31 lemmas at every step.
* Measured 700 s CPU, 223 s wall. Profile categories (which overlap and sum
  past total CPU): tactic execution 693 s, `refine` ≥ 300 ms 276 times
  (183 s, `refine Below.bind` is in `below_go`), `split` 65 s, one
  declaration's elaboration 92.4 s, attribute application 90 s, simp 62 s.
  Attributing the bulk to `below_go` is likely, not proven.
* Peak RSS 7.3 GiB (F3). It is rebuilt rarely (1–14 times a week).

**First step.** For each `*_step` theorem, pass only the lemmas for the
callees of that function, and re-profile. Reordering `first` (e.g.
`Below.bind` before the `apply` list) can change which branch succeeds, so
check every proof still closes.

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
* `symbolicCustom` (`:191-193`, `sol_prove (steps := 2048)`) is a likely
  source of the 46.7 s check; the 25.1 s and 8.6 s checks are printed after
  the `#eval` region near `:241`, so they are later theorems. The profiler
  prints no positions, so the mapping is not confirmed.
* CPU ≈ wall here although the file does not set `Elab.async false`.
* 6.2 GiB peak; rebuilt 16–48 times a week.

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
* Master's `f160e517f` fetch script no longer panics on this VM
  (`+0 module entries; pack master f160e517fd`). Nothing new was installed,
  so seeding a fresh cache with it was not re-verified.
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
* Measured ones use one core: DecisionGaps CPU/wall 0.99, Decision 0.99.
  This does not isolate the option: OpenLoops and RevertData do not set it and
  also run near 1.
* The stated reason (`DecisionGaps.lean:17-18`) is that parallel evaluations
  overflow the stack (exit 135), with `--tstack=131072` already in effect.
* Full builds already run 4 Lake jobs, and `gate.sh touched` sets
  `LEAN_NUM_THREADS=1`, so the in-file parallelism would mainly shorten the
  tail of a build.

**First step.** On DecisionGaps alone, try a larger `--tstack` with
`Elab.async true` and check for exit 135. Not measured; low priority.

## 5. Things that look bad but are fine

* **Depth 211, a chain of 207 `Yul.Views` modules.** A tiny module costs
  about 0.4 s: `Yul.Views.PrimitiveOwnershipPreservation` (33 lines, 217
  imports) 0.55 and 0.36 s; `RetainedLoopSourceWrite` 0.37 s; `Keccak` 0.43 s;
  the chain's end, `RetainedLoopPayloadReadbackControls`, 3.1 s. That is about
  1.5–2 min of serial latency at most (Lake's own per-job overhead not
  measured).
* **Root `Solidity.lean` (6,038 imports, touched by 1,211 of 1,974
  commits).** It takes 6.3 s warm (25.8 s on the first run, when the page
  cache was cold) and 3.4 GiB. Lower figure: 482 rebuilds × 6.3 s ≈ 0.8 h/wk.
  `docs/parallelism.md` P5 records 1.5–4.3 s for rebuilding the root, at a
  time it reached 3,487 modules, so the cost grows roughly with the import
  count. Nothing imports the root except `scripts/AxiomAudit.lean`.
* **Most-touched modules are cheap.** `Yul.Interfaces.P16` (43 touches, 120
  rebuilds) 1.0 s; `Frontend.Testing` 7.1 s; `Frontend.Import` 7.7 s.
* **Huge fan-in at the bottom.** `Keccak` (6,043 dependents) and `KeySort`
  (4,506) are rarely edited (0 and 0 touches in 7 days).
* **The largest files are not the slowest.**
  `Frontend.ExpressionUniqueness.AxiomPins` (3,905 lines) takes 23 s and is
  rebuilt 6 times. (`Examples.DecisionHashes` takes 1.2 s, but its checks
  moved to `DecisionHashesChecks`, which was not measured.)
* **First-run timings after a container restart** were 3.5–32× higher (Fork:
  27.1 s, then 0.84 s; SignedEnumControls: 19.5 s, then 5.6 s;
  SourceMemoryKeccak: 85.0 s, then 16.9 s). This comes
  from the page cache, not Lean, so those runs were discarded.

## 6. Skeptic pass

A separate read-only reviewer (no builds, no Lean server) tried to refute
each finding against the raw logs, the cited lines and the project docs.
Outcomes, all applied above:

| Finding | Verdict | Change |
|---|---|---|
| F1 pins | Downgraded | Pins also enforce exact, non-growing sets and 23 `requiredPins`, so they are not redundant with `AxiomAudit`; the serialization explanation is now "consistent with"; the extrapolation from 5 chosen modules is flagged; overlap with F5 noted; counts now come from `pins.py` |
| F2 OpenLoops | Downgraded | 16 chunk checks, not 17 (the first is the other theorem); growth not monotone; payoff counts only lane-end time; moving it reverses a documented decision (Q2) |
| F3 memory | Downgraded | VmHWM counts shared `.olean` maps, so overlap is near the limit, not over it; the P5 OOMs had another cause; "Lake job weights" not known to exist; risk "reduced", not "removed" |
| F4 DecisionGaps | Stands | Same churn caveat as F2 |
| F5 leaf controls | Downgraded | Fit is from large files; the 7.7 h CI figure is not a checkpoint saving; audits must import the new root |
| F6 Horizon | Downgraded | Profiler categories overlap; attribution to `below_go` is likely, not proven; reordering `first` can break proofs |
| F7 Arms | Stands | — |
| F8 RevertData | Downgraded (small) | Candidate theorems corrected |
| F9 cache | Stands | "+0 entries" shows only that the panic is gone |
| F10 Elab.async | Downgraded | CPU ≈ wall does not isolate the option; `--tstack` already set; payoff unmeasured, low priority |

Also corrected: closure sizes, GB vs GiB, "5–30×" → 3.5–32×, average
`Yul.Views` size 79 lines, the TargetNested noise comparison, and the source
of the root's 1.5–4.3 s. One scratchpad log
(`SourceReferenceReadControls.nopins` in `prof/`) was produced before the pin
regex was fixed and still contains the pins; only the `ab/` A/B runs are
used for F1.

## 7. Open questions for the user

* **Q1 [Axiom pins]** Are exact, per-theorem `#guard_msgs in #print
  axioms` pins still required now that `scripts/AxiomAudit.lean` bounds
  every declaration in CI? Options:
  * Drop the 9,403 pins whose set is already all three standard axioms,
    keeping `requiredPins`, subset and "no axioms" pins (largest saving; no
    check is lost, since CI's `AxiomAudit` bounds every declaration by the
    same three).
  * Move the pins to one `*AxiomPins` module per area, off the checkpoint
    path (keeps every check; saving smaller and later).
  * Keep everything as is (no saving).
* **Q2 [Slow examples]** May the three slowest examples (OpenLoops,
  DecisionGaps' two `#eval`s, RevertData's large theorems) move to a
  non-default library built only by CI or nightly? Options:
  * Yes, CI-only.
  * Yes, but also at lane end with `--slow`.
  * No, keep them in the default targets.
