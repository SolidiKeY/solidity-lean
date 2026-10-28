# Revert-power handoff

Branch `codex/revert-payload-settings`; implementation `64bfd02e`; starting master `f4dee4a29c2e208b36db4a4161a4723c735cd775`.

Default checked unsigned powers preserve `Panic(0x11)` bytes in supported self-call, nested, conditional and index paths. No new panic code or explicit `revertStrings` setting is admitted. Full coverage-plan step 4 remains partial.

## Current validation

- Kernel: 40 completed execution certificates (34 returns, six precise assertion panics), both pipelines; only `propext`, `Classical.choice`, `Quot.sound`. Exhaustion cannot establish a return.
- Compiler/EVM: 82 exact-byte observations, both pipelines. Per pipeline: own fixture 29, original panic fixture eight, original debug fixture four. Debug evidence is compiler/EVM only.
- Library continuation: original `Decision` passed in 1043 seconds (309 jobs, 5,631,021,056-byte peak). The remaining explicit targets plus `Solidity` passed in 207 seconds (676 jobs, 1,099,825,152-byte peak). All 686 default jobs then passed `--rehash --no-build` freshness verification.
- TestSuite and frozen sorts retain their independent passes at `093819c1`: 259 jobs; 377 taclets, all 131 read-bearing annotations matched. They were not rerun.
- Static/integrity checks passed again. Independent finder/skeptic review details are recorded in the reports. No Lean source, theorem statement, premise, guard, expectation, heartbeat/fuel/search/time limit or supported/refused setting changed in this continuation.

## Concrete timeout diagnosis

Six library jobs were unfinished: `Decision`, its direct dependents `DecisionKInt`, `DecisionMemory`, `DecisionArrays`, the stale `Solidity` root and the library default facet. All 309 Decision dependency jobs were already current. A cache-only refusal identified this boundary without compiling.

Profiling exposed compiled verdict batches at Decision lines 780 (186 seconds), 910 (149 seconds) and 810 (88.5 seconds), plus kernel coverage checks. Timing messages polluted 35 guarded-message checks, so that 994-second diagnostic exited 1 and is retained as failed evidence. Removing only the profiler flag allowed the original unchanged target to pass. Existing sequential elaboration and certified replay speed choices were preserved; no general closer or sharing repair was needed.

Every command retained the 1800-second bound, hard 12 GiB cgroup cap, zero swap, one CPU and serial Lean `-j1`. The measured outer VM cgroup is 16 GiB, leaving a 4 GiB margin. These are warm-cache, per-target results; they do not claim a cold build fits one time window. All five earlier whole-script timeouts remain nonpassing. `run-lean.sh` was not blindly retried.

## Evidence and remaining scope

`library-continuation.json` contains current gate commands, hashes, measured costs, artifacts, headroom and reviews. `independent-gates.json` and `validation.json` are unchanged historical checkpoints with all hashes retained. The preceding handoff is preserved verbatim as `handoff-093819c1.md.txt`. The feature document now appends this milestone; its prior bytes and original hash are retained in `calls-exceptions-093819c1.md.txt`. All original logs, observations and blocked attempts remain in place.

Signed magnitude-overflow payload precision, allocation panic `0x41`, and explicit default/strip/debug/verbose-debug `revertStrings` settings remain gaps. Explicit checking modes and environment/log/layout/delegate policies are unchanged; malformed-storage `0x22` remains excluded. Original upstream Lean replays remain blocked by their host adapter and debug-setting refusals; EVM observations are separate evidence. The prior documentation audit retains 20 missing references and six ambiguous names in unchanged files.
