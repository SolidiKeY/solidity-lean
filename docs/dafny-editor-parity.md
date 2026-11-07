# Dafny VS Code comparison harness

This audit compares the official Dafny extension with `vscode/`, the Solidity
Lean verification extension. Full parity is not established. The
[tracked inventory digest](dafny-editor-features.json) binds the external full inventory:93 discovered capabilities and391 mechanical obligations,
including explicit missing and unexamined work. Readers verify its SHA256 and fail
with restoration instructions when the full payload is missing. This inventory is separate from
the [language and verification inventory](dafny-parity.md).

## Architecture and placement

Repository discovery covered the module map, extension and backend sources,
source verification runner, Node tests, editor-host tests, compiler/solver
boundaries, build measurement scripts, and both CI workflows. The core Lean
package remains dependency-free. The harness belongs in `vscode/parity/`, beside
the existing real editor launcher and injectable controller tests. Its offline
regressions run through `vscode/test/*.test.cjs`; the existing CI editor inventory
step also validates the new inventory. Live runs require separately provisioned
VS Code, Dafny, .NET, solc, and Lean. No new production dependency is needed.
The optional harness requires Node 22 or later for its built-in WebSocket client;
the production extension's Node requirement is unchanged.

The production local extension now starts `vscode/src/lsp-server.cjs` and
synchronizes versioned in-memory Solidity buffers over standard LSP stdio.
A separate compiler worker retains the pinned solc WASM module. A bounded pool
of 1–4 proof workers can use the compact generated-C/WASM verifier for admitted
fragments. General frontend checks retain a Lean language server and generated
document, reusing imported modules on edits. Workers parallelize exact function
selections and files; assertions within one function remain serial. Default IDE
checks return direct verifier decisions without per-result certificates. Explicit
`certify: true` requests use the `solc_import`/`#solkey_test` pipeline with
kernel-checked certificates.
It retains source hashes, compiler pins, import-gap diagnostics and counterexample
validation. Dependency changes invalidate live sessions and checked reports.

The server provides completion, definitions, references, symbols, signatures,
highlights, guarded rename, versioned diagnostics and verification notifications.
The extension adds syntax, gutters, status and Testing integration. Completion
uses a broad lexical fallback for incomplete code; complex receiver inference, full specification refactoring and assertion-level
parallel scheduling remain open. Formatting, quick fixes, workspace symbols,
project imports and cross-file rename are implemented. See [the implementation record](feature-work/solidity-lsp.md).

Dafny uses `vscode-languageclient`, its language server, Boogie verification
tasks, and Z3. The pinned server serializes VC translation through
`DafnyProgramVerifier`'s mutex. `ProjectManagerDatabase` constructs a shared
scheduler bounded by `VcsCores`; `ProjectManager` orders work by explicit priority,
recent edits, then source order. `Compilation` starts Boogie tasks without
waiting for each task to finish and publishes their states. Async scheduling
alone does not establish parallel solver execution. Runtime traces and sampled
CPU activity are needed to assess that separately.

The project manager owns its Boogie engine. The pinned Boogie 3.5.5
[engine constructor](https://github.com/boogie-org/boogie/blob/d90c6c9ef7e0e244cef55ddd0557e28a1a1301d8/Source/ExecutionEngine/ExecutionEngine.cs#L55)
creates a checker pool and a per-instance `VcsCores` semaphore. Requested cores
are therefore not a global server-wide solver cap. The recorded suite includes
multiple projects, cancellation and restart: its maximum CPU-active solver counts
must not be interpreted as the initial file's configured parallel width.

## Reproduce

Build the current local API before measuring. Follow the repository toolchain,
compiler and [resource instructions](refactoring-progress.md#resource-bounds-and-resuming-work).

```sh
LEAN_NUM_THREADS=1 lake build Solidity.Frontend.Testing
node --test vscode/test/*.test.cjs scripts/source-locations.test.mjs
node vscode/parity/discover.cjs --check
```

Provision the reference source at these immutable revisions:

| Component | Revision |
|---|---|
| Official extension, version 3.5.4 | `1a329b121ef66f2c8be8ca2c28eda437040042eb` |
| Dafny server and 4.11.0 executable | `fcb2042d6d043a2634f0854338c08feeaaaf4ae2` |

Run `npm ci` and `npm run compile` in the reference extension checkout. Dafny's
custom installation still checks for a working .NET executable even when using
a self-contained Dafny binary. The live launcher uses the same VS Code binary,
hardware, client deadlines, and paired sources for both targets:

```sh
node vscode/parity/run.cjs \
  --code /absolute/path/to/code \
  --dafny /absolute/path/to/dafny \
  --dafny-extension /absolute/path/to/ide-vscode \
  --dotnet /absolute/path/to/dotnet \
  --workers 1,2,4 --cache none,basic \
  --warmups 1 --trials 5 --obligations 8 \
  --output /absolute/path/to/new-results
```

Linux needs a running X server; set `DISPLAY` or launch using `xvfb-run -a`.
Use a new output directory for each run. The launcher serializes harness
instances through a global temporary lock, selects isolated editor profiles and
extension directories, and checks a unique launch identity in each host report.
If a host crashes without evidence, its exit code cannot substitute for a pass.
The parent stops its own process tree on interruption or timeout and samples a
4 GiB RSS ceiling plus a 12 GiB available-memory reserve. These sampling guards
supplement, and do not replace, the required systemd memory scope for heavy builds.

For repeated timing runs after a full functional pass, `--suite benchmark`
retains startup, hover/provider probes, incremental verification, concurrent-file
verification, renderer input, cancellation and restart measurements while
omitting repeated correctness/counterexample/save regressions. Keep full and
benchmark datasets separate. Target order alternates between repetitions.
The CI runner selects a smaller available-memory reserve explicitly for its
host; `--memory-reserve-mib` and `--memory-max-mib` record those choices.

Local worker settings are applied to concurrent functions/files (maximum four).
The local exact-snapshot proof cache is always enabled; Dafny cache-policy names
do not select equivalent local policies. Scaling uses the within-file declaration/function metric; cross-file measurements
are retained separately. These scopes must
remain distinct. Use `--targets local` or `--targets dafny` for isolated debugging.
`--trace off` disables raw protocol recording for an observer-overhead control.

## Scenarios and observations

The shared workload contains constant-return functions with matching true or
false postconditions. It stays within the unsigned range and avoids integer
overflow, recursion, and termination-policy differences. Obligations pair by
function ordinal; source ranges and diagnostic messages remain native to each
language. Incremental verification adds a declaration. Rapid edits replace a
false specification with true specifications and an additional declaration.
The additional symbol gives a completion barrier: Dafny can suppress identical
symbol-status arrays across document versions. Waiting for a new terminal
notification after a comment-only edit would be an invalid protocol assumption.

The host exercises initial and incremental verification, false postconditions,
rapid edits, real Testing API profiles, hover, discovery probes for completion
and navigation, counterexamples, concurrent files and requests, cancellation,
configuration/save behavior, and server restart. All target verification uses
the real backend. Instrumentation observes the target extension's real VS Code
objects; unrelated built-in extension registrations are excluded.

Empty completion/navigation/signature responses at a declaration are discovery
observations, not capability passes. A dedicated local call-site scenario checks
actual completion, definition, references, signatures and rename through VS Code;
raw real-LSP tests additionally check current versions, qualified references and
invalid identifiers. Cross-language semantic equivalence remains unexamined.
Counterexample checks require positioned Dafny evidence or a certified local model
prestate, but do not establish witness equivalence. Editor cancellation records
acknowledgement latency; real LSP tests also check old Lean process quiescence.
Both targets exercise actual server restart.

Production verification now reads the exact open buffer without saving it.
The save/edit regression checks that the superseded request is discarded, the
latest buffer verifies and the saved Solidity source remains unchanged. Legacy
CLI-controller tests retain their explicit fixture injection and saved-file checks.

The independent source audit also found project ownership/includes and solver
options; parse/resolution/verification diagnostic distinctions; expanded related
errors and quick fixes; language editing configuration; assertion-batch costs;
Testing API exclusions and state transitions; cache migration, fairness,
contention and assertion splitting; plugins; and installer/version failures.
Their inventory entries remain missing, partial, or unexamined until targeted
runtime evidence exists. Source or test-file presence is not local test success.

## Results and methodology

Each live output contains:

| Artifact | Evidence |
|---|---|
| `report.json`, `summary.md` | Per-trial outcomes, median/p95/spread, timeouts, resource summaries, differential observations and worker scaling |
| Trial `result.json`, `events.jsonl` | Scenario assertions, real editor diagnostics, test states, hover contents, commands and extension-host delays |
| Trial `lsp.jsonl` | Byte-framed official client/server JSON-RPC traffic; method names, versions, errors and message ordering are retained |
| Trial `resources.json` | Sampled descendant process RSS, CPU ticks and verifier activity overlap |
| Trial `dom.json`, `accessibility.json`, `visible-state.json` | Actual renderer DOM, accessibility tree and visible UI text |
| Trial `screenshot.png` | End-of-run visual evidence for failed launches and the first reference/candidate pair; it does not depict each earlier failing phase |
| Trial `editor.log`, `config.json` | Startup failures and effective harness inputs |

Raw protocol normalization replaces only explicit workspace roots. It retains
diagnostic severity, ranges, text, versions, ordering and statuses. Cross-language
API observations are compared separately; verification reports are never fabricated into
LSP transcripts. Meaningful mismatches remain visible even when expected.

Targets run sequentially, with warmups excluded from summary statistics.
Fresh processes and profiles measure process-cold startup while retaining OS
caches. Incremental trials reuse the live server. No cold-page-cache claim is
made. Reported p95 uses nearest rank; small samples are descriptive, and repeated
trials plus variability must support any regression conclusion. The same number
of declarations and client deadlines do not equate Z3 resource limits with Lean
heartbeats or establish general proof-workload equivalence.

CPU overlap counts distinct verifier processes accumulating ticks in a sample
interval; it is not a count of `async` methods or sleeping children. Native queued
and running status intervals include transport and notification throttling. Pure
frontend, VC-generation, solver, and UI-notification times are not isolated.
Within-file declaration scaling differs from parallel assertion splitting inside
a single declaration; the latter remains unexamined.

`vscode/parity/analyze.cjs --output tests/editor-parity/baseline.json REPORT.json ...`
consolidates completed datasets without combining full and benchmark samples.
It separately derives Z3 and Lean CPU activity from retained process samples;
the server/frontend process is not counted as an additional solver.

RSS sums can double-count shared pages and sampling can miss short-lived
children. The Dafny recorder adds synchronous disk writes in the extension host. The
extension-host heartbeat measures that process's responsiveness; DOM snapshots
alone do not measure renderer input latency. Complex proofs, large projects,
fairness under resource contention, cache eviction, comprehensive restart/error
recovery and visual theme parity remain open. No unsupported, skipped or
untested capability is classified complete.

## Review record

The read-only finder review reproduced stale success acceptance with a fake
editor, identified timeout undercounting and interruption cleanup gaps, and
found missing/empty observations counted as passes. The harness now checks
per-launch identities, preserves scenario timeouts, forwards interruption, and
records missing/partial/unexamined statuses separately. The read-only skeptic
review rediscovered upstream features before reading the first inventory,
adding the missing runtime command and the explicit families described above.
Neither review used the Lean server or established extra runtime passes.

## Harness integrity and stdio comparison (2026-11-03)

Repository discovery located the existing CommonJS extension, stdio LSP, solc
analysis worker, bounded proof-worker pool, persistent Lean sessions, optional
generated-C/WASM verifier, Node tests, Electron launcher and CI. Additions reuse
`vscode/parity/`, `vscode/test/`, this guide and `tests/editor-parity/`, with no
package dependency or core Lean import.

Read-only finder and skeptic reviews reproduced false-pass and measurement
defects. Both independently reviewed the final changes without Lean. Repairs:

- Every proof scenario requires expected outcomes and the exact local `f0`
  through `fN` obligation set. Terminal errors and unknowns cannot count as
  proofs; unknowns cannot count as demonstrated refutations.
- Failed launches remain in failure/resource/timeout reports but cannot
  contribute latency samples or scaling. Host reports require consistent
  identities, unique scenario IDs, checks and aggregate status.
- Byte-frame finalization distinguishes empty, incomplete and corrupt protocol
  recordings. None can certify observed compatibility.
- Paired call-site checks assert actual definition/reference ranges, rename
  replacement text/ranges, minimal-edit member completion and meaningful hover.
  Signature help at the opening parenthesis and second argument are separate.
- Editor service edits run after proof measurements. Stdio disables automatic
  Dafny verification and explicitly schedules native verification symbols, so
  service edits cannot leave competing proof jobs in measured phases.
- Stdio requires graceful shutdown and exit zero, checks process ownership,
  bounds version probes and records configurable resource guards. CI explicitly
  selects its smaller available-memory reserve.

The skeptic rediscovered five additional families: proof code actions and lazy
resolution; symbol/lookup/diagnostic migration; solver retention; standard-library
and refinement navigation; and hover before verification finishes. Their added
inventory entries remain unexamined. The independent
[test ledger](dafny-editor-audit.json) enumerates 99 tracked upstream test files
and 609 registration sites before reconciling paths with the feature inventory.
Registrations include TypeScript suites and unexpanded parameterized tests.
Every unported registration remains **unexamined**. Offline and immutable-source
CI gates check the ledger; its size is not a count of passing tests.

For machines without Electron or an X display:

```sh
LEAN_NUM_THREADS=1 node vscode/parity/stdio.cjs \
  --dafny /absolute/path/to/dafny --scope services \
  --workers 1,2,4 --trials 5 --warmups 1 \
  --output /absolute/path/to/new-stdio-results
```

Services scope exercises real initialization, document/workspace symbols,
definitions, references, hover, completion, signature help, rename, formatting
invocation, concurrent requests, rapid edits and server lifecycle. It does not
run the local verifier. Full scope additionally requires a freshly built backend
and exercises true/false postconditions, incremental verification, current-version
stale-diagnostic checks and concurrent files. Configure `SOLKEY_ROOT` and Lean
as for the editor harness. Both transports use the same global run lock.
`--memory-max-mib` defaults to 4096 and `--memory-reserve-mib` to 12288;
build resource requirements apply separately.

Outputs retain `report.json`, `summary.md`, native JSON-RPC responses/traces,
events, process samples, phase windows, configuration and server logs. Phases
with too few CPU samples remain unexamined. CPU deltas within a sample window
do not prove simultaneous instructions. Stdio startup measures launch through
initialization; full proof timings include explicit symbol discovery/scheduling.
These are separate from editor activation and automatic verification metrics.

The [fresh measured record](../tests/editor-parity/stdio-baseline.md) and
[JSON results](../tests/editor-parity/stdio-baseline.json) preserve observations
and limits. The reduced [Dafny](../tests/editor-parity/services.dfy) and
[Solidity](../tests/editor-parity/services.sol) fixtures are shared by both
transports. Dafny retains member completion after a minimal insertion but loses
it after full replacement with incomplete code; the local server handles both.
Dafny returns opening-parenthesis signature help but no second-argument result
in this fixture. These remain explicit partial statuses and native differences.

The official VS Code download returned HTTP 403 under this environment's
network policy. Changed editor/DOM scenarios were reviewed but have not run
here. This environment also lacks the systemd user scope required by repository
instructions for heavy builds, so no fresh local backend build or local proof
performance comparison is claimed. Fresh paired service runs use real solc;
reference-only proof runs use real Dafny/Z3. Earlier editor/proof baselines
remain historical evidence.

Manual `editor-parity` CI offers `editor` and `stdio` transports and builds the
current local backend before full comparisons. Stdio has no VS Code API, DOM,
accessibility or renderer measurements, and lacks cancellation, restart,
counterexample and settings-transition scenarios. Long-running proofs, large
projects, resource contention, assertion-level scaling, equivalent solver limits,
isolated solver/VC timings and cold-page-cache behavior remain open. Formatter
response shape does not establish correct applied edits. No full parity claim
is made by either transport.

## Historical CLI baseline

The [baseline report](../tests/editor-parity/baseline.md) and
[JSON evidence](../tests/editor-parity/baseline.json) retain 46 valid editor
launches: 35 measured trials and 11 warmups, with no broken launch in those
datasets. Eight earlier cache-batch attempts are retained separately; six could
not start because the editor IPC path exceeded the Unix socket limit. The
launcher now keeps editor state under a short temporary root. Both cache policies
were rerun with that setup; the earlier successful worker-scaling dataset remains
separate. No owned editor/verifier processes survived trial cleanup.

The runs used VS Code 1.108.0, Dafny 4.11.0, Lean 4.24.0, a four-core CPU quota,
a 16 GiB memory limit, and one Lean thread. With four constant-return functions,
the one-worker scaling dataset's median initial feedback was 1.13 s for Dafny
and 5.87 s locally; incremental feedback was 0.246 s and 6.55 s. The roughly 26×
incremental gap persisted across repetitions. The local path recompiles source
and launches Lean for each request, whereas Dafny retains a language-server
pipeline. These are end-to-end editor results, not pure solver-speed ratios.

This small workload did not establish representative solver scaling or a
significant cache-policy improvement. The trace-disabled control had similar
initial timing; no observer-overhead correction was applied. The full suite
retains the native diagnostic difference: Dafny errors on an unproved false
postcondition, while local open goals are warnings until certified model evidence
is requested. These measurements describe the former CLI implementation, before the persistent
LSP. See the implementation record for current measurements and remaining gaps.

Validation passed 71 Node tests, the 88-entry source inventory and immutable-source
reconciliation, the existing 36-family language audit, workflow YAML parsing,
new Markdown links and diff whitespace checks. The current Lean API built all
263 required targets. The reduced paired fixture produced one verified function
and one expected failure in Dafny, and one proof plus one kernel-certified
refutation with local counterexample search enabled.

## Version 0.4 persistent LSP validation

The [LSP baseline](../tests/editor-parity/lsp-baseline.md) and
[validation record](../tests/editor-parity/lsp-validation.json) cover the current
implementation after integration with master. All 18 editor launches passed
without broken scenarios; gaps remain classified separately. One-worker local
median changed-buffer verification was 5.17 s versus Dafny's 247 ms; unchanged
local cache hits took 100 ms. These are different operations. The
[implementation record](feature-work/solidity-lsp.md#measured-editor-results)
explains warm-session evidence, cross-file scaling and remaining proof costs.

## Version 0.5 compiler/project validation

The [project/compiler report](../tests/editor-parity/compiler-project-baseline.md)
records 20 successful launches and current function scheduling. Local incremental
medians were 5.07 s with one worker and 3.51 s with two; initial latency remained
about 6.4 s. This workload still trails Dafny. See the
[implementation record](feature-work/compiler-project-services.md) for exact
compiler scope, semantic refusals, editor services and validation evidence.


## Handoffs

### solidity-dafny-20261105 / dafny-parity — inventory and gate foundation

**Blocked; full parity is not established.** The first required gate run exited
1 with 270 rows and zero passing rows. Existing assessments were preserved;
93 original features remain, with 177 append-only mechanical obligations under
`mechanical.rows` in the same inventory. These are 42 contribution entries
(including setting defaults), 62 TypeScript API call sites, 18 live capability
leaves, three observed `dafny/*` methods, five automatic lifecycle obligations,
35 visual obligations and 12 adversarial/performance/benchmark obligations.
The visual grid is an obligation list; discovery of actual screenshot
differences still requires paired phase captures and additional rows.

The new [mechanical scanner](../vscode/parity/mechanical.cjs) uses the pinned
reference extension's TypeScript parser. It includes source tests and records
individual locations, expressions and source hashes. The existing broad
source/test discovery remains unchanged. [Inventory refresh](../vscode/parity/inventory-refresh.cjs)
only appends rows; it never replaces assessments or deletes retired hits.
[Inventory check](../vscode/parity/inventory-check.cjs) checks clean immutable
source pins, reruns AST/manifest discovery, parses the retained live trace and
can also check a fresh trace with `--live-trace FILE`. Existing editor-parity CI
now records and checks a fresh lifecycle trace before editor provisioning.

The [reference lifecycle collector](../vscode/parity/lifecycle-trace.cjs) drove
real Dafny 4.11.0/Z3 without explicit verification requests: open and edit proved,
a changed return value produced a verifier error, and the repaired buffer proved
before save and close. Successful phases require every symbol correct; a
verified marker cannot mask a failing proof. The validator correlates document
URI/version, terminal feedback, broken-proof diagnostics, initialization,
shutdown acknowledgement and both framing finalizers. Dynamic registrations
are inventoried when present. [Raw traffic](../tests/editor-parity/lifecycle/dafny-lsp.jsonl)
and [phase observations](../tests/editor-parity/lifecycle/phases.json) establish
reference discovery only, with one worker and enabled ghost/gutter notifications.
They do not establish candidate or editor parity or a performance comparison.

The [parity gate](../vscode/parity/parity-gate.cjs) freezes its first row IDs at
`/workspace/dafny-parity-state/first-run-rows.json`, outside this checkout.
Preserve that file across continuations; do not recreate it to remove rows.
The [machine report](../tests/editor-parity/parity-gate-report.json) rejects
incomplete rows before model calls. Complete rows need existing repo-relative
evidence, a matching `assessment.testedSourceState`, and two independent
`codex exec --ephemeral -s read-only` judgments using the strict
[judge schema](../vscode/parity/judge-schema.json). The report exposes the source
fingerprint to which new runtime evidence must be bound. The first question asks
whether ours reproduces the row; the second assumes it is unfinished and searches
for a missing aspect. Both must say yes. Prompts require opening files/images,
treat prose as claims, and reject any missing aspect. Cache inputs include row,
prompt, schema, evidence bytes, upstream/trace hashes and candidate source state.
No row is complete here, so no per-row model call or cached yes is claimed.

Reproduction after provisioning the pinned sources and their dependencies:

```sh
node vscode/parity/inventory-check.cjs
node vscode/parity/parity-gate.cjs
# Equivalent named commands:
npm --prefix vscode run inventory-check
npm --prefix vscode run parity-gate
```

Independent read-only finder and skeptic reviews identified weak initial trace
acceptance, omitted dynamic registrations, stale judgment caches, missing fatal
reports, malformed versions/external-state symlinks, and mixed success/error
feedback. Confirmed findings were repaired and adversarial tests added at
[parity-gate.test.cjs](../vscode/test/parity-gate.test.cjs). Neither review used
Lean. Source discovery, immutable-source reconciliation and offline regressions
pass (120 passed, two runtime-dependent tests skipped, zero failures); detailed
commands and logs are retained under
`/workspace/dafny-parity-artifacts/`. The required parity gate remains failed.
No Lean source, generated library root, theorem, premise or production editor
feature was changed. These JavaScript tests and reference Z3 observations are
external-test evidence, not Lean proofs or kernel certificates.

**Blocking environment evidence.** VS Code 1.108.0 provisioning via
`@vscode/test-electron@2.5.2` failed resolving `update.code.visualstudio.com`.
A retry through the configured HTTP proxy returned HTTP 403. Current enforced
network policy does not list that host. No alternate download route was used.
The VM also lacks Lean/Lake on PATH and a usable systemd user scope; the probe
reported missing `DBUS_SESSION_BUS_ADDRESS` and `XDG_RUNTIME_DIR`. Heavy Lean
builds, fresh proof benchmarks, KeySort and `RUNTIME_GATE_PASS` are not claimed.
The repository pin is Lean 4.24.0; an installed Lean/Lake version is unavailable.
Observed tools are Node 24.19.0 and codex-cli 0.163.0. All work remains local on
`codex/solidity-dafny-20261105/dafny-parity`, based on verified published commit
`9584f9e7df09f638d9e0cb8930501d1660aa4b2f`; nothing was pushed.

**Outstanding work:** provision the official editor and Xvfb/runtime prerequisites,
capture both extensions at all five phases, inventory every actual difference,
implement/reproduce every row, bind fresh evidence to candidate source state,
execute both independent judgments for each complete row, run the full adversarial
and cold/warm/median/p95/worker-scaling benchmark matrix, restore the required Lean
build environment and run repository final gates. Re-run the unweakened parity
gate until it exits zero. The saved checkpoint does not complete the assignment.

**Q-VIS-01 [assignment:1e; environment:download]:** How should the official
VS Code 1.108.0 executable be provisioned after the observed HTTP 403?
Options: enable the official update/download hosts in this environment's managed
network policy, allowing the pinned download to be retried; or provision a
verified official VS Code 1.108.0 Linux x64 archive on the VM, allowing the same
headless captures without a policy change. Neither option waives visual parity.


### Audit c0ef3ec7 — controller, lifecycle harness and recoverable tooling

The original goal remains blocked and untouched; no goal creation, reset,
reactivation, completion or integration action occurred. The available tool
catalog exposes no `get_goal` operation. Checkpoint `13c85fe54a38eb92c768bf6c1b2bc4c4f9c69f87`,
the pinned base, assigned branch, all 270 row IDs and the external first-run
freeze are preserved. Its SHA256 remains
`d2f7e40e0c4cd370d09f9feb04872ea81963524b48be8e46c9b98dba26f945f1`.

**Controller implementation checkpoint.** Pinned Dafny manifest/source inspection
confirmed enabled gutter/test visibility defaults, per-document compilation
messages and status actions. The existing local controller now ignores obsolete
or closed-document status notifications, redraws visible gutters on configuration
changes, and contributes `solidityLean.displayVerificationAsTests` with default
`true`. Disabling tests hides only that resource's test items; reports and
verification remain available, and re-enabling reconstructs current items without
backend work. UI-only changes no longer restart servers. The automatic-verification
fallback now agrees with the already-contributed `onchange` default; no backend
verification semantics or run profile was changed.

The local status bar opens an action menu for restart/output. This remains partial:
Dafny's help/report actions and exact rendered status messages are not reproduced.
Restart generations prevent obsolete reopen operations and late errors after
disposal. Crashes clear only the failed client's owned documents and abort stale
publication; stale/cancelled save errors cannot erase healthy state. Failed clients
remain owned until asynchronous cleanup finishes, and deactivation awaits retirement.
These paths are covered by 12 injected-editor/isolated-RPC regressions in
[editor-state.test.cjs](../vscode/test/editor-state.test.cjs) and the
[recorded TAP output](../tests/editor-parity/recovery-c0ef3ec7/controller-regressions.tap).
The isolated protocol fixture is not a Dafny server or verification proof.

**Independent harness checkpoint.** The existing editor launcher accepts
`--suite visual`, separately from full/benchmark timing runs. It uses the existing
declared on-change verification configuration and makes no explicit proof requests.
It requests real overview screenshots at open, first feedback, verified, broken
and fixed, plus actual `editor.action.showHover` subcaptures at final phases.
Each capture is bound to a fresh launch/request identity, stable source and native
state before/after capture. A missed early phase is explicitly missing; a terminal
error or cancellation cannot be relabeled verified. Hover-provider responses alone
are never evidence of a rendered hover. The renderer records visible hover count,
DOM/accessibility state and PNG bytes. Seven coordination/phase regressions pass.
No real editor run or screenshot is claimed while Q-VIS-01 remains unanswered.
Visual rows remain unexamined and actual visible-difference discovery remains due.

The existing stdio harness now exercises rapid symbol updates, close/reopen identity,
concurrent file isolation and cancellation/follow-up service responses. Assertions
inspect recursive symbol names, rejecting metadata decoys. Cancellation is explicitly
partial: it measures client acknowledgement, not worker quiescence. The
[reviewed service matrix](../tests/editor-parity/recovery-c0ef3ec7/services-reviewed.json)
retains 36 successful launches with gaps: five measured trials and one warmup for
each target at configured widths 1, 2 and 4. Automatic proof verification was disabled;
there were no Lean proof/build requests. The
[compressed raw archive](../tests/editor-parity/recovery-c0ef3ec7/services-reviewed.tar.gz)
retains native traces, responses, lifecycle exits and resource samples. Its source
hash manifest identifies the producer files; report Git HEAD predates the uncommitted
slice, so it is not presented as the tested source identity. The earlier dataset
with weaker assertions remains preserved separately and is not pooled.

For example, at width one, process-cold initialization median/p95 was 1599/3361 ms
for Dafny and 227/495 ms locally. The eight-hover request batch was 43/63 ms and
146/246 ms respectively. These descriptive five-sample service measurements retain
OS caches and differ from proof feedback latency. They establish neither equivalent
solver policies nor proof-worker scaling; `parallelProofScaling` remains empty.

Read-only finder/skeptic reviews found and repaired the controller and evidence
issues listed in the [review record](../tests/editor-parity/recovery-c0ef3ec7/reviews.md).
Full offline validation passed 140 Node tests, with two runtime-dependent tests
skipped and zero failures; inventories/source pins also pass. Rows with source or
service evidence are honestly partial. No row is complete or independently judged;
the original parity/judge contracts are unchanged and parity-gate must still fail.

**Tool recovery and remaining block.** Official Lean 4.24.0 (commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`) and Lake 5.0.0-src+797c613 were
extracted under `.cache/toolchains/lean-4.24.0-linux/bin`. Signed Debian metadata
and task-owned download/extraction provisioned Xvfb 21.1.16 without installing
system packages; its actual X11 setup handshake succeeded. Official .NET SDK
8.0.427 was installed under `.cache/toolchains/dotnet8`. The pinned solc 0.8.34
asset was provisioned under `.cache/parity-solkey`; reference Dafny remains 4.11.0.
No global PATH was changed, VS Code download retried or network policy bypassed.
The .NET installer encountered denied optional `ci.dot.net` metadata before using
its permitted official builds feed successfully.

The [resource probes](../tests/editor-parity/recovery-c0ef3ec7/provisioning.json)
show PID 1 is `tail`, both user/system systemd scope probes fail, and cgroup2 is
read-only. Inherited `memory.max` is 16 GiB and `memory.swap.max` is unlimited;
this does not enforce the required 12 GiB/no-swap scope. No heavy Lean build,
full/TestSuite/strict/trust gate sequence, KeySort runtime output, kernel certificate
or `RUNTIME_GATE_PASS` is claimed. An operator must provide a functioning manager
and delegated scope on this VM before heavy proof gates. Q-VIS-01 remains pending;
no visual waiver or semantic/profile choice is requested or assumed.

Whole-scope outstanding work remains: actual paired phase/hover screenshots and
all visible-difference rows; every remaining contribution/API/protocol/lifecycle
implementation; complete adversarial and proof performance/cold/warm/scaling
matrices; fresh source-bound evidence and both independent judgments for every
complete row; repository final proof gates under compliant limits; parity-gate exit0.
The recovered tools and these implementation checkpoints do not complete the goal.


### Audit 5bad5756 — diagnostic locations, hover scheduling and Testing requests

This recovery preserves checkpoints `13c85fe54a38eb92c768bf6c1b2bc4c4f9c69f87`
and `f71d00a48fe04880706a8fe0c61319807b043b4e`, the original base and assigned
branch. The goal remains blocked and untouched. The available catalog exposes
only a goal-stop operation, not `get_goal`; no goal mutation was attempted.
Q-VIS-01 and Q-RES-01 remain unanswered; no unchanged download/scope probes were
repeated, no heavy Lean job ran, and no push/merge/PR occurred.

All 270 original row IDs and the external first-run file are preserved. Twenty-three
new scenario obligations were appended, bringing the inventory to **293 rows**,
all incomplete. The inventory checker now also requires those separate scenarios.
The original gate, judge prompts/schema, evidence requirements and frozen pins
were not weakened. The four requested families moved from unexamined to partial.

**Diagnostics and document versions.** Inspection covered pinned Dafny
`relatedErrorView.ts`, `Migrator.cs`, `IdeState.cs`, `DiagnosticMigrationTest.cs`,
`SymbolMigrationTest.cs`, `LookupMigrationTest.cs` and `HoverTest.cs`, plus the
existing local server, client, controller and tests. Local compiler diagnostics
now retain solc secondary source locations and their own file text/URI/ranges,
including UTF-8 to UTF-16 conversion. Foreign primary errors remain anchored at
zero in the owning editor with their actual locations in related information;
unknown foreign offsets are not projected onto the main file. The existing
controller already converted standard related information; its stale/closed
batch behavior now has targeted regression evidence.

Incremental client synchronization sends a minimal text edit without splitting
CRLF or surrogate boundaries. The server relocates surviving verification
**display diagnostics**, marks them `Outdated: ` and demotes errors to warnings.
Deleted/edge-crossing or invalid old display ranges are removed; valid edits cannot
be blocked by an invalid old location, while invalid new edits still fail; full-buffer replacement clears them.
Same-document related ranges move, foreign ranges retain their own coordinates.
Fresh results replace the corresponding display entries. Standard diagnostic
`data` records local function ownership so selected verification cannot erase an
unverified sibling's outdated diagnostic. Reports/cache entries are not migrated
or treated as current proofs. Dependency-content invalidation, backend reset and
close/reopen discard old display state; confirmed review regressions have tests.
Symbol-table/lookup migration and the exact custom Dafny postcondition wavy
underline remain unimplemented. Native related information is not that decoration.

**Hover before verification.** The existing server already served declaration
information after analysis without awaiting verification. A deliberately pending
injected verifier now verifies that scheduling property. Cancelled requests detach
promptly from shared analysis without aborting a sibling request; closed/reopened,
retired/reassigned-client and configuration-obsolete replies cannot return a stale
hover. This is injected backend/controller evidence, not a pending real Lean run
or a rendered hover comparison.

**Testing exclusions and transitions.** The existing Verify profile and result
classification remain unchanged. Selections now queue stable leaves once, even
with overlapping file/leaf includes; file exclusions also cover directly included
leaves. Native TestRun cancellation and profile cancellation share the current
request token. Command cancellation/disposal stop queued siblings as well as
active work. Current item/source/URI checks prevent stale selections or a wrong
opened file with identical contents from receiving a pass. Cancellation/stale
responses are skipped, compiler failures are errored, and runs end once. Tests
cover edits, visibility toggles, multi-file selection and overlapping runs.
Conflicting include/exclude cases use conservative ancestor exclusion; complete
pinned Dafny edge-case equivalence and automatic native Testing state behavior
remain due. No alternative proof profile or verification semantics was selected.

**Native observations and failures.** The existing stdio harness now has real
service-only cases for same-file duplicate locations, foreign override locations,
fixes and imported duplicate errors following watched-file invalidation. The
[local record](../tests/editor-parity/recovery-5bad5756/local-services.json) and
[raw archive](../tests/editor-parity/recovery-5bad5756/local-services.tar.gz)
retain exact primary/secondary ranges, messages and versions. Automatic proof
verification was disabled; one functional trial is not a performance benchmark.

The opt-in reference collector `--migration` requires a separate output directory.
The exact pinned `ResolutionDiagnosticsContainPreviousVerificationResultsWhenCodeIsInsertedBefore`
fixture passed live: primary `0:44–45` and related `0:36–41` became `5:44–45`
and `5:36–41`, with warning severity and `Outdated: ` prefix; full replacement
cleared them. [The reference record](../tests/editor-parity/recovery-5bad5756/reference/migration.json)
and [raw traffic](../tests/editor-parity/recovery-5bad5756/reference/dafny-lsp.jsonl)
retain the observation. Full ranges/columns/messages are asserted, stale passed
markers are removed at startup, and a passed record is written only after shutdown
and exit zero. The existing one-core/20-second reference verification budget is
unchanged. This is Dafny/Z3 evidence, not a local kernel certificate or editor run.

An earlier comment-only probe did **not** emit `Outdated: `: the pinned runtime
cleared and reissued the error. Its expectation failed with exit 1 and remains
recorded as a real difference from the local conservative display migration.
A malformed imported-declaration fixture also timed out before correction, and
a stale-output test fixture initially failed due to escaped newlines. The
[attempt ledger](../tests/editor-parity/recovery-5bad5756/attempts.json) retains
all failures and corrections; assertions, expected codes/ranges and timeouts
were not relaxed to obtain successful reruns.

**Validation and review.** Final regressions passed **166 Node tests**, with two
runtime-dependent tests skipped and zero failures. Focused recorded output covers
[diagnostics](../tests/editor-parity/recovery-5bad5756/diagnostic-state.tap),
[Testing](../tests/editor-parity/recovery-5bad5756/testing-state.tap) and
[editor lifetime](../tests/editor-parity/recovery-5bad5756/editor-state.tap).
Fresh live inventory, immutable source reconciliation and test ledger checks pass.
The [source hash manifest](../tests/editor-parity/recovery-5bad5756/source-sha256.json)
binds the prospective committed source; post-commit exact-head logs are retained
in `/workspace/dafny-parity-recovery-5bad5756/`. Read-only finder/skeptic reviews
found and repaired sibling diagnostic loss, dependency stale-state publication,
weak range assertions and stale passed artifacts; see the
[review record](../tests/editor-parity/recovery-5bad5756/reviews.md).
Reviewer temporary-file sandbox failures were not counted as passing tests.
Neither reviewer ran Lean.

Whole-scope obligations remain: every missing implementation, actual paired phase
screenshots and all visible-difference rows, full lifecycle/adversarial and proof
performance/scaling evidence, both independent judgments for every complete row,
and full/TestSuite/timed-strict/trust/KeySort gates under the required aggregate
12 GiB/no-swap scope with serial Lean `-j1` and headroom. Static classification is
not timed strict validation. No `RUNTIME_GATE_PASS`, full parity or completion is
claimed. The original parity gate must still exit nonzero until all 293 and later
new obligations have their full required evidence and judgments.


### Audit bdbc1491 — historical symbol lookup implementation

The original blocked goal is untouched. No getter is exposed in the available tool catalog; no goal mutation was used. The assigned branch and pinned base ancestry were verified at starting checkpoint `5b78e6a93820cfc95216327d5c61eabaecff05d5`. All previous checkpoints/evidence and all 293 prior obligations remain, plus nine separate lookup obligations (302 total). The original external 270-ID first-run freeze and gate/judge contracts remain unchanged. No integration action occurred.

**Source and reproduction.** Pinned `SymbolMigrationTest.cs` distinguishes current resolver results from historical migration during malformed edits. `LookupMigrationTest.cs` checks unaffected earlier symbols and relocated later symbols when middle text changes. The local normal definition succeeded, then disappeared after an incomplete incremental edit; [the corrected-cursor failure](../tests/editor-parity/recovery-bdbc1491/lookup-before-correct-position.tap) records that gap. The earlier incorrect cursor attempt is retained separately.

`lookup-state.cjs` now captures data-only locations, descriptions and document symbols after successful compilation. Safe incremental edits relocate UTF16 ranges for historical definitions, symbols, hover, local references and highlights. Hover/symbol descriptions carry `Outdated: `. Full replacements, crossed/deleted ranges, changed identifiers/directives, imported dependency bytes, retired configuration/generations and close/reopen conservatively invalidate data. Expression text, word provenance and surrounding significant tokens guard qualification and comment/string transitions. This is historical display information: no compiler AST, proof report or proof cache entry is restored; rename, prepareRename, verification and other edits retain their current compiler requirements. Historical completion/signature help and full upstream migration equivalence remain unproved.

[Eleven focused regressions](../tests/editor-parity/recovery-bdbc1491/lookup-final.tap) cover CRLF/emoji UTF16 offsets, rapid sequential changes, shadow/name/deletion/directive invalidation, cancellation and stale generations, reset/close/reopen and proof/edit isolation. The [native local service record](../tests/editor-parity/recovery-bdbc1491/local-services.json) and [ordered raw archive](../tests/editor-parity/recovery-bdbc1491/local-services.tar.gz) assert exact local/imported URIs/ranges, migrated hover/symbols, strict rename rejection, full replacement clearing, dependency-byte invalidation without a watcher and restoration after valid recompilation. This service-only run executes no proof and has no editor renderer. Independent finder/skeptic reviews repaired comment/string and adjacent/whitespace qualification counterexamples; [review details](../tests/editor-parity/recovery-bdbc1491/reviews.md) retain the findings and limits.

The bounded [synthetic metadata benchmark](../tests/editor-parity/recovery-bdbc1491/lookup-overhead-final.json) records seven ordered samples, median/p95 and RSS for 100/1,000/5,000 records after two warmups. It measures migration plus one definition query only, excluding snapshot capture, compilation, proof, worker scaling and UI. An off-by-one synthetic fixture failed before correction; its output remains in the attempt ledger. No original proof benchmark obligation is certified by these numbers.

**Related decoration boundary — Q-REL-01 [behavior:expanded-related-diagnostics; upstream:src/ui/relatedErrorView.ts; local:vscode/src/lsp-worker.cjs; local:scripts/source-locations.mjs].** The pinned UI decorates the first related postcondition location with theme-specific wavy orange underline. Current verifier output supplies aggregate function outcomes/ranges, not specific failing-postcondition identity/location. Compiler secondary notes cannot supply that proof identity. Options: provide verifier-owned failed-postcondition identity and exact location to support this UI; or keep this decoration blocked pending that metadata while independent work continues. No semantic/payload choice is assumed; no core hook was edited or fake diagnostic emitted. Future server-side hook needed: verifier-owned failed-postcondition identity plus source URI/UTF16 range, distinct from solc secondary locations.

**Validation and remaining whole scope.** [The recorded checks](../tests/editor-parity/recovery-bdbc1491/gates.json) report 177 Node passes/2 runtime skips, native services exit zero, source pin/ledger/inventory success, and original parity-gate exit **1**, **0/302** rows passing. No row is complete, so no per-row model calls or paired judgments are claimed. Source hashes bind these observations; fresh post-commit exact-head evidence is retained in `/workspace/dafny-parity-recovery-bdbc1491/`.

Q-VIS-01 and Q-RES-01 remain unanswered. No unchanged downloads/scopes or heavy Lean jobs were attempted. Full library/TestSuite/full build/timed strict/trust and KeySort runtime gates remain mandatory under the aggregate 12 GiB/no-swap serial `-j1` scope with headroom. Static trust/classification is not kernel/timed validation. The full original queue still requires every remaining implementation, paired phase screenshots and visible differences, lifecycle/adversarial tests, real proof cold/warm/median/p95/scaling benchmarks and both independent judgments for every row. No RUNTIME_GATE_PASS or completion is claimed; the unmodified parity-gate must exit zero before the goal can be complete.


### Structural lookup recovery after d7f87983

Starting head `d7f87983251f993b3d30692ca34a3113c5faf92c` was clean on the assigned branch with the pinned base as ancestor. The original persistent goal remains blocked and untouched; the tool catalog still exposes no get_goal. No reset, recreation, completion, push, merge or PR occurred. All previous artifacts/checksums, frozen270 IDs and prior302 obligations are preserved; seven separate structural/provenance scenarios append (309 total). Original gate/judge contracts, expected observations, semantics and budgets are unchanged.

**Demonstrated defects and repair.** The [native failing reproduction](../tests/editor-parity/recovery-structural/reproduced.json) shows a lookup still targeting AncestorA.field after the containing contract changes to AncestorB while another edit leaves parsing incomplete. The initial fixture's off-by-one expected columns are retained separately. [Pre-repair focused failures](../tests/editor-parity/recovery-structural/scope-before.tap) also demonstrate stale lookup after a brace change and changed declaration type. These are real failures, not waived observations.

Compiler-derived declaration-header guards now cover local types, signatures, inheritance and receiver provenance. Header token changes conservatively retire historical data, including namespace/type prefixes inserted just outside old AST spans. Lookup entries and targets must retain the identity of every enclosing lexical brace opener. Whole call/member/index/operator context and receiver-name edits guard overload and shadowing changes away from the queried name. This is still historical read-only data: no compiler AST, proof result/cache or edit authority is restored. Existing current compiler requirements for verification and rename remain intact. Document symbols remain a clearly Outdated historical tree, not a current scope tree; arbitrary malformed-program correspondence is not claimed.

The [final native record](../tests/editor-parity/recovery-structural/native-services.json) and [ordered traffic archive](../tests/editor-parity/recovery-structural/native-services.tar.gz) assert original target → null during structurally changed incomplete source → exact new compiler target after valid recompilation for inheritance, moved block boundaries and overload arguments. Existing safe incomplete sibling migration and foreign dependency invalidation/recovery still pass unchanged. This runs actual solc-backed local services only; it is not a new Dafny trace, renderer run or kernel proof. Pinned SymbolMigrationTest/LookupMigrationTest distinguish migrated versus current resolver data and retain unaffected locations, but full correspondence remains incomplete.

[15 focused tests](../tests/editor-parity/recovery-structural/scope-final.tap) include same-depth brace identity replacement, receiver shadowing, exact UTF16 ranges, stale/cancelled generations, config/reset, close/reopen and proof/edit isolation. The full suite records181 passes/2 runtime skips. Finder/skeptic reviews repaired a quadratic header scan and benchmark omission: token ranges are indexed, brace stacks linked, and the bounded benchmark now includes header guards and depths32/128. [Raw samples](../tests/editor-parity/recovery-structural/metadata-final.json) cover warm migration/query overhead only; snapshot capture, compiler/proof/UI and worker scaling remain unmeasured. [Review details](../tests/editor-parity/recovery-structural/reviews.md) preserve findings and limits. These reviews are not paired fresh-process row judgments.

**Whole original scope remains unfinished.** parity-gate must still exit1 with0/309 passing until every aspect and both judgments are present. Q-VIS-01, Q-RES-01 and Q-REL-01 retain their prior unanswered wording/options: official VS Code provisioning; enforceable aggregate12GiB/no-swap scope; authentic verifier-owned failed-postcondition identity/location. No unchanged download/scope probes, fake postcondition metadata, visual waivers or heavy Lean runs occurred. Remaining work includes every unresolved contribution/API/protocol/lifecycle implementation, actual paired phase screenshots, complete adversarial tests and real proof cold/warm/median/p95/scaling benchmarks, fresh row evidence/judgments, mandatory full/TestSuite/timed strict/trust and KeySort gates under serial-j1 limits/headroom. Observed Lean/Lake versions are not proof/runtime evidence; no RUNTIME_GATE_PASS or completion is claimed. Post-commit exact-head gates and absolute patches/handoff/checksums are retained in `/workspace/dafny-parity-recovery-structural/`.


### Startup/version recovery after c6dc1c60

Starting clean head `c6dc1c60c4ce722be702e6bc6c40c2009c939c34` and pinned base ancestry were verified on the assigned branch. The original goal remains blocked and untouched; no get_goal operation is exposed. All prior artifacts/manifests and309 obligations/frozen270 IDs remain, plus17 distinct startup/adversarial scenarios (326 total). No reset, reactivation, completion, push, merge or PR occurred. Original gate/judge contracts, verification semantics, intrinsic types and proof budgets remain unchanged.

**Source and failing observations.** Pinned startupCheck/dotnet/installation/extension/version code checks supported .NET before initialization, offers explicit configuration/download actions, waits for its custom version notification with a five-second unknown fallback, and disposes subscriptions. Local README already requires Node18+, manifest engine VSCode^1.85 and lean-toolchain Lean4.24.0; no new support threshold was chosen. [Production boundary failures](../tests/editor-parity/recovery-startup/startup-before.tap) show an empty backend initialized and missing runtime error lacking setting context. The version attempt instead failed because SOLKEY_ROOT was absent, not as version evidence; that failure and its first repaired rerun remain recorded. Subsequent runs use the existing pinned compiler source environment.

`startup.cjs` now bounds runtime version probing at5000ms, validates the existing Node18+ contract and readable declared backend files, and prevents initialization on concrete preflight failure. Missing/unexecutable runtime and unknown/unsupported claimed versions have regressions; unsupported runtime version is an injected fixture, not a provisioned Node17 binary. Initialization failures preserve causes and offer settings; runtime failures additionally offer an explicit Node download-page link. No executable is downloaded/replaced. Workspace trust precedes client creation; cancellation, closed/replaced documents, ownership epochs and resource configuration generations suppress obsolete work/actions. Current failed clients retire with disposal; healthy folder clients survive scoped recovery. Existing protocol fixture now answers --version using actual process.version, without changing its protocol expectations.

**Independent original version-status and adversarial implementation.** The server initialize version now derives from its running extension manifest instead of a stale literal. The per-document right-hand status item displays actual server identity, Node and extension metadata; missing/malformed version remains unknown. There is no invented supported server-version range. Local identity comes from the standard initialize result under the existing30-second request bound; exact Dafny custom-notification/five-second unknown temporal parity remains unproved. Version display is neither compiler/backend nor proof readiness. Injected tests cover visibility, failure, cancellation, config recovery, close/reopen and subscription disposal; rendered equivalence remains blocked.

[Native startup observations](../tests/editor-parity/recovery-startup/native-startup.json) and [ordered raw protocol archive](../tests/editor-parity/recovery-startup/native-startup.tar.gz) retain missing/unexecutable runtime and missing backend → configuration correction → successful real initialize → invalid worker initialization → correction → scoped restarts/warm reuse → disposal. The healthy folder retains its PID. All seven spawned server children have exit state and owned-PID absence asserted after cleanup. Five ordered serial process-cold and five warm samples supply median/p95; OS caches remain warm and these are startup-only timings, not proof/parallel-worker benchmarks. [Existing native service scenarios](../tests/editor-parity/recovery-startup/native-services.json) also pass. No Lean proof or rendered host was run.

[Finder/skeptic reviews](../tests/editor-parity/recovery-startup/reviews.md) reproduced ownerless/retired errors, stale workspace symbols, old close/reopen prompt actions and shared-client ownership ABA. Failing outputs and the new fixture object/URI assertion correction remain in [the ledger](../tests/editor-parity/recovery-startup/attempts.json). Repairs capture document identity/generation, per-URI epochs and workspace ownership revisions; healthy-folder actions remain usable across unrelated changes. Both final reviews found no additional demonstrated defect. These are source reviews, not paired row judgments. Full lightweight validation records196 passes/2 runtime skips.

**Whole original scope remains unfinished.** Original parity-gate still exits1,0/326 rows passing, none complete and no per-row model calls. Q-VIS-01, Q-RES-01 and Q-REL-01 retain their unanswered questions/options; no decision is presumed. No unchanged downloads/scopes, policy bypass, fabricated postcondition metadata or heavy Lean runs occurred. All remaining contribution/API/protocol/lifecycle implementations, actual paired phase screenshots/visible differences, full adversarial and real proof cold/warm/median/p95/scaling matrices, fresh complete-row evidence plus both judgments, mandatory full/TestSuite/timed strict/trust and passing KeySort runtime remain necessary. Aggregate12GiB/no-swap enforcement, serial-j1 and headroom remain binding. Observed Lean/Lake versions and startup/compiler/service/injected evidence are not kernel proof. No RUNTIME_GATE_PASS or completion is claimed. Post-commit exact-head commands/exits and absolute patches/handoff/checksums are retained in `/workspace/dafny-parity-recovery-startup/`.


### Version notification lifecycle recovery after 7dd84beb

Observed clean starting head `7dd84bebbc15a1ac19db31d134f1ea5270f477e7`; assigned branch and pinned base ancestry verified. Original persistent goal remains blocked and untouched; get_goal remains unavailable. All prior checkpoints/artifacts/manifests,326 rows and external frozen270 IDs are preserved;16 distinct temporal/API/adversarial scenarios append (342 total). No push/merge/PR, reset/reactivation/completion, new Lean source or verification-semantic/budget change occurred.

Pinned extension.ts waits after client.start for onServerVersion, races5000ms/unknown, then disposes; the pinned C# StartedAsync producer sends actual DafnyVersion. The [existing reference trace extraction](../tests/editor-parity/recovery-version/reference-version-order.json) retains initialized at index3 and actual legacy version notification at index6 with native value4.11.0.0. This is an unchanged pinned recording, not a new reference/editor run. The [before failures](../tests/editor-parity/recovery-version/version-before.tap) establish that local native producer notification was absent and a delayed injected notification lost to immediate initialize header metadata.

The local server now emits `solidityLean/serverVersion` once after initialized using its actual running manifest metadata. It does not masquerade as Dafny or invent proof/diagnostic data. The client registers before startup to retain early metadata, begins its separate5000ms decision after the initialize response, and publishes matching notification data or unknown on timeout. The existing30000ms initialize deadline is unchanged. Malformed/wrong-name messages do not resolve; duplicate/late messages cannot replace a settled identity. Decision, transport failure, cancellation and disposal release timers/registrations. Per-owner epochs and scoped restart guards remain. Early metadata stores normalized fields only, capped at128 candidates/64KiB; overflow fails STARTUP explicitly instead of dropping data into a passing/unknown result. These are operational transport limits, not a version support policy or raised proof/test budget.

The [ordered matrix](../tests/editor-parity/recovery-version/versions.json) and [raw archive](../tests/editor-parity/recovery-version/versions.tar.gz) distinguish native producer data from injected early/missing/malformed/late/duplicate/failure/disposal/cancellation cases. Raw sequence/source labels preserve initialize response → initialized → version → identity; a real duplicate initialized message produces no second native version. Missing fixtures wait the real5000ms fallback; late data remains raw but cannot publish. Close/reopen of pending fixture A followed by scoped configuration recovery uses the actual native producer while healthy native B retains its PID. Handler/timer cleanup and owned server child exits/PID absence are asserted. These observations do not certify rendered UI, compiler/EVM agreement or kernel proof.

**Further independent original API/adversarial work.** RpcPeer notification registrations now return ownership-safe disposables, and closed transports release handler maps. Request/verification/workspace waits at readiness and restart barriers cancel promptly without cancelling shared discovery or creating clients after cancellation. [Review failures](../tests/editor-parity/recovery-version/attempts.json) retain wrong early-name selection, workspace cancellation, handler retention, unlimited early metadata and cleanup counterexamples. Harness cleanup attempts every manager/client, preserves errors and emergency-stops owned children even after falsely resolved disposal; cleanup errors remain fatal. The new cleanup fixture's missing disposal method was corrected with its failed output retained, not an expected observation relaxed. [Finder/skeptic reviews](../tests/editor-parity/recovery-version/reviews.md) verified repairs and reported no remaining demonstrated defect. These are not the paired fresh-process row judgments.

Full lightweight checks record210 passes/2 runtime skips; [normal startup](../tests/editor-parity/recovery-version/startup.json) and [existing native services](../tests/editor-parity/recovery-version/services.json) also pass. Whole original gate remains exit1,0/342,none complete/no per-row model calls. Q-VIS-01/Q-RES-01/Q-REL-01 remain unanswered with prior wording/options; no decision, scope waiver, fake postcondition metadata, unchanged network/cgroup probe or heavy Lean run occurred. Remaining implementations, all paired VSCode phases/visible differences, complete adversarial and real proof cold/warm/median/p95/scaling matrices, both row judgments and mandatory full/TestSuite/timed strict/trust/KeySort remain necessary under aggregate12GiB/no-swap, serial-j1 and headroom. Version/service/injected evidence and observed Lean/Lake versions are not proof/runtime gates; no RUNTIME_GATE_PASS or completion. Exact committed-head commands/exits, patches, handoff and checksums are retained in `/workspace/dafny-parity-recovery-version/`.


### Status summary/menu recovery after 7593670b — audit e0914c14

Observed clean head `7593670b857b11a2466ad926cb282eb352a5fcc5` on the assigned branch with pinned base ancestry. Original blocked goal is untouched; no read goal operation is exposed and no mutation/reset/reactivation/completion occurred. All prior checkpoints/manifests,342 obligations and frozen270 IDs remain;21 independent status/lifecycle scenarios append (363 total). No push/merge/PR, new Lean source, verification premise, proof/fuel/node/test budget increase or gate/judge change.

**Before evidence and authentic summaries.** [Initial failures](../tests/editor-parity/recovery-status/status-before.tap) reproduce generic messages losing counts/names, source-mismatched state overwriting current data, wrong-document picker actions and document jobs pretending all functions run. Terminal status now retains actual backend names, outcomes, direct-check/audit fields and error counts. Document job metadata reports declarations ready/unverified until authentic outcomes exist; it does not invent per-function scheduling. Summaries expose completed/total, running/preparing names, failed names/counts and every incomplete category. Completion counts include reported proved/direct-correct/failed outcomes, not a proof count. Direct checks and unspecified proof modes stay distinct; unknown/unsupported/stale/cancelled do not become proved. Unknown/incomplete/vacuous entry audits remain visibly qualified, preserving existing model judgments.

**Lifecycle/API and further original work.** Producer source hashes, echoed client synchronization IDs and document object/text guards reject stale data, including identical URI/version/text reopen. Invalid metadata is validated before cancelling existing work. Menu ownership includes per-document lifecycle epochs and active-editor changes, rejects ownerless/ABA/closed/replaced/disposed/config-stale pickers, but allows legitimate live progress and unaffected-folder actions. Issue drafts derive from declared GitHub repository metadata and use current server/Node/extension data at selection; no source is attached and no issue is submitted. A separate concrete gap left compilation spinning on rejection; [its failure](../tests/editor-parity/recovery-status/compilation-before.tap) is retained. Current analysis now publishes compilation failure, while aborted/replaced attempts cannot publish late ordinary errors or diagnostics. No parsing/resolution/proof stage is invented.

**Pinned/native observations.** [Exact pinned-source output](../tests/editor-parity/recovery-status/reference-comparison.json) executes compilationStatusView and statusBarActionView with an explicitly injected editor/document boundary. Counts/names compare directly; text differences remain, including local Completed rather than Verified for finished work and no-results rather than pinned success for empty symbols. The pinned modern verifying text uses lowercase while its help condition checks uppercase Verifying; actual menus are retained. These differences are not waived and no row is complete. [Native status/controller observations](../tests/editor-parity/recovery-status/native-status.json) and [raw archive](../tests/editor-parity/recovery-status/native-status.tar.gz) record actual compiler/status/identity transport through production controller code and injected VSCode APIs: compile → failure → fix, rapid edits, background document, close/reopen, cancellation, scoped restart preserving healthy PID, explicit mocked issue selection and disposal. Mixed proof/check outcomes are injected tests, not new kernel evidence. The first harness launch failed because its edit assembly omitted the helper module; that failure remains separate from runtime/compiler claims.

**Reviews and validation.** Finder/skeptic [reproductions](../tests/editor-parity/recovery-status/review-before.tap) found internal direct alias false success, lost audit qualification, invalid-open side effects and ownerless picker behavior. All were repaired. Native rapid-edit checks now use recursive assertServiceSymbols rather than serialized substring matching. [Final reviews](../tests/editor-parity/recovery-status/reviews.md) found no remaining demonstrated defect; these are source reviews, not paired row judgments. Full lightweight checks record227 passes/2 runtime skips; strict native status/reference, version lifecycle and existing services pass. Post-commit exact-head gates/patches/handoff/checksums reside in `/workspace/dafny-parity-recovery-status/`.

**Q-STATUS-HELP-01 [upstream:src/ui/statusBarActionView.ts; local:vscode/package.json; local:vscode/README.md].** No local public proof-help destination is declared. Which destination should the conditional proof-help action use? Options: provide an approved proof-help URL, enabled only after explicit selection; use the existing repository verification guide docs/solidity-testing.md instead of a public question service; or keep external proof-help blocked pending a destination while independent status/local-output work continues. No option is assumed. Conditional local-output inspection is implemented separately, not represented as the missing public service.

Whole original scope remains unfinished: parity-gate exits1,0/363,none complete/no per-row model calls. Q-VIS-01/Q-RES-01/Q-REL-01 remain unanswered with prior wording/options; no unchanged network/cgroup attempt, fake postcondition metadata, scope waiver or heavy Lean job. Remaining contribution/API/protocol/lifecycle implementations, all paired VSCode screenshots/visible differences, full adversarial and real proof cold/warm/median/p95/scaling matrices, both judgments per row, mandatory full/TestSuite/timed strict/trust/KeySort and compliant aggregate12GiB/no-swap serial-j1/headroom remain necessary. Legacy status packets without hashes/synchronization IDs retain weaker correlation. Rendered equivalence, compiler/EVM agreement and kernel/runtime proof are not established by these service/injected observations or observed Lean/Lake versions; no RUNTIME_GATE_PASS or completion.


### Automatic Testing recovery after 6f487977 — audit 97e445d4

Started from clean `6f487977ba10e2e4ea007d2aedc18d8cb62b757c` on the assigned branch with original-base ancestry. Existing blocked goal is untouched; no getter is exposed and no mutation/reactivation/reset/completion was called. All prior commits, external frozen270 IDs and artifact manifests remain binding. Twenty-one separate automatic Testing scenarios append to363 prior rows (384 total); none is complete. No Lean source, proof premise, proof/fuel/node/test budget, exclusion, gate or judge contract changed; no push/merge/PR.

[Before evidence](../tests/editor-parity/recovery-auto-testing/before.tap) demonstrates reports only updating descriptions rather than producing automatic TestRuns. Production `automatic-testing.cjs` now projects accepted native result rows through the existing model classifications, without starting proof work. Explicit function-level queued/running updates can enqueue/start existing current items; document-wide compilation/verification and ready/listing declarations never fabricate individual progress or success. Terminal direct checks remain described as correct rather than kernel-proved; incomplete/vacuous audit outcomes retain the existing attention/error classification. Report errors prevent passes. Duration uses an authentic row duration when present, otherwise only elapsed time since an explicitly observed function-running state.

Ownership covers document object/version/text and native synchronization IDs on reports/status/invalidation, including identical URI/version/text reopen. Native server echoes the existing synchronization identity rather than inventing a Dafny API. Manual profiles claim their documents so streamed/manual responses cannot create a second automatic run; existing selection/exclusion and cancellation expectations remain. Automatic groups end once on edit/removal/close, cancellation, compiler failure, scoped configuration/restart/crash, hidden display, context disposal and deactivate. Completed runs release cancellation registrations; cancellation cannot feed back into newer text. Hidden and stopped states are separate. Malformed status metadata cannot mutate runs.

[Reviewer counterexamples](../tests/editor-parity/recovery-auto-testing/review-before.tap) retain cancellation -> hide/show reviving a pass, terminal companion statuses creating duplicate skipped runs, and queued cancellation blocking a legitimate retry. Repairs preserve the original expected observations. [Independent finder/skeptic reviews](../tests/editor-parity/recovery-auto-testing/reviews.md) confirmed final fixes and found no remaining demonstrated source defect; these are not the two fresh-process per-row judgments. Two existing manual regression assertions now select the manual run after the newly visible automatic run, preserving their full enqueued/started/terminal/end expectations and adding automatic expectations.

[Ordered native observations](../tests/editor-parity/recovery-auto-testing/native-testing.json) and [raw archive](../tests/editor-parity/recovery-auto-testing/native-testing.tar.gz) exercise native compiler failure/fix, source changes, close/reopen session identity, cancellation, global restart, genuinely scoped configuration recovery preserving another folder's owner/PID, and child/subscription cleanup through the production extension controller and injected editor API. Explicitly injected progress and proved outcomes are labeled and do not establish real proof transitions. [Pinned-source execution](../tests/editor-parity/recovery-auto-testing/reference-comparison.json) records queued/running/terminal/stale/empty and duplicate behavior without a reference server or renderer. Local grouping, symbol hierarchy, actionable editor buttons, full automatic proof scheduling and rendered/timing correspondence remain unproved.

Further original protocol/API work adds native report/invalidation session rejection, report-error qualification, malformed payload handling, context-owned disposal and explicit-function timing. Remaining contribution rows were inspected: public build/run/custom-argument/trace commands are still absent, and existing verify/list commands are not silently relabeled as their implementation. No trace, postcondition metadata, support threshold or semantic profile is fabricated.

Validation retains actual failed exits: unset default sibling compiler path, initial implementation/reviewer failures, and three unchanged native-plugin mock startup deadlines under concurrent scheduling. Existing `.cache/parity-solkey` is the configured compiler fixture; no download/provisioning was repeated. Serial full Node suite passes255 tests with2 runtime skips and unchanged deadlines. Native Testing/reference and existing service checks, inventory/source pins/audit and static trust/strict classification pass. Static classification is not timed strict. Unchanged parity-gate exits1,0/384; prechecks reject all incomplete rows without model calls. Exact committed-head gates, original patch, handoff and checksum manifest are in `/workspace/dafny-parity-recovery-auto-testing/`.

Whole original scope remains outstanding: missing contribution/API/lifecycle/protocol aspects; all paired VS Code screenshots/visible differences; full adversarial and actual proof median/p95/cold/warm/scaling matrices; both independent judgments for every row; final full/TestSuite/timed strict/trust/KeySort. Lean4.24.0/Lake5.0.0-src+797c613 are observed, but KeySort/runtime is not passed and no RUNTIME_GATE_PASS is claimed. Q-VIS-01, Q-RES-01, Q-REL-01 and Q-STATUS-HELP-01 remain unanswered with unchanged options. No heavy Lean until enforceable aggregate12GiB/no-swap, serial-j1 and OS headroom; no unchanged network/cgroup probes, scope waivers or goal completion.


### Current Testing hierarchy and truthful contributions — audit50a2b0dc

Started from clean `35eb0be79d298b3a7254dcf0c068d609a1a9b7c0` on the assigned branch with original-base ancestry. Original blocked goal is untouched; no read-goal tool is exposed and no mutation/reset/reactivation/completion was called. All384 prior obligations, frozen270 IDs, protected commits and nine prior artifact manifests are preserved. Twenty-two separate hierarchy/contribution scenarios append (406 total); none is complete. No Lean source, intrinsic type, proof premise, exclusion, proof/fuel/node/test budget or gate/judge contract changed. No push/merge/PR or unchanged provisioning probe.

[Before evidence](../tests/editor-parity/recovery-hierarchy/before.tap) demonstrates flat file/function items and missing parent exclusions. `testing-tree.cjs` now projects accepted exact contract/signature identities under current compiler DocumentSymbol ancestors, matching function name and source-range containment. Parents carry current compiler selection ranges only; no parent becomes a proof result. Existing leaves retain identity and accepted outcome descriptions while moving from fallback into compiler parents, so manual and automatic owners remain stable. Synthesized constructors and absent/missing/unmatched symbols use explicit result grouping without guessed parent ranges. Physical declaration and verification contract can differ for inherited functions: Base remains the declaration parent, Derived.f() retains its exact obligation identity and the description identifies both contexts. This was an investigated provenance case, not a theorem/profile change.

Current symbol queries are display-only and never start verification. Snapshot ownership checks document object, version, text, accepted report object, latest request, cancellation/disposal and display visibility after every asynchronous reply. Historical Outdated symbols are rejected as current hierarchy data. Edit/close/reopen, config/restart, invalidation, visibility and disposal retire owned requests and recursively clear metadata. Parent selection/exclusion traverses the whole subtree, including directly included descendants, with exact live-item checks. Duplicate accepted identities fail before projection. Existing manual selection, cancellation, signature and outcome expectations remain; test helpers now select nested leaves rather than flattening the production hierarchy.

[Expanded failures](../tests/editor-parity/recovery-hierarchy/hierarchy-first.tap) retain disposal leaving the mock tree behind. [Review counterexamples](../tests/editor-parity/recovery-hierarchy/review-before.tap) retain Map mocks hiding undocumented TestItemCollection iteration and missing inherited-context qualification. Production traversal, disposal and existing manual-root enumeration now use the documented forEach API; a deliberately non-iterable boundary verifies it. Both independent finder/skeptic [final reviews](../tests/editor-parity/recovery-hierarchy/reviews.md) confirmed repairs and found no remaining demonstrated source defect. These reviews are not paired fresh-process row judgments.

[Native observations](../tests/editor-parity/recovery-hierarchy/native-hierarchy.json) and [raw archive](../tests/editor-parity/recovery-hierarchy/native-hierarchy.tar.gz) combine actual pinned solc ASTs and actual local LSP compiler symbols with production Testing controller code. Multiple contracts, overloads, inheritance, parent exclusions, compiler break/fix, removal, identical reopen, scoped config preserving another folder's owner/PID, and disposal are ordered. Editor APIs, ready result rows and manual terminal outcomes are explicitly injected, not verifier/kernel evidence. The first harness launch failed because its fixture URI changed after controller registration and its symbol-request microtask was not awaited; the failure/raw observations remain, and setup/settlement were repaired without relaxed expectations. [Exact pinned hierarchy execution](../tests/editor-parity/recovery-hierarchy/reference-comparison.json) retains matched, absent, unmatched and historical cases. Pinned unmatched items can be invisible; local unmatched results remain visible with qualified fallback grouping. File roots, fallback labels and historical rejection differ. No difference is waived or called complete.

**Further original contribution work.** The trusted Solidity-file editor context submenu now exposes only the six existing verify/list/cancel/output/status/restart operations. [Before evidence](../tests/editor-parity/recovery-hierarchy/contributions-before.tap) and the contribution regression retain the missing submenu and verify commands are genuinely registered. This does not implement or relabel Dafny build/custom/run/test/trace actions. Exact pinned compileCommands.ts saves a program and constructs target build/run/test commands (run/test use --no-verify); the local declared backend exposes verification/listing instead. Their commands and bindings remain incomplete. No default keybinding is guessed or proof verification substituted for execution.

**Q-CLI-01 [upstream:src/ui/compileCommands.ts; local:vscode/src/backend.cjs; local:scripts/test-solidity.mjs].** Which build/execution contract should be supplied before implementing Dafny build/run/test counterparts? Options: specify compiler-only build artifacts and keep run/test incomplete until a runner is chosen; specify an approved Solidity runtime/test runner and artifact contract before adding these actions; or keep build/run/test blocked pending a contract while independent editor work continues. No option is assumed. Q-VIS-01, Q-RES-01, Q-REL-01 and Q-STATUS-HELP-01 also remain unanswered, with unchanged options.

Pre-commit serial Node checks pass273 tests with2 runtime skips; two additional targeted manual-relocation/provider-failure regressions then pass as part of20 targeted cases. Native hierarchy and existing Testing/reference harnesses, inventory/source pins/audit and static trust/strict classification pass. Static strict is not timed strict. Original parity-gate still exits1,0/406,none complete/no per-row model calls. Final committed-head commands/exits and actual counts, original/recovery patches, handoff, raw evidence and checksums reside in `/workspace/dafny-parity-recovery-hierarchy/`.

Whole original assignment remains unfinished: remaining contribution/API/protocol/lifecycle implementations; all paired VS Code phases/screenshots/visible differences; full adversarial and genuine proof median/p95/cold/warm/scaling matrices; both independent judgments per row; final full/TestSuite/timed strict/trust/KeySort and required runtime evidence. Lean4.24.0/Lake5.0.0-src+797c613 were observed, but no passing KeySort or RUNTIME_GATE_PASS exists. Heavy Lean remains blocked until enforceable aggregate12GiB/no-swap, serial-j1 and OS headroom. Injected UI/results and compiler/service observations do not prove rendered equivalence, compiler/EVM agreement or kernel proof. No scope waiver or completion.


### Worker/thread/process retention recovery — audit abce42e5

Started from clean `a059c1f8da34b8921b594343c5a6149aa54b8c3b` on the assigned branch with pinned base ancestry. Existing blocked goal is untouched; no getter is exposed, and no mutation/reset/reactivation/completion was called. All406 prior obligations, external frozen270 IDs, protected commits and ten prior artifact checksum manifests remain preserved. Twenty-nine separately judged retention/RPC scenarios append (435 total), none complete. No core Lean source, intrinsic representation, theorem/premise/exclusion, proof/fuel/node/test/deadline budget, gate or judge contract changed. No push/merge/PR or unchanged provisioning probe.

**Pinned expectations and before evidence.** Exact ThreadUsageTest.cs resolves a failing Dafny proof, measures current-process threads over ten edits, tolerates +/-5 and retries up to100 times. ResourceUsageTest.cs compares actual versioned Z3 process counts before open, after verification and after an edit. Our compiler-only observations do not reproduce that proof/solver workload. [Before failures](../tests/editor-parity/recovery-retention/before.tap) demonstrate actual compiler-worker disposal returning before close, replacement starting before retired closure, and removal of the live-worker directory. [Crash evidence](../tests/editor-parity/recovery-retention/crash-before.tap) freezes one captured owned compiler worker and kills its server: the worker survived parent-only cleanup. These are real OS processes under explicitly injected faults, not solver/kernel evidence.

**Lifetime implementation.** WorkerPool now holds retiring capacity until child close and owned-session quiescence, preserving the original queued deadline through retirement and ownership admission. Idle crashes and IPC errors retire too. Reset validates settings before mutation, uses counter-based directories, and shares a start barrier with replacement pools/builds. Dispose aborts owned requests, awaits pools/build retirement and only then removes its directory; failure preserves paths and blocks unsafe admission. Server shutdown, exit, EOF and signals share awaited cleanup and report failures. Client closure no longer resolves merely because termination was requested. Per-configuration retirement rejects bounded failures promptly, retains poisoned capacity until actual cleanup is confirmed, preserves other folders and propagates cleanup failures to shutdown.

Workers/build launchers own private sessions. Authentic PID/birth/PPID/private-group metadata is registered with a capability-negotiated client before worker task dispatch. Missing, terminated, foreign or non-private registrations fail closed. Client ownership records allow cleanup after parent death; raw stdio retains the same group authority, including descendants missed by sampling, and uses birth-checked survivor cleanup. Unnegotiated legacy and non-Linux branches remain weaker/unproved, not full crash guarantees. Linux cleanup freezes only a known positive owned PID/session and uses PPID/birth readback; it does not kill unrelated processes by name. CONFIG_PROC_CHILDREN is unavailable here; the failed assumption and probe, including its masked shell exit, remain explicitly recorded rather than counted as pass.

**Build admission and further original RPC work.** A lightweight Node launcher waits for acknowledged ownership before starting the same existing Lake command/arguments. Its startup, ACK wait, command and group closure remain within the original deadline. This can add cold-build startup latency; no actual Lean build was run or benchmarked. [Admission failures](../tests/editor-parity/recovery-retention/admission-before.tap) retain missing-PID authority and fast build success before delayed refusal. Fake executables and IPC-ready -> ACK -> command-marker tests verify the repair without kernel work. [RPC before evidence](../tests/editor-parity/recovery-retention/rpc-before.tap) retains cancellation writes throwing before settlement. Cancellation and timeout write failures now settle once, remove timers/listeners and close the broken transport.

**Reviews and failures retained.** Independent read-only finder/skeptic [reviews](../tests/editor-parity/recovery-retention/reviews.md) identified descendant/build ownership, unbounded or swallowed retirement errors, released poison keys, insufficient identity validation, fast-build ACK ordering and raw-stdio group authority. All confirmed findings were repaired; final reviews found no further demonstrated source defect. These are not paired fresh-process row judgments. [Attempts](../tests/editor-parity/recovery-retention/attempts.json) preserve closure-deadline, detached-descendant, unsupported-proc, test-helper and first native URL-fixture failures. No expected original observation was relaxed and no timeout was raised.

**Measured native scope.** [Native report](../tests/editor-parity/recovery-retention/native-retention.json) and [raw archive](../tests/editor-parity/recovery-retention/native-retention.tar.gz) retain repeated actual compiler open/ten edits, attempted cancellation/recovery, three in-place configurations, three close/reopens, three scoped restarts, a frozen-worker/server crash and disposal. Every process is tied to captured ownership/start identity; healthy-folder PIDs, native pool capacity and final runnable-process readback are checked. Pre-commit server threads were7 ->7; warm compiler median65.149ms/p9585.028ms over10 samples. These are service/compiler measurements, not proof/solver performance or worker scaling. Cancellation outcomes are recorded, including races where completion can win. One terminated Z process remained after the injected crash; no runnable owned processes remained. Z is never equated with PID disappearance or solver-count stability. Crash directory removal is explicitly harness cleanup after quiescence, not claimed production cleanup. The 4GiB observation guard/12GiB reserve is not cgroup enforcement or authorization for heavy Lean.

Serial Node checks pass291 tests with2 original runtime skips. Native retention and existing service observations, inventory/pins/audit, static trust and classification-only strict pass. Static strict is not timed strict. Original parity-gate remains exit1,0/435,none complete/no per-row model calls. Exact committed-head commands/exits, original/recovery patches, handoff, raw evidence and checksum manifest reside in `/workspace/dafny-parity-recovery-retention/`.

Whole original assignment remains outstanding: remaining implementation and visual/lifecycle/protocol differences; paired VS Code screenshots at every required phase; real Lean/solver retention and all proof median/p95/cold/warm/scaling/adversarial matrices; both independent judgments per row; mandatory full/TestSuite/timed strict/trust/KeySort and runtime evidence. Lean4.24.0/Lake5.0.0-src+797c613 are observed but KeySort is not passed and no RUNTIME_GATE_PASS exists. Q-VIS-01, Q-RES-01, Q-REL-01, Q-STATUS-HELP-01 and Q-CLI-01 remain unanswered with unchanged options. No runtime/help URL/postcondition identity/profile or waiver is selected. Heavy Lean remains blocked until enforceable aggregate12GiB/no-swap, serial-j1 and OS headroom. Compiler/OS/injected-process observations do not establish rendered parity, compiler/EVM agreement or kernel proof; no completion.


### Recovery concurrency checkpoint — audit bc4721df

From clean `a262559adeaf662d4cf9555e9fcb0986e3b9ce6e` on the assigned frozen branch/base. Retained failing reproductions precede repairs to cached verification snapshot admission, per-caller shared-work cancellation, workspace multi-root/outer-await snapshot checks and diagnostic synchronization ownership. Imported dependencies, identical-source reopen and superseded late compiler errors have regressions. Neither historical display migration nor proof/cache/rename authority was relaxed. No proof, fuel, node, test or deadline budgets changed.

`tests/editor-parity/recovery-concurrency/` retains original failures, repaired tests, ordered actual compiler/LSP traffic, source expectation comparison and finder/skeptic findings/repairs. The native three-file save storm retains a final current compiler error and recovers; it runs automaticVerification never and no proof workers. The initial harness expected a symbol request rejection; actual existing behavior is empty symbols plus diagnostics. Its failed attempt is retained and the harness corrected. Compiler-only cold/warm measurements are descriptive (one cold batch, five warm requests); not native solver/kernel, rendered UI, fifty-document, thousand-method proof workload, scaling or full benchmark evidence. The upstream skipped resolution case remains skipped. Per-symbol recency verification order remains unimplemented/unproved; FIFO is not a substitute.

All existing435 rows and external frozen270 remain; fifteen additive concurrency scenarios stay partial. Both source reviews found and confirmed repairs for legacy hash support, dependency admission and nested workspace completion windows; final reviews report no remaining concrete defect. Neither review replaces paired row judgments. No row marked complete.

New absolute artifact root: `/workspace/dafny-parity-recovery-concurrency/` (HANDOFF.md, original.patch, evidence/, SHA256SUMS); prior artifact roots/checksums remain untouched. Exact committed-head gate receipts and full head/base are recorded there. Original parity-gate failure remains mandatory failure; full build/TestSuite/timed strict/KeySort, rendered phases/paired screenshots, complete native proof/solver/adversarial/performance matrices, every contribution/lifecycle aspect and both fresh-process judgments per row remain outstanding. Static trust/classification and Node/compiler tests do not prove kernel correctness or EVM agreement. Lean4.24.0/Lake5.0.0-src+797c613 previously observed; no passing KeySort or RUNTIME_GATE_PASS.

Q-VIS-01, Q-RES-01, Q-REL-01, Q-STATUS-HELP-01 and Q-CLI-01 remain unanswered with original options. No downloads/resource probes repeated, no heavy Lean launched, no fake postcondition metadata/help destination/CLI contract chosen. Original persistent goal remains blocked and untouched; no get_goal tool exposed here and no substitute mutation invoked. No push, merge or PR.

Precommit reviewed gates: serial Node302 pass/2 existing runtime skips; native compiler concurrency passed-with-gaps; inventory450 rows, pins, independent audit, static trust and classification-only strict exit0. Unchanged parity-gate exit1,0/450. Eleven previous checksum manifests verified unchanged; frozen270 hash unchanged. Exact-head repeat receipts are in the new artifact root.


### Recovery large-file checkpoint — audit29e7e399

From clean `aa8b5771bd4082267393abecac9ad4630356810e`, assigned branch/base unchanged. Extended the existing workload helpers and lifecycle entry point (`startup.cjs --output NEW_DIRECTORY --large-file`) with a native compiler/LSP-only1000-function/100-prepend scenario. Every accepted increasing version must have the exact source hash/session; every function name, whole range and UTF16 selection range is checked before/after exactly100 real newline prepends. Newest compiler error/fix, managed stale-query rejection, request-frame cancellation, bounded late-error observation, zero proof workers, request quiescence and owned disposal are asserted. Cold/warm labels require actual server/compiler PID reuse. One file open; no50-document stress.

Initial harness attempt mistakenly inserted literal backslash-n and wrote invalid JSONL separators. Original exit0/bytes are retained but explicitly invalidated in `first-attempt-invalid.txt`; it is not passing scenario evidence. Corrected native observation and three subsequent samples passed-with-gaps. The native workload demonstrated no compiler/migration defect. Separate injected inner-reply regressions demonstrated managed request version/text/close/cancellation and workspace cancellation delivery gaps; source guards now revalidate after nested awaits and before client acquisition. Both original failing TAP files retained. Historical display data and proof/cache/rename checks remain unchanged.

Three precommit native samples: process-cold open5279.97ms(n1), warm open median4047.63ms/p954062.51ms(n2),100-edit median12578.98ms/p9514120.83ms(n3). OS caches retained, same actual server/compiler PIDs; observed aggregate peak740831232bytes including harness sampling. Compiler stop threshold4GiB and12GiB OS reserve are observation guards, not cgroup/no-swap enforcement. All upstream settings, source hash,1000/100 counts, ten-attempt ceiling, strict scheduling<100ms and ratio<15 expectations are retained. Harness timer drift is not C# Task.Run(Thread.Sleep(100)); no threshold or proof-performance equivalence is claimed. Fixed native samples retain all failures and stop on failure; no hidden retry/pass. Original full proof workload and retry/performance correspondence remain unproved.

Finder/skeptic reviews traced exact managed-client authority boundaries, found the workspace cancellation gap, and confirmed repairs; final reviews found no remaining concrete defect. Eleven targeted tests and full serial suite313 passes/2 existing runtime skips. Inventory/pins/audit/static trust/classification pass; unchanged mandatory parity-gate remains exit1,0/464. All450 prior IDs and frozen270 retained; fourteen additive scenarios stay partial, no row complete and no paired row judgments substituted.

New absolute artifacts `/workspace/dafny-parity-recovery-large-file/`: original.patch, HANDOFF.md, evidence/, SHA256SUMS, exact-head receipts and sealed bundle. Previous artifacts/checksums remain unchanged. All original contribution/API/lifecycle/visual/protocol obligations, actual native proof/solver/scheduler/scaling matrices, paired screenshots and both independent judgments per row remain required. Full build/TestSuite/timed strict/KeySort remain blocked on Q-RES-01; Lean4.24.0/Lake5.0.0-src+797c613 previously observed but no passing KeySort/RUNTIME_GATE_PASS. Node/compiler/injected evidence proves neither kernel correctness, EVM correspondence nor rendered parity.

Q-VIS-01,Q-RES-01,Q-REL-01,Q-STATUS-HELP-01,Q-CLI-01 remain unanswered with unchanged options. No provisioning retries, guessed metadata/help/CLI policy, semantic changes, new Lean sources/axioms/sorry, changed expected observations, raised proof/fuel/node/test/deadline budgets or gate/judge weakening. Original goal remains blocked and untouched; getter unavailable, no mutation invoked. No push/merge/PR.


### Recovery hover correspondence checkpoint — audit8bb3c280

From clean `0654dfc05cf3c65673faf0afdf969ad905871b18`, assigned branch/base unchanged. Strengthened the existing shared service hover assertion: unrelated nonempty text cannot certify the source declaration. Local exact Markdown/signature/type/comment and queried occurrence ranges are checked; reference assertions retain pinned full expected Markdown substrings. Definition URI/ranges validate lexical targets in both. Pinned handler explicitly lacks hover ranges (TODO); no reference range was fabricated. The actual reference executable reports4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2, matching the source pin, with executable/DLL hashes retained.

Compiler-backed failures reproduced before repair: plaintext function-type hover lacked declaration signature/Markdown; compiler documentation retained a delimiter-prefix space; valid modifier check(S({x:1})) truncated at its inner brace. Display now derives headers from compiler body/source provenance with a balanced fallback, and documentation from compiler-owned comment spans. No AST/proof inputs or source semantics changed. An injected actual-production-provider test also showed appendText escaped Markdown; the adapter now preserves Markdown and continues escaping plaintext proof/historical values without enabling trust/HTML. This is not renderer evidence.

Extended existing stdio runner with paired native local/reference declaration/use, formal/field/local/inner-block/scope-exit/explicit receiver, comments, unknown null, incremental UTF16, foreign declaration/unsaved dependency update, parse/type error/fix and reopen observations. Native local --hover lifecycle entry point additionally records edit/late reply, identical URI/version/text reopen, config reset, scoped restart, cancellation, background-folder isolation, quiescence and owned disposal. Verification remains disabled. Explicit differences persist: local replacement-error null versus Dafny parse placeholder or resolved declaration during type error; proof-summary precedence, full comment/plugin/language bindings and reference extension lifecycle are unfinished. Hover-before-proof-completes remains separately partial with injected-verifier-only evidence.

Original assertion-before, strong-before, lexical-first, header-before and provider-before failures are retained. Full serial Node initially exposed2 shutdown-only oracle fixture failures after strengthening; updated explicit fixture returns source expectations while retaining original lifecycle-failure/cleanup assertions. It is not native evidence. Finder/skeptic reviewed source and failures; skeptic found nested-brace defect, repaired and confirmed; both final reviews found no remaining concrete defect. Neither review substitutes for paired row judgments.

Precommit checks:320 Node passes/2 existing runtime skips; paired native services and native hover lifecycle passed-with-gaps; inventory480 rows, pins/audit/static trust/classification exit0; unchanged mandatory parity-gate exit1,0/480. All464 prior IDs and frozen270 retained,16 additive scenarios remain partial; no row complete.13 prior checksum manifests verified unchanged. Exact committed-head receipts and original full-scope report are exported under `/workspace/dafny-parity-recovery-hover/` (original.patch,HANDOFF.md,evidence/,SHA256SUMS,sealed bundle).

All original independent contribution/API/lifecycle/protocol/visual implementations, native proof/solver/scheduler/retention and full performance/cold-warm/median-p95/scaling/adversarial matrices, paired screenshots and both fresh-process judges per row remain necessary. Compiler/reference/injected observations prove neither kernel correctness, EVM correspondence nor rendered parity. Full build/TestSuite/timed strict/KeySort remain blocked by actual aggregate12GiB/no-swap serial-j1 enforcement; observed compiler RSS is not enforcement. Lean4.24.0/Lake5.0.0-src+797c613 previously observed, no passing KeySort/RUNTIME_GATE_PASS.

Q-VIS-01,Q-RES-01,Q-REL-01,Q-STATUS-HELP-01,Q-CLI-01 remain unanswered, original options unchanged. No provisioning repeats, proof metadata/help/CLI policy choices, new Lean source/axioms/sorry, weakened rows/gates/judges/expected observations or raised proof/fuel/node/test/deadline budgets. Original persistent goal remains blocked and untouched; getter unavailable and no mutation used. No push/merge/PR.


### H44 source/bulk split — human decision2026-11-05

H44 authorizes keeping generated fixtures/evidence/corpora/logs out of git.376
lane-added bulk files are retained byte-for-byte on this VM and ignored at their
original repo-relative paths. Final archive/index and preserved original snapshot
paths, sizes and SHA256 values are committed in
[the bulk manifest](dafny-parity-bulk-manifest.json). No test inputs, rows, traces,
expected observations, predicates or proof/fuel/node/deadline budgets were weakened.
All480 obligation IDs and external frozen270/hash remain unchanged. Required
inventory/control metadata, authored source/tests and small handwritten hover
fixtures remain reviewable tracked inputs; generated observations are archive-only.

The source-only commit is based directly on master260441fd82852fc1c294e62f6818e15de6375ceb.
Prior lane tip996369b39d9ec009b6c09aab325573be2a7bad36 and its full protected history
remain under refs/archive/solidity-dafny-20261105/dafny-parity-pre-h44 and the
manifest-bound VM Git bundle. No hard reset/discard or push/merge/PR was performed.
The next integration can take the source-only head without importing bulk history.

Use scripts/coord-tools/dafny-parity-bulk.py under the writer lock to verify/restore
exact ignored inputs before unchanged tests/gates. Fresh-checkout restore and
permission preservation pass; corrupt archives, traversal, symlinks and tracked
paths are rejected. Finder/skeptic reviewed the helper and explicit CI preparation,
with no remaining safety finding. Hosted CI is **blocked pending coordinator bundle
provisioning**: merely setting DAFNY_PARITY_BULK_DIR cannot copy/mount VM bytes to an
ubuntu-latest runner. No artifact publication or network destination was assumed.

Packaging checks:320 Node passes/2 existing runtime skips; inventory/pins/audit and
classification-only strict pass. Unchanged parity-gate exits1,0/480. Static trust
exits1 with2 inherited master inventory drifts for expressionPathAnyM/referencesM
in Solidity/Frontend/QualifiedUnits/References.lean; that file, trust inventory and
gate scripts match integration parent exactly. Findings retained, not repaired by
changing core sources or trust predicates in this packaging-only task. No Lean or
other heavy gates run; no RUNTIME_GATE_PASS. Full assignment, five unanswered human
questions, actual proof/rendered/performance matrices and paired row judgments
remain outstanding. Goal status is untouched. Full receipts and hashes are in
/workspace/dafny-parity-bulk-h44/; prior artifact manifests remain unchanged.


### Human decisions H47-H50 and serial resource authorization —2026-11-05

The five prior questions now have answers, recorded in docs/dafny-human-decisions.json.
Historical H49 exclusion claims in this checkpoint are superseded by incoming H80:
proof help links project README and calculus guide; no current exclusion is assumed.
The official VSCode1.108.0 archive provisioned at /workspace/vscode-official/ passes
sha256sum -c against the saved official API hash. docs/dafny-provisioned-assets.json
records exact paths/sizes/hashes. Editor/version is1.108.0/94e8ae2b28cb5cc932b86e1070569c4463565c37;
archive, extraction and cached Xvfb remain offgit under H44; no download retried.
Rendered rows remain open until fresh paired evidence is collected.

Historical concrete-model CLI work is documented in vscode/README.md. H80 now
specifies compiler-only Build and keeps runtime/test equivalence incomplete.
Build writes a real compiler AST/source-hash artifact; Run selects Contract::function;
Test executes concrete cases and compares exact status/text. None publishes proof
or EVM-equivalence evidence. Source/dependency/function identity, pending prompt
nonces/resource config, stale errors and physical child retirement are guarded.
Reviewer failures were retained before fixes;25 targeted command/status and39
command/editor checks pass. The initial full Node run retained an old contextual
help assertion failure; that checkpoint replaced help with ordinary output. H80
has since restored proof documentation help, superseding the H49 claim,
while unrelated-folder picker ownership assertions remain. No budgets increased.

Q-REL-01 is authorized but not implemented: whole-goal kernel refutation cannot
identify a particular failed ensures clause, direct results are uncertified, and
raw clause byte provenance is lost before binding. The real hook needs stable
owner/ordinal/source spans and clause-specific certification before decoration;
no fabricated postcondition metadata was emitted. Read-only source review retained.

Coordinator Q-RES authorization permits isolated serial heavy gates without a
systemd scope. They will be attempted, not left blocked: pinned Lean4.24.0 and
Lake5.0.0-src+797c613, LEAN_NUM_THREADS=1, temporary weak -j1 arguments only, no other
work alongside,12GiB observed aggregate intent/available reserve and no swap.
Missing enforced scope remains a limitation. Cache --no-build readiness exits3
because modules require building; not a successful proof gate. Actual full,
TestSuite,timed strict,KeySort and renderer outcomes will follow in the handoff.

All480 original IDs/frozen270 remain;4 concrete-command scenarios are additive and
partial. Original source/bulk split persists. Receipts remain outside git under
/workspace/dafny-parity-decisions-20261105/. Full original proof/rendered/performance/
scaling/adversarial/paired-judge obligations remain; no RUNTIME_GATE_PASS, theorem,
axiom/sorry, proof/fuel/node/test/deadline budget, goal-state or gate changes.
No push/merge/PR. Execution interrupted before committing; no heavy gate started.

### Authorized gates and rendered observations — 2026-11-05

Source checkpoint `7c586a31518cf24f7facf5842984f496f116f2eb` committed successfully; the prior interruption note is historical. Full gate was actually attempted serially under the coordinator resource authorization. Touched-file gate passed. The monitored owned aggregate peaked at5,023,707,136 bytes RSS; no swap. Available memory fell to12,884,238,336 bytes (below the12GiB reserve), so the guard killed only owned processes. Full gate exit-9/supervisor exit1; this is failed validation. Missing enforced scope remains recorded. No full/TestSuite/timed strict/KeySort pass or RUNTIME_GATE_PASS. No proof-budget or theorem changes.

Official archive checksum passes against the saved update API. Cached Xvfb and actual Electron executable run the existing renderer harness. Initial CLI-wrapper launch failed before host evidence; preserved. Actual upstream run exposed suite validation incorrectly requiring the nonvisual initial-verification scenario, then a missing launcher suite identity. Both have failing regressions, focused repairs and independent read-only finder/skeptic reviews. Visual suite now requires all five scenarios; missing/partial/checks/identity/aggregate classification and nonvisual proof checks remain. No parity-gate or judge changes.

Final paired observations: pinned Dafny five phases partial, local open missing/first feedback partial, local verified/broken/fixed scenarios fail on genuine unsupported results (compiled verifier unavailable). Actual screenshots/DOM/accessibility/LSP/status traffic retained; no owned survivors. No substitution of unsupported for proved. Shared source fragment is semantically paired across languages, not identical syntax. Native proof/rendered equivalence is still unfinished.334 Node passes/2 original skips precede two additional passing visual regressions.

Bulk, prior failed attempts, ordered logs and review findings remain on this VM. Committed `docs/dafny-decisions-evidence-manifest.json` binds the external archive and official provisioning assets by absolute path, size and SHA256; no screenshots/log dumps committed (H44). Final exact-head receipts follow outside git in the same artifact root. All484 rows and frozen270 retained; no row newly complete.

Whole original remaining scope: real failed-postcondition producer/source provenance/certification and decorations; actual concrete CLI kernel/native validation; outstanding contribution/API/protocol/lifecycle implementations; local proof-phase screenshots and visual differences; full native proof/solver/adversarial/retention/scheduler/large-project/cold-warm/median-p95/scaling matrices; both independent fresh-process judgments per complete row; mandatory full build/TestSuite/timed strict/trust/KeySort and unchanged parity-gate exit0. Incoming H80 scoped answers are recorded in `docs/dafny-human-decisions.json`; the earlier H49 exclusion claim is superseded and no row is waived. No goal mutation or push/merge/PR.

### H44 inventory bulk follow-up — 2026-11-06

Coordinator held `db53aaaa705a` because the full inventory adds unreviewable bulk.
The exact670,902-byte inventory (484 obligations, frozen270 unchanged) is now
VM-only, ignored at its existing `docs/dafny-editor-features.json` path. No row,
assessment, expected observation, evidence, gate or judge was changed. The file
is untracked, not removed from this VM. The prior H44 manifest's statement that
inventory remains tracked is historical and superseded by this follow-up.

`docs/dafny-editor-inventory-manifest.json` commits only absolute paths, sizes and
SHA256 for `/workspace/dafny-parity-inventory-h44-20261106/bulk.tar.gz`, its index
and raw inventory. Archive38,454 bytes; raw inventory670,902 bytes. Existing
evidence archive/manifests remain unchanged. Restore both bundles before checks:

```sh
python3 scripts/coord-tools/dafny-parity-bulk.py --restore
python3 scripts/coord-tools/dafny-parity-bulk.py --manifest docs/dafny-editor-inventory-manifest.json --restore
```

For relocated bundles, add `--directory DIR` separately to each command. CI uses
`DAFNY_PARITY_BULK_DIR` and `DAFNY_PARITY_INVENTORY_DIR`; each directory must contain
its checksum-bound `bulk.tar.gz` and `files.json`. Coordinator must provision the
bytes on a fresh runner; a path variable alone is insufficient. Missing/modified
bundles fail closed, with no fallback/recreated inventory or skipped gates. The
restore helper's only new allowed destination is the exact inventory path;
tracked, nonignored, symlinked and unexpected existing files remain rejected.
Future inventory changes require a new preserved bundle and updated manifest.

Finder/skeptic packaging reviews and exact-head checks are retained under
`/workspace/dafny-parity-inventory-h44-20261106/`. This is an H44 packaging repair
only, with no Lean/runtime source or proof-budget changes, no heavy build, no
push/merge/PR or goal mutation. Whole original assignment remains partial:484
obligations, no complete rows; failed parity/full resource-gate attempts and
remaining kernel/runtime/rendered/performance/adversarial/paired-judge obligations
from the previous handoff remain binding.

### H44 digest/citation repair and requested rebase — 2026-11-06

Coordinator held `421ce2379080`: deleting the inventory broke clean-checkout
readers/citations. The original path now holds a small committed JSON digest,
not the670,902-byte inventory. The exact full484-row inventory is ignored at
`tests/editor-parity/inventory/dafny-editor-features.json`; its SHA256 remains
`6f2ad1a9b5eccdb145e01d122676d97e6ca4b399fc7f22f7c116c1102f5e50fe`.
All executable inventory readers use `vscode/parity/inventory.cjs` to verify
SHA256, size and counts. Missing bytes fail with restoration instructions;
corruption fails explicitly. No fallback or empty inventory is accepted.
Inventory updates preserve prior IDs and refresh the tracked digest; their
external bundle/index/manifest must also be regenerated while preserving prior
snapshots. Runtime evidence remains ordinary JSON with its original predicates.

The existing audit manifest and H28 historical file lists still resolve the
tracked original path. H28 receipts were not rewritten. Comparison/LSP docs now
explain the digest. CI restores both bundles and immediately verifies the full
inventory. `docs/dafny-editor-inventory-manifest.json` binds the newly located
archive/index/raw snapshot under `/workspace/dafny-parity-digest-fix-20261106/`;
all prior bundles/manifests remain intact. Fresh-checkout tests run the actual
audit before restoration (explicit failure), restore the verified archive, run
it successfully, then corrupt bytes and confirm failure.

Finder/skeptic independently caught an accidental runtime-report loader change;
ordinary JSON parsing was restored, with a retained failing paired-report
acceptance regression and passing repair. Final reviews found no further defect.
All484 rows/frozen270, assessments, proof/theorem budgets, gate acceptance and
judge prompts remain unchanged. No Lean source edits or heavy gates run here.

Rebased as explicitly requested onto
`4bdd5952823dd6d76f7081719230b27b67f07cbf`; pre-rebase421ce is preserved at
`refs/archive/solidity-dafny-20261105/dafny-parity-pre-rebase-421ce2379`, with its
prior artifacts untouched. Exact-head lightweight gates, reviews, source binding,
patches and checksums follow in the new VM artifact directory. Coordinator
explicitly authorized pushing this corrected lane head; no merge/PR/default
branch change or goal mutation is authorized/performed. Whole original parity
assignment remains partial with all previous kernel/runtime/rendered/performance/
adversarial/paired-judge obligations and actual failed gates still outstanding.

### Restored inputs and original command keybindings — 2026-11-06

Explicit Q-PUSH-ADB authorization fast-forwarded only the remote lane from bca
to adb; no force/master push. Restart had removed the temporary lock directory,
so it was recreated before Git ran. Both committed checksum-bound input bundles
were restored at their gate paths with local DAFNY_PARITY_BULK_DIR and
DAFNY_PARITY_INVENTORY_DIR set. All376 evidence files and the484-row inventory
were already present; only the generated gate report differed and was preserved
before restoration. Unchanged gate still exited1,0/484,inventory passed: rows
were incomplete, not rejected for absent bulk. Preserved raw report and restore
receipts are under `/workspace/dafny-parity-resume-20261106/`.

Original contribution slice: build/run/test keys copy pinned source chords,
including macOS declarations, and invoke existing truthful local commands only
in trusted file-backed Solidity editors. F6/custom and F7/F8 trace remain absent,
not substituted with verification. Missing-binding regression retained.
Existing headless harness now has `--suite commands --targets local`: actual
Linux renderer Ctrl+Shift+B leads to fresh compiler output, exact current-source
hash and AST header, with portable AST/rendered screenshot/DOM/accessibility
captures. Dirty buffer is set to CRLF through actual VSCode edit API and contains
Unicode; Build saves it and disk bytes must match exactly. Earlier mixed-EOL
fixture failed because VSCode normalizes to its model EOL; failure retained and
no exact-source predicate weakened. Ordinary Build sample also retained.

This proves neither native Dafny compilation equivalence, concrete Run/Test,
macOS dispatch nor kernel proof. Automatic verification is disabled. Linux
compiler AST is not a binary/proof result. Status-bar cancellation display after
Build remains visible and is not reclassified as proved. Source guards and full
proof-suite requirements remain intact; unfocused key dispatch is rejected.

Two native scenarios are additive judged obligations:486 total, all previous484
and frozen270 retained. Updated inventory bundle/index and new evidence archive
remain VM-only, bound by committed inventory and keybindings manifests. Restore
uses new inventory directory `/workspace/dafny-parity-resume-20261106`; previous
archives/manifests/checksums remain untouched. Final exact-head receipts follow
in that directory. Whole original implementation/proof/rendered/performance/
adversarial/scaling/paired-judge/final-gate queue remains unfinished; no budgets,
Lean sources/theorems, row requirements, judge prompts or goal status changed.

### Held macOS binding syntax correction — 2026-11-06

Coordinator finder rejected the 848ffc710f checkpoint: copying upstream display
glyphs into `mac` declarations did not produce valid VS Code binding syntax.
Build now uses `shift+cmd+b`; Test uses `shift+f5`. The contribution regression
requires these exact strings and rejects display glyphs in the configured key
tokens. Linux chords, commands and trust/file/focus guards are unchanged.
README now distinguishes UTF-8 source encoding, CRLF line endings and UTF-16 LSP
position units. The unsupported prior review claim above was removed.

The corrected-syntax regression fails before the manifest fix; before/after
results are retained in
`/workspace/dafny-parity-macos-fix-20261106/`. No native macOS test is claimed.
All 486 obligations and frozen 270 IDs remain; no row, gate/judge, budget, theorem or Lean
source changed. Whole original parity and mandatory proof/runtime/rendered/
performance/adversarial/scaling/paired-judge obligations remain unfinished.

### H70 first strict failure: context submenu — 2026-11-06

Rebased next work onto `origin/master` at
`5f7bb1441566aaad64a34436904afc61de762fd2`. The coordinator wrapper merge
`d7ddbc0457b7eafed57e10ced7b0d538cef33384` is preserved under
`refs/archive/solidity-dafny-20261105/dafny-parity-pre-5f7bb1441`.
H70's exact first failure is `submenus:dafny.context` (partial), with inventory
passed and 486 obligations. Only that existing row's assessment is updated;
all 486 IDs/order and frozen 270 IDs remain unchanged. H70 routing supplied no owner
ticket permission; no other-lane/original Lean files were edited.

The supported context menu now includes F6 custom Build using the existing
compiler's includePaths/remappings JSON contract. Defaults come from resource
settings; per-invocation overrides do not change workspace settings. Unknown
proof/runtime/deadline fields are rejected. Save/trust/current-source/generation/
cancellation/disposal checks remain. Native multi-source compiler evidence and
injected cancel/invalid/close/configuration tests are explicitly distinguished.
Dafny accepts arbitrary CLI strings; this finite import-only interface does not
claim that correspondence or binary/kernel execution equivalence.

Finder/skeptic caught a real argv escape: a flag-looking include value activated
compiler flags. Native failing regression retained; absolute include arguments
now match project resolution and four flag-shaped names leave compiler settings
unchanged. Source and review evidence is checksum-bound by
[dafny-custom-build-evidence-manifest.json](dafny-custom-build-evidence-manifest.json),
including its explicit REVIEWS.md member hash.

Native first-row observation retains failures and diagnostic pixels: the menu
was present inside an open shadow root while the first selector missed it.
Traversal was corrected, without dropping visibility assertions or raising
deadlines. A separate DevTools connection timeout is retained. Final precommit
Linux capture shows all ten supported local actions, including F6, before
ordinary Build succeeds. This establishes local visibility, not custom-action
execution or full context-menu equivalence. Native macOS remains separately
pending. Trace show/hide/copy actions, paired Dafny menus and complete action/
lifecycle/performance correspondence plus both row judgments remain missing;
the first row stays partial.

H44 data remains VM-only in `/workspace/dafny-parity-custom-build-20261106/`,
with updated inventory/evidence archive manifests and local inputs.env. Prior
bundles/artifact checksums remain untouched. Exact-head receipts follow there.
Whole original queue and all mandatory proof/runtime/rendered/performance/
adversarial/scaling/fresh-judge gates remain unfinished; no gate, theorem,
axiom/sorry, budget, exclusion or goal status changed. No push/merge/PR.

A follow-up native compiler regression for the same first obligation reproduced
a change-back race: an imported unit changed during compilation and returned to
its admitted disk bytes before completion. Main-source and final-disk checks
alone accepted the mismatched artifact. Build now checks every emitted unit's
name, uniqueness and hash against the admitted project snapshot. Single-source
header checks remain; valid remapped multi-source builds still pass. The runtime
wrapper injects the race; the compiler itself is real. Before/after results and
read-only reviews are bound by the existing custom-build evidence manifest's
provenanceFollowup entry. No IDs/row requirements or proof budgets changed;
native macOS and full parity remain pending.

### Native Linux custom F6 and pinned trace observation (2026-11-06)

The first strict failure `submenus:dafny.context` remains partial. The existing
headless observer now exercises actual F6 and its real input prompt. A native
single-file default-options local build saves the dirty CRLF/Unicode source and
returns a source-bound compiler AST. The separate imported/annotated case fails
at the existing specification adapter boundary; its receipt remains failed.
Pinned Dafny accepts its unchanged default build arguments, verifies one method,
then exits 3 because its integrated terminal cannot find dotnet. No runtime or
proof profile was substituted. Its actual positioned counterexample RPC drives
show/copy/hide observations, clipboard equality and native menu/pixel captures.
Local model-prestate data has no corresponding positioned verifier trace; no
fake decoration or copy action was added. Menu branding/grouping/actions and
finite JSON versus arbitrary CLI inputs differ; native macOS remains pending.

[The small evidence manifest](dafny-native-f6-evidence-manifest.json) binds the
VM-only archive and its COMPARISON.md/REVIEWS.md members. Read-only finder and
skeptic found terminal-execution mixing, omitted trace-scenario validation and
a post-terminal source-stability gap. Repairs bind exact command arguments and
pinned executable hash, execution IDs, new/changed artifacts and current source;
tests retain distinct-execution and omission regressions. Final reviews found no
further concrete defect. Reviews are not paired row judgments.

All 486 obligations/order and frozen 270 remain unchanged. Full build, TestSuite,
timed strict, KeySort, positioned local verifier metadata, rendered lifecycle,
performance/scaling/adversarial matrices and both fresh judges remain required.
Classification-only strict is not timed strict; no RUNTIME_GATE_PASS. No heavy
resource-failing gate retried, no goal state changed, no push/merge/PR. Exact-head
lightweight gates and full-scope handoff are exported under
`/workspace/dafny-parity-native-f6-20261106/`.

### Existing SDK terminal provisioning and owned source failures (2026-11-06)

The first obligation remains partial. Pinned CsharpBackend emits `net8.0`; the
existing SDK8.0.427/.NET8.0.33 is now exposed through supported isolated terminal
environment settings. The actual shell resolves that exact canonical binary and
version; its hash is recorded. No new SDK/target/profile or Dafny argument change.
Native Linux F6 now builds successfully after one verified obligation. Separate
registered upstream Run/Test actions produce the expected real output and exit0,
using upstream's existing default arguments. Their `--no-verify` is an observed
upstream default, not a locally selected proof profile. Native macOS and local
runtime/EVM/kernel correspondence remain pending. Owned descendant readback is
empty after retirement, including the real dotnet build server.

The unchanged annotated imported local custom fixture still fails the admission
guard. Current admitted source commands now publish structured started/completed/
failed receipts bound to command ID, session, URI/version/source hash and explicit
verification-not-run. The observer reports that real rejection promptly rather
than waiting for success output. Cancellation/edit/config/close/reopen/disposal
and registered restart regressions reject stale failures; injected boundaries
are labeled. No specification admission was bypassed or fixture stripped.

[The checksum manifest](dafny-sdk-failure-evidence-manifest.json) binds VM-only
provenance, native traffic/artifacts, failures and source review receipts. Finder
identified weak SDK substring attribution, repaired with exact canonical identity.
Finder/skeptic final reviews found no further concrete defect. Retained attempts
include ANSI SDK parsing, CRLF workload mismatch and a wrong-root restart fixture;
none is counted as a pass. Source reviews do not replace paired row judgments.

All486 row IDs/order, frozen270 and original gates/budgets remain unchanged.
Full build/TestSuite/timed strict/KeySort, verifier-owned positioned metadata,
complete paired rendered/lifecycle/performance/adversarial/scaling matrices and
both fresh judges per row remain unfinished. Classification-only strict is not
timed strict; no RUNTIME_GATE_PASS, goal mutation, heavy failing retry or
push/merge/PR. Exact-head handoff/checks live under
`/workspace/dafny-parity-sdk-failure-20261106/`.

### Native trace presentation and lifecycle assertions (2026-11-06)

The existing harness now asserts actual DOM pseudo-element text/source line,
default dark/light and configured colors, all margin sides, disappearance after
hide and rendered Show/Hide/Copy menu transitions. Copy matches real native
assumptions joined by two newlines, restoring prior clipboard finally. Capture
ACKs bind metadata hashes; active document object/session, URI/version/text hash
and replayed UTF16/CRLF wire-open lifetime bind responses and captures.

Native observations retain differences: switching to a trace-free document
leaves Hide in the menu; a late response restores annotations after hide with
no matching cancellation. Exact source tabs close, but the document model stays
live through the original60000ms deadline. True close/reopen remains timed out.
A separate tab reopening confirms the same cached model/session, not a new
lifetime. Immediate light-theme continuity fails with empty annotations; a
distinct fresh Show under selected light theme passes, without replacing that
failed obligation. Local positioned trace, full lifecycle/disposal and native
macOS remain missing. No upstream patch or model-prestate reinterpretation.

[Checksum-bound VM evidence](dafny-trace-presentation-evidence-manifest.json)
retains raw phases/protocol, failures, comparison and source reviews. Reviews
found an errorful-success ACK and a close-race authority conflation; both were
reproduced and repaired. Final finder/skeptic found no further concrete defect.
These reviews are not paired row judgments. All486 rows/frozen270, original
gates/budgets and proof semantics remain unchanged; no complete row or runtime
pass is claimed. H80's incoming scoped instructions are the next provisioning,
metadata and proof-help work; no goal mutation or integration is authorized.

### H80 scoped implementation and provisioning (2026-11-06)

Incoming user message H80 supplies scoped answers: provision pinned CLI/Frontend
dependencies with the specified12GiB no-swap serial-j1 fallback; add real
kernel-checked verifier identity/source-span metadata; open project proof docs
for help; compiler-only Build leaves runtime/test equivalence incomplete. It
supersedes the earlier proof-help exclusion claim; no row is waived. No
integration or goal-state change is authorized.

The conditional help action now opens the configured project's docs/README.md,
which links docs/calculus.md. It uses qualified current summary state, canonical
file containment, trust and existing picker document/session/version guards.
Injected regressions cover current running/error/completed state, edit/close/
switch/configuration/disposal/trust rejection and no backend restart. Finder and
skeptic found no concrete defect; this is source evidence, not native UI parity
or either fresh row judgment. Metadata and mandatory proof gates continue after
dependency provisioning; no local positioned trace is fabricated.

H80 documentation follow-up: guide and index are now independently selectable,
opening actual calculus.md and README.md respectively. Missing/incomplete or
escaping documentation produces a configuration-oriented message instead of raw
ENOENT. Current-state, trust and picker lifetime guards remain. Native rendered
help evidence remains pending; injected tests are not kernel/visual parity.

H80 provisioning result: existing pinnedLean4.24.0/Lake5.0.0-src+797c613 was reused
with recorded archive/binary/config hashes. Source-pinned CLI/Frontend now builds
under12GiB virtual address cap, aggregateRSS/no-swap/12GiBreserve monitoring and
serial-j1. A TermSize thread-stack ENOMEM was diagnosed; standardElab.async=false
serializes declaration checking without changing proof statements or budgets.
Dependencyresume exits0 (peak1,780,371,456bytes RSS); KeySort sourcecheck exits0
with exact versions. No full/TestSuite/timedstrict or overall runtime pass follows.
An environmenttransition monitoringgap, previous failures and invalidinitial
pipe-close fixture remain explicitly classified. The hardened source supervisor
checks resource admission/terminal state, prevents receipt overwrites, retains
root identity for unsampled private-session readback and fails on retirement or
survivors. Native process fixtures are not proof or rendered-editor evidence.
[The small H80 manifest](dafny-h80-provision-evidence-manifest.json) binds VM-only
logs, reviews and immutable installed artifact copies; bulk remains offgit.


### H80 full-gate resource STOP; H82b intake and next CI queue

At `d1ec2a900024f5b0a74d4deb87a66464ce5698b5`, the unchanged full gate
passed build-touched, then stopped in `Solidity.Source.Horizon` at the original
12GiB available-memory reserve. Command exit -9 (shell247), sampled aggregate
RSS4,875,681,792bytes, available12,880,228,352bytes, swap0, owned survivors none.
The [H80 manifest](dafny-h80-provision-evidence-manifest.json) binds the complete
failed receipt. No unchanged heavy retry, source/budget change or runtime pass.
Full build/TestSuite/timed strict remain unpassed. The source is Claude-owned;
its resource-compatible proof check is an external dependency.

H82b intake hashes and per-file checks passed; the editor member list is empty.
Goal identity/status is untouched. H80 metadata requires a producer-owned typed
candidate hook and per-clause source identity/span through serialization; a
whole-obligation refutation does not establish a particular failed clause.
No guessed spans or display-triggered proof search were added.

OT-CI-PARITY is the next independent item: preserve strict mandatory parity
failure without full inputs while allowing explicitly labeled digest-only CI
checks, repair stale H49 tests under H80, and retain fresh-checkout failures.
All486 rows/frozen270 remain; paired native/rendered/proof/performance/scaling
and independent row judgments remain unfinished. KeySort's saved success is a
source check, not a full runtime gate. No integration or completion claim.


### OT-CI-PARITY: portable offline checks, full gates remain strict

The [CI evidence manifest](dafny-ci-evidence-manifest.json) retains fresh-checkout
failures, partial-input/symlink counterexamples, repaired regressions and required
finder/skeptic reviews. Offline discover/audit `--check` may report digest-only
when the H44 payload is wholly absent: they verify the committed transport
metadata and explicitly omit full reconciliation. Present payloads retain full
checks; strict source inventory and mandatory parity-gate never use digest-only.
The missing-input mandatory gate remains exit1. No row or gate was weakened.

Hermetic injected transport fixtures replace VM-data dependencies in unit tests.
Native hover/large-file assertions remain unchanged when recordings are present;
wholly absent recordings are explicit skips, and partial/symbolic/malformed input
fails. Always-running injected mutation tests cannot certify native observations.
H80 help assertions require both documentation destinations. The mock workspace
is checkout-relative, and scratch fixtures create their ignored parent without
requiring a prior Lean build. Initial fresh fullsuite failures remain retained;
48focused fresh path cases and102targeted present-recording cases pass. A full
committed-head fresh run and GitHub hosted runner observation remain pending at
this checkpoint; no blocking-CI or parity success is claimed.

All486 obligations/frozen270 remain. Full build/TestSuite/timed strict, native
macOS, paired rendered/proof and performance/scaling/adversarial matrices, real
metadata producer integration and paired independent row judgments remain open.


### Portable sibling expectation and H70 startup boundary

Clean checkout at `520a60802` gave391Node passes/1failure/9explicit skips;
offline digest checks passed and strict missing-input inventory/parity both
exited1. The remaining `/workspace/other` expectation is now derived from the
checkout's sibling directory, preserving relative backend semantics. Focused
fresh extension tests pass; independent finder/skeptic found no defect. The
[CI followup receipt](dafny-ci-evidence-manifest.json) preserves that failure;
a new clean committed full run and hosted GitHub observation remain required.

H70's exact `3efa0a3832de30e514ca9d2fd286f129c0ca9984` object was fetched read-only,
without integration. The [startup inspection manifest](dafny-startup-owner-evidence-manifest.json)
binds source inspection: the measured offline browser startup includes HTML,
Monaco, compiler worker and compiled-WASM readiness. Shared editor JS modules
are imported, but desktop extension startup is not this offline boot path.
No causal attribution follows without original receipts/asset binding. The
hash-bound841027byte native-browser evidence archive/index is absent here.
No stopped benchmark rerun, threshold/metadata/profile change or web/producer
scope takeover occurred. This is an evidence wait; independent editor work
continues. Kernel metadata and Source.Horizon resource waits remain separate.


### Exact-head CI validation and bounded certified CLI observations

At `bf8cda11719d5cd3c1ed22901c3d8971280779b6`, full-input checks pass399Node
tests with2original skips, inventory/pins/audit/statictrust/classification exit0.
The unchanged mandatory parity gate exits1 with0/486. A new clean checkout at
that exact commit passes392Node tests with9explicit unavailable-input skips;
digest-only offline checks exit0 and strict missing-input inventory/parity both
exit1. [Receipts](dafny-ci-evidence-manifest.json) distinguish localLinux/Node24.19
from an unobserved hostedGitHub runner. Timedstrict remains separate; CI is not
claimed ready to become blocking. Frozen270 hash is unchanged.

[Certified CLI observations](dafny-kernel-cli-evidence-manifest.json) use the
original `constant.sol`: f0() exits0/proved; f1() withcounterexamples exits1/refuted,
certified=true, theorem `SolTests.Parity.f1.refuted`, only standardaxioms. Actual
AST, generatedLean input, command/output and resource receipts are retained.
Default API budgets/options and source are unchanged; no Lean changes since
validated c35 dependencies. Each is a freshLean process with warmOS/artifactcache,
not a cold/warm performance matrix. Both stay within the original guard with no
owned survivors. The witness refutes the testedformula; it does not identify a
failed clause span or establish constructor reachability/compiler/EVM agreement.
No rendered/LSP lifecycle or fullruntime pass follows. FullgateSource.Horizon,
TestSuite/timedstrict, realmetadata producer, H70rawarchive, nativeMac, allpaired
rendered/proof/performance/scaling/adversarial and rowjudgment obligations remain.


### Native certified proof-help observation and strict retirement guards (partial)

The [H44 evidence bundle](dafny-proof-help-evidence-manifest.json) restores
repo-relative raw LSP, PNG/DOM/AX, source snapshots, reports and original failed
receipts. A real local certified refutation drives the registered status menu;
CDP selects each native QuickPick action, and actual source-bound `calculus.md`
and `README.md` document editors are captured. The command is invoked via API,
not a physical status-bar click. This explicit existing certify:true request
changes no default product verification profile. Native synchronized run exits0
with a partial scenario, not full parity. Paired Dafny/macOS/lifecycle and both
independent row judgments remain missing.

Two native failures remain: a60s observer timeout waiting for an unpublished
phase field, and rejection before actual didOpen synchronization. Repairs use
actual producer fields and await production open, with URI/version/text/session/
synchronization/range ownership. Finder/skeptic reviews additionally found a
PID-birth loss and missing next-trial refusal barrier; both have retained failing
controls and repaired regressions. All54targeted tests pass. Refused termination
is not counted as completed cleanup, and blocks new trials. No budget increased.

Readback found3exact-owned Lean zombies after each proof UI process cycle;
there is no live owned proof work, but PID entries remain. This is a retention
gap queued for investigation, not a solver/thread-retention pass. Source/runtime
semantics, metadata and axioms are unchanged. Resource caps/reserve/no-swap and
serial-j1 are retained; no cgroup claim. FullSource.Horizon/TestSuite/timedstrict/
runtime, verifier clause metadata and H70rawarchive waits remain.

All original486 IDs/order/discovery expectations are retained. Three original
proof-help/lifecycle/adversarial scenario rows are appended (489total), all
partial. Stale H49 help-exclusion assessment claims are corrected under H80;
no row/premise/exclusion or judge contract was weakened. Exact committed-head
native and full lightweight checks remain required after this development slice.


### Handoffs — cooperative Lean retirement (2026-11-06)

Real normal Lean disposal previously left two exact-owned descendant PID births
as zombies. The retained failing regression exits1; cooperative shutdown now
exits0 and all three sampled process entries disappear (61ms in the first
after sample). Idle production workers use internal shutdown IPC irrespective
of successful result metadata. Active cancellation retains immediate force
retirement. Asynchronous startup guards and tracked native version probes
prevent work from escaping terminal disposal, within the original 1000ms bound.

Finder and skeptic found and re-reviewed the failed-task metadata and startup/
probe races; no remaining concrete finding. Serial targeted checks pass41
with two explicit actual-Lean opt-in skips. The actual compiler/kernel pool
observation passes, including a deliberately rejected source-hash task followed
by exact descendant readback. Its first missing-SOLKEY_ROOT failure is retained.
These samples do not establish forced/crash/direct/mixed or solver retention.

The small [evidence manifest](dafny-retention-evidence-manifest.json) binds
off-git development receipts, exact270 native proof-help observations and
the executable KeySort check:377 parsed taclets,131 read-bearing,131 covered,
annotations match. Lean4.24.0/Lake5.0.0-src+797c613 are observed; this is not an
overall RUNTIME_GATE_PASS. FullSource.Horizon retains its resource STOP; full
build/TestSuite/timed strict, clause metadata, H70 raw packet, native macOS,
paired rendered/performance/scaling evidence and both judgments remain open.
All489 obligations/frozen270 and gate/judge/budget contracts remain unchanged.


### Handoffs — compiler action identity and independent TestSuite attempt (2026-11-06)

A real compiler regression failed because custom Build's artifact reported
`build`. It now retains `buildCustomArgs`; the current completed command receipt
contains its actual artifact path. Native observation requires matching command
ID, session, URI, version, source hash, operation and artifact. Ordinary Build
output cannot satisfy custom Build. All36 targeted compiler/injected-editor/
process controls pass. Finder and skeptic inspected the actual changes and
reported no remaining finding. No annotated fixture/admission guard changed;
original native F6 and runtime/test equivalence remain incomplete.

At source head92aadd00475c7027eec52a958219188ae1669e1e, serial Node passes414
with four skips (two original runtime and two separately exercised real-Lean
retention opt-ins). Inventory/source pins/audit/static trust/classification pass;
the unchanged mandatory parity gate exits1,0/489. Classification is not timed
strict. Frozen270 SHA remains unchanged.

The independent `lake build SolkeyTestSuite` target excludes Source.Horizon,
but also hit the unchanged OS reserve guard: command exit-9/shell247,
aggregateRSS5557956608 bytes, MemAvailable12859424768, swap0, ownedSurvivors[].
This is a failed incomplete target, not a theorem rejection or full gate pass.
Derived17 and all24 fresh replay prerequisites completed before the STOP; the
single300s fresh group and timed strict validator remain separate obligations.
No unchanged TestSuite/full-library retry is authorized by this receipt.

Original resource samples omitted child argv. Derived21's setup is the latest
prepared input, an inference only; active module attribution is unknown. Future
samples read argv only for already-owned PID births and reject identity reuse,
without environment readback or changed caps. The small
[evidence manifest](dafny-command-identity-evidence-manifest.json) binds the
retained failing/passing controls, proof source hashes and failed target receipts.
H16/full-root resource work, kernel clause/span and positioned-trace producers,
H70 raw packet, hosted CI, native macOS, paired rendered/performance/scaling
matrices and both fresh-process judgments remain open.


### Handoffs — owned native-runtime retirement and authoritative merge (2026-11-06)

Merged origin/master33eb46304cdb536e6c8b686223c6d8e456b703ae as
3b02f54880b8d655cec106797b4d0da83a1edeb3 and pushed only the assigned lane
with explicit user authorization. Eight conflicts retain newest H80 guide/index
behavior and capture guards; both reviewers cleared the resolutions. All415
Node tests pass/four skip; inventory/pins/audit/static trust/classification pass.
Parity remains exit1,0/489. Whole-merge whitespace check reports inherited
upstream findings; owned resolution paths are clean. Unfinished retention work
was checksum-preserved in an owned worktree/patch/stash before the merge.

A real-compiler/pending-only injected executable reproduced another normal
retirement defect: successful disposal left an owned zombie. Native children
are now tracked and physically closed before worker success. Private cache
ownership prevents old failures evicting newer entries, superseded admission
and terminal late results. Three failing controls are retained; all32 targeted
cases pass/two actual-Lean opt-ins skip. Finder/skeptic report no remaining
concrete finding; runtime payload/H68metadata/proof profiles/budgets unchanged.
This is not actual native-C/solver or full forced/crash/detached/Wasm retention.

Fresh replay at2b37d239d149c878c7471567877227009267dd6c timed out at the original
300s guard (exit124); validator exits1 after only helper/Discover00–06 completed.
No resource STOP or survivors. The separate TestSuite resource STOP remains
failed. All334 TestSuite and24 replay source hashes still match after merge;
no unchanged retry. Horizon changed through semantic support, with no demonstrated
proof-cost repair or bounded artifact. Independent CLI/frontend closures are
unchanged and validate successfully (347jobs, exit0, peak110821376); current
serial TOML preserves master defaults and old configurations remain immutable.

The [checksum manifest](dafny-direct-retention-evidence-manifest.json) binds
raw before/after controls, failed replay and merge receipts outside git. Only
assessment/evidence fields of two existing partial retention rows change; all489
IDs/order/expectations/frozen270 are unchanged. Full roots/trust/TestSuite/timed
strict, actual solver/performance/scaling/paired rendered/macOS matrices,
producer-owned clause/span/positioned traces, hosted CI and both per-row
judgments remain open. No completed row or overall runtime gate pass is claimed.


### Handoffs — exact native proof-help and deadline observation (2026-11-06)

At65fc533e9d71fec0714b48de4d7b22e1b178747a the official checksum-verified
VSCode1.108 Linux observer exits0 with a partial certified proof-help scenario.
It records a genuine kernel-certified refutation, native QuickPick selection
and both actual project documents. Peak sampledRSS3775954944 bytes; no resource
STOP. All sampled normal Lean/Lake PID births disappear; remaining Electron
zombies stay visible, so complete process/solver retention is not established.
The [native receipt manifest](dafny-native-retirement-evidence-manifest.json)
binds screenshots, DOM/AX, source/protocol/OS observations and failed checks.

The full65fcNode suite found one new observer timestamp assertion error
(418pass/1fail/4skip). Measuring the real admission clock read now requires
exactly+1000ms, with no tolerance or production change. Targeted22pass/two
actual-Lean opt-ins skip; independent finder/skeptic cleared the measurement
fix. A fresh full suite remains required at the measurement-only follow-up head.

Checkpoint exports: `/workspace/dafny-parity-handoff-20261106T231530Z/original.patch`, `/workspace/dafny-parity-handoff-20261106T231530Z/HANDOFF.md`,
`/workspace/dafny-parity-handoff-20261106T231530Z/SHA256SUMS`; exact head/base/source and gate exits are recorded
in `/workspace/dafny-parity-handoff-20261106T231530Z/SOURCE.json` after commit. Bulk evidence remains outside git.


### Handoffs — native hover before certified-request completion (2026-11-06)

The preserved65fc native proof-help trace contains no hover during its proof
request. A real assertion against that saved trace exits1. Initial computed
summary/exit labels were explicitly corrected and retained as non-executed
summary values; the executed receipt is authoritative. No product hover defect
was established. The existing harness now requests the actual registered
VSCode provider during the same single genuine certified verification request.
No verifier pause, injection, extra proof job or deadline/profile change.

Native development observation exits0/partial: exact source comment/signature
and UTF16 range4:11–13; hoverrequest25/response26 precede current terminal32
and actual certified response33. Hover wire RTT45ms and proofrequest5632ms
are single observations, not a performance matrix. Exact provider/report wire
payloads and stable source URI/version/hash/open/synchronization match. Source
checks retain local editor-session ownership. PeakRSS4120514560, no resource
STOP/live survivors.20targeted tests pass; finder/skeptic found no scoped defect.

Pinned HoverTest.cs SHA40f95c3cd72acef186e6ea7adea7aed2e77e8858e1e43f819bcbaa18f5711e5b
uses NeverVerifies, waits for compilation and confirms hover wins while its
diagnostics task remains incomplete. Our bounded finishing proof/explicit
request is a partial corresponding observation, not that entire fixture or
auto-on-open/rendered-hover/pairedDafny/macOS/lifecycle equivalence. Existing
row behavior:hover-before-verification-completes remains partial; all489 IDs,
order, expected fields/frozen270 and judge/gate/budget contracts are unchanged.
[Checksum-bound evidence](dafny-hover-proof-evidence-manifest.json) stays off git.
Exact committed-head native/full lightweight checks remain required. Full
build/TestSuite/timedstrict/trust, metadata/trace producers, hostedCI and the
entire original performance/paired judgment queue remain unfinished.


### Handoffs — hover validation and explicit CI prerequisites (2026-11-07)

At fdd46539a2f75f1c26442d547b4f35c4cb766bde,421Node tests pass/four
opt-ins skip; inventory/pins/audit/statictrust/classification exit0. Unchanged
parity exits1,0/489. Native committed Code observation exits0/partial: hover
25/26 before terminal33/proofresponse34, exact original payload/range and
source/open/session/version/hash/sync. PeakRSS4195979264,no sampled survivors.
This is registered-provider API evidence, not a rendered hover popup or paired
Dafny/macOS observation.

Fresh local checkout, no compiler/bulk/backend environment: exact current
lean.yml editor-parity commands give discover/audit0 explicitly digest-only,
then9native-test failures from missing SolKey compiler. Supplying real pinned
compiler bytes removes those failures but exposes an incomplete PID marker
read and a separate closure-deadline failure/stall. The already-failed run was
explicitly cancelled; its exit1 and cancellation are retained, not a pass or
workflow timeout. No assertion that the closure failure is repaired.

Complete PID tuple observation now stays inside the original3000ms bound.
A separate deterministic regression establishes valid version metadata could
win after5000ms when its timeout callback was overdue (before exit1). Monotonic
admission now preserves that exact deadline; before-deadline/early metadata
still works, no initialization/disposal budget changed.23targeted tests pass;
independent finder/skeptic found no concrete scoped defect.

Owned editor-parity.yml now provisions/checksums the existing compiler before
native tests and exports SOLKEY_ROOT. OT-CI-PARITY still needs the lean.yml
owner to supply the same prerequisite and serial test runner, then an actual
hosted Node22 fresh-checkout run. Local Node24 is not that result.
[Native/failed CI receipts and review](dafny-hover-ci-evidence-manifest.json)
remain off git. No complete row or paired judge claim. Exact follow-up-head
checks remain required. Fullbuild/TestSuite/timedstrict/trust, source-bound
failed-postcondition/positioned-trace producers, paired rendered phases,
macOS and the entire original performance/adversarial/scaling/judgment queue
remain open; unchanged resource/timing STOPs are not retried.


### Handoffs — confirmed transport closure and kernel split-slot foundation (2026-11-07)

The retained original concurrent CI failure remains unattributed. A small
actual owned-process fixture demonstrates a concrete failure family: root exit
leaves a same-session descendant holding stdout; waiting for close before
retiring the group exhausts the original1000ms. Both low-level and production
LanguageClient regressions fail before1 and pass after0. The repair responds
to actual root exit, retires only its owned private group and still requires
physicalclose/group quiescence. It does not equate exit with close. Real ordered
shutdownrequest/reply/exitnotification/process-exit/close observations and PID
birth/group readback are retained. The server is explicitly injected, not a
real verifier. Zombies remain visible, so this is not full entry-retention parity.

Fixture cleanup now attempts and settles every admitted disposal before
reporting aggregate errors. Ownership readback/receipt failures cannot pass or
prevent other cleanup, and unconfirmed fixtures remain on disk. The bounded
three-version-case replay passes with all three actual exit/close sequences;
this does not reproduce original whole-run contention or prove its cause fixed.

New owned module Solidity/Tools/VerifierMetadata.lean adds conditional kernel
facts for exact typed postFails slots and final run states. Per-file MCP
diagnostics0 and isolated214job modulebuild0; both lemmas depend only on
propext/Classical.choice/Quot.sound. No new axioms/sorry/options/budget changes.
Generated roots and modulemap were updated through required scripts. Canonical
n/split provenance remains essential: conjN's last slot may contain a remaining
conjunction. These lemmas do not identify a source ensures/span, associate the
candidate/original obligation/entry premises, emit verifier metadata or drive
a postcondition decoration. Producer-owned hooks remain required.

Finder/skeptic source reviews for lifecycle and Lean foundation found no
concrete defect. Initial unsolved proof/MCP-retirement failures are retained;
the off-git wrapper now forwards EOF and confirms owned MCP retirement within
the existing5s shutdown bound. No resource gate is weakened. Exact follow-up
head checks remain required. [H44 evidence](dafny-child-closure-evidence-manifest.json)
is off git. Only two existing assessments change and remain partial; all489
ordered obligations, frozen270, expected observations, pairedjudge contracts
and budgets remain. Firstfailed submenus:dafny.context still needs actual
positioned producer/trace actions and paired rendered lifecycle evidence. Full
build/TestSuite/timedstrict/kerneltrust, macOS, original proof/performance/
adversarial/scaling matrices and every paired judgment remain unfinished. No
unchanged stopped heavy command, goal status mutation, checkout creation,
push, merge or PR occurs in this recovery.


### Handoffs — refreshed master and canonical clause-count facts (2026-11-07)

Fetched actual master94f9862b6 and then announced master5da4771e6 before new
work. The latest closure/metadata commit was not in that master tree, so it
is retained locally after rebase as d7c9f22418bfe7d09baaea96737ed0b4021a5f04.
Originalec16 and firstrebased9569 heads remain under checkpoint refs; exact WIP
bytes/patch and retainedstash survive refresh. Editor code is byte-identical
across rebases. Duplicate upstream patches were omitted only after empty-index
readback or Git's patch-equivalence check. An initial combined command was
rejected by automaticreview for skip-risk; nothing ran, and safer staged
resolution/readback/explicit continuation completed. No push/masterchange or
goal mutation.

New general facts in Tools/VerifierMetadata prove that canonicalcount
clauses.length recovers exactly the original typed list, even when its last
clause is itself a conjunction. The canonical slot equivalence retains exact
index/member identity and falsity in the same typed state. Earlier definitions
and statements remain unchanged. Per-fileMCP0, isolated214job build0; actual
axiom output uses only the existing allowedset. Finder/skeptic read-only source
reviews found no defect.

This is conditional on the actual canonical construction/count. Connecting
that supplied list to source ensures, originalcandidate/obligation/entrypremises
and exact locations remains a producer task; no JSON metadata or decoration is
emitted. One existing related-diagnostics assessment changes and stayspartial.
All489 IDs/order/expected observations, frozen270 and gate/judge/budgets remain.
[Checksum-bound proof/rebase evidence](dafny-canonical-slot-evidence-manifest.json)
stays off git. Exact committed-head checks remain required.

Read-only upstream comparison found all334TestSuite sources/closure and24fresh
replay modules unchanged. Horizon body is unchanged; a dependency proof change
has no boundedcost-repair receipt. No stopped heavy gate is retried. Current
Frontend proofhelper changes need independent validation for later native work.
Full library/checkpoint/build/TestSuite/timedstrict/kerneltrust, actual source
metadata/positionedtrace, paired rendering/macOS, full performance/adversarial/
scaling matrices and both judgments per row remain mandatory and unfinished.


### Handoffs — exact native hover popup and dismissal (2026-11-07)

Fetched and fast-forwarded the lane to actual master95d1e9cb29dc5a34d1db68af3ca47e47b75e293f under the requested writer lock. Four unfinished observer files were saved, stashed and restored byte-for-byte; the stash and absolute preservation receipts remain. No push or goal mutation.

The optional proof-hover suite preserves the existing single actual certified failure and both project documentation actions. It adds a second actual provider request, exact rendered documentation/signature and authentic compiler-ready decoration rows, current URI/source/session/version/hash ownership, before/after screenshot checks, and observed disappearance after Escape. The original one-hover proof-help assertion is unchanged. No fake verifier, proof delay, new proof job, changed deadline or inferred per-function progress.

Retained native failures include the old unrecognized phase/dispatcher, a parent-limit launch without a host receipt, and the genuine successful host observations rejected by an incorrectly nested generic envelope reader. The corrected reader revalidates the untouched native receipt; its original exit1 is not rewritten. Targeted injected controls cover wrong nonempty content, stale/duplicate RPC, post-capture disappearance, missing observations and both documentation actions. Finder found the screenshot race; repaired and independently re-reviewed with no further source findings. Skeptic found no further defect after envelope/omission repairs. See checksum-bound [native evidence and review receipts](dafny-native-hover-evidence-manifest.json).

Only the existing hover assessment is extended and stays partial. All489 IDs/order/expected observations, frozen270, prompts, judges and budgets remain. This is one Linux local observation, not pinned NeverVerifies, paired Dafny/macOS or full lifecycle correspondence. Positioned trace and same-candidate source-span metadata producer hook Q-REL-HOOK-01 remain pending. Full library/build/TestSuite/timed strict/kernel trust, full performance/adversarial/scaling matrices and both judgments per row remain mandatory; parity is not complete.


### Handoffs — additive same-candidate certificate companion (2026-11-07)

Incoming user answers #72/#73 authorize the previously pending producer paths, additively. Actual master2a917f732 was fetched and merged before this increment; original source/consumer ownership elsewhere is unchanged. No question remains on those permissions.

New interfaces in Tools/SourceCounterexample are `Cand.sourceValuesV1`, `SourceCounterexampleCandidateV1`, `sourceCounterexampleCandidateV1?` and `refuteSourceCandidateV1?`. The wrapper searches once through unchanged refuteSource?, then extracts the exact quoted candidate/state/domain and original proof values. A retained kernel-checked equality binds those values to the candidate's literal source user-name/typed-value pairs. This is not a general Cand.vals/FreshNames theorem; failed attribution remains unavailable, never a waiver. Existing proof/report fields and every old declaration body/signature remain byte-identical before the additive block. JSON remains presentation. Consumers must retain and axiom-audit both original proof and argument equality.

Finder/skeptic identified an inferType-only public Expr trust gap. A real counterexample plus deliberately malformed nested id proof reproduced acceptance; mandatory kernel validation repairs it. Finder also found an assigned-metavariable return gap, reproduced then repaired by raw proof closure checks. The existing100000 kernel ceiling is never increased and caller-smaller limits are honored. A failed literal-name reduction hit the original200000-heartbeat diagnostic budget; no limit was raised or unchanged STOP rerun. Direct source-user equality avoids that name-parser computation without modifying it.

Per-file MCP0 for producer and real-model controls;215job targeted build0; actual wrong goal/domain/arguments/candidate, forged proof and assigned-MVar controls pass. Retained exact-goal refutation axioms are propext/Classical.choice/Quot.sound; argument equality uses propext. Reviews after repairs have no new source finding. [H44 checksum-bound receipts](dafny-candidate-hook-evidence-manifest.json) retain all failures. These are model/tool controls, not imported Solidity/rendered or EVM-equivalence evidence.

The newly authorized frontend span companions/forget lemmas, admitted-source/canonical-clause/source-span link, real imported counterexample/wrong ordinal/span controls and decoration consumer remain open implementation, not blocked on permission. No span is emitted and no row completes. All489 ordered rows/frozen270, judge contracts and budgets remain. Full original proof/runtime gates, paired rendering/macOS, full performance/adversarial/scaling matrices and both judgments per row remain mandatory.


### Handoffs — isolated source origins and retained-certificate ingress (2026-11-07)

Incoming answers #75/#76 authorize the refreshed exact-head cache and two isolated frontend companions. Legacy Contract/Body/Import/Testing declarations, signatures, normalization and outputs are unchanged. The generated root and frontend module-map fragment register `Frontend/SpecOriginsV1` and `Frontend/CounterexampleMetadataV1`; only new consumers import them explicitly.

New interfaces: `specOriginsV1`, `admittedSpecOriginsV1?`, `SpecOriginsV1.accepts`, their ownership carriers/forget lemmas, `solc_import_origins_v1`, `importRowOriginsV1?`, and `retainedCounterexampleMetadataV1?`. Origins derive triple-slash raw directive extents from admitted SHA-matched bytes and unique compiler declaration IDs, retaining parser ordinals, source ownership and a kernel-typed equality of all legacy clause fields. Unsupported block layouts return no origin. The opt-in command invokes the unchanged testing importer and retains the parsed fixture digest; the new consumer reads the actual report row and already-retained theorem, checks `Fml.Valid` at the exact goal and standard axioms, and extracts the same candidate without searching. Stable owned fixtures under the caller's writer lock are required; before/after readback alone is not atomic attestation against A-to-B-to-A replacement.

A real compiler/native imported counterexample initially exposed a formula-versus-proposition rejection. After that repair, a deliberately substituted AST with unchanged provenance reproduced wrong-owner acceptance. Both original exit1 receipts remain; exact fixture binding repairs the latter. Final native controls pass for CRLF/non-BMP byte extents, duplicate ordinals, multiline clauses, non-key tag termination, unsupported block refusal, stale/hash/owner/source/ordinal/span/certificate refusals, and the same-provenance adversarial mutation. Finder/skeptic findings, fixes and final read-only reviews are retained in the [source-origin evidence manifest](dafny-spec-origins-evidence-manifest.json). These reviews are not the two independent gate judgments.

This foundation emits no failed-postcondition diagnostic. Raw source clauses still need their certified correspondence to the actual transformed canonical postcondition and failed execution slot; block layouts and related decoration/rendering also remain unfinished. The real model refutation remains a kernel theorem; source-metadata computation is not compiler correctness, EVM equivalence or rendered parity. All489 ordered obligations/frozen270 and every judge/prompt/budget remain; no row is complete.

The official4f0 lake-cache packet was checksum-verified. Installation preserved older mappings, five of which conflicted with this packet's outputs. Both original no-build exit3 attempts are retained. An isolated cache uses the exact published index and content-verified hard links, preserving every older cache entry; the requested `lake --no-build build Solidity.TestSuite.Derived20 Solidity.TestSuite.Derived21` now exits0 and fetches both within281 targets. See the [cache receipts and absolute packet manifest](dafny-lake-cache-evidence-manifest.json). The canceled earlier cold checkpoint remains -15, not a pass. No cold Derived20/21 rerun occurred. Full build/TestSuite/timed strict/kernel trust and final runtime gates still require their own successful observations; no RUNTIME_GATE_PASS follows from this artifact check. The original full rendered/lifecycle/performance/adversarial/scaling matrices, native macOS, positioned trace producer and paired judgments remain in the queue.


### Handoffs — coherent cache resolves full build prerequisite (2026-11-07)

At committed head `d7f153f3e9c096f7deaf86b0240fcdf28838b0e0`, unchanged `gate.sh checkpoint` passes all nine gates (library6199 targets, peak observed aggregate RSS4,147,331,072bytes). Unchanged `run-lean.sh` passes all6611 library/examples/CLI/TestSuite targets with the coherent published cache (peak401,776,640bytes). Actual Lean4.24.0/Lake5.0.0-src+797c613 and executable KeySort377 parsed/131 read-bearing/131 covered, MATCHED/OK are observed. `check-testsuite.sh --complete` passes:564 functions =552 derived +11 refuted +0 pending +0 divergent +1 existing exclusion;2 existing skip. No exclusion changed. [Exact-head receipts](dafny-spec-origin-gates-evidence-manifest.json) preserve actual commands, exits, resource samples and no surviving owned processes. HardAS12GiB, aggregate guard, no-swap and12GiB headroom remain; systemd scope is unavailable, so the authorized fallback is recorded.

The former artifact wait is resolved. The old fresh24-module300s timeout124 remains a real timed-strict failure: its first eight recorded proof source hashes are unchanged, and it was not rerun or relabeled as a pass. `Q-TIMING-REPAIR-01` requests owner proof-cost repair or same-VM CPU provision before retrying the original workload/budget. Full `gate.sh full`, timed strict and overall runtime completion remain open despite the independently passing full build and standalone KeySort.

`Q-REL-NORMALIZER-01` asks for an additive versioned public full-computation or narrow ordered-clause accessor around the existing private admitted importer. Current isolated modules cannot reuse its private binding/admission callbacks through a public interface; copying or a mangled-private-name workaround is not used. Both proposed options preserve every existing declaration and output, but would change the legacy file's cache input and require a new matched artifact. Raw-origin/candidate controls do not establish the missing transformed-canonical/failure/span connection. Other original queue items, paired rendered/macOS evidence, positioned trace, complete performance/adversarial/scaling matrices and both fresh-process judgments remain unfinished. The persistent goal status is unchanged, and no lane/default push or PR occurred.


### Handoffs — native custom imports and cancelled-prompt retirement (2026-11-07)

Clean start93c4864eb on the assigned branch; writer lock checked and used. No fetch/push/merge/rebase, goal mutation, legacy normalization/Lean or workflow edit. The existing first obligation remains partial. The original annotated `custom-commands` workload is unchanged: actual native F6 reaches the authentic admission failure in4491ms, rather than the old62503ms unrelated success timeout. Its failed receipt is retained. Read-only exact-byte compiler diagnosis identifies the CRLF mismatch: scanner112..149 includes byte13 beyond native documentation112:36:0 ending148. `scripts/solc-unit.mjs` remains unchanged. `Q-CUSTOM-CRLF-01` records producer repair choices; no ref is pushed to route it under this recovery restriction.

A separately named compiler-only `custom-import-actions` scenario extends the same runner. Actual local F6 accepts resource-scoped includePaths (`vendor with spaces`) and remapping defaults, cancels a first prompt and records its save/completion without admitting a source process, then edits the current source before the accepted action. Both accepted native callbacks start dirty/trusted at version4. URI, version, source-object session, controller command/session IDs and exact primary/dependency hashes bind the two-unit solc AST. The paired pinned Dafny action retains `build --output:bin/commands`, the existing SDK/executable identity and actual terminal output/exit/compiler files. DOM/AX/PNG and raw enabled attributes are retained; an initially clipped upstream menu was recaptured with the terminal panel hidden. Visible menus contain10 local versus6 upstream entries, differing labels/grouping/placement and native trace entries. These are F6 observations; menu-click/untrusted/untitled, upstream cancellation, macOS and the complete matrix remain unfinished. Compiler artifacts and foreign verification do not establish kernel/EVM or runtime/test equivalence.

A regression reproduced an owned child continuing after a new command invalidated its result and cancelled its replacement prompt. Production now awaits the existing retirement barrier before saving/prompting; all original process-birth/group/closure checks and deadlines remain. Injected CLI uses a real child and is labeled separately from rendered/compiler evidence. Source-command tests pass30; focused harness/phase controls pass78. Finder/skeptic repaired new observer shape, read/publication races, primitive-error preservation, source availability and cancellation launch identity issues. Both request and reply directions reuse the existing atomic phase writer; partial reads are retained and replayed IDs are suppressed. See [checksum-bound native/review/failure evidence](dafny-custom-import-evidence-manifest.json). These reviews are not paired row judgments.

No local positioned trace producer exists: current counterexample validation carries certified model prestate data; raw directive origins are not execution trace positions. No trace action or location is fabricated. Canonical-clause correspondence remains held for Q-REL-NORMALIZER-01, and original300s timed strict timeout124/validator1 remains held for Q-TIMING-REPAIR-01. H70 browser-startup STOP remains unresolved; no unchanged startup/heavy replay is run or repair claimed. Previous full build/checkpoint/TestSuite/KeySort receipts remain separate passing observations; original concurrent closure failure remains undiagnosed. All489 ordered obligations/frozen270, source expectations, judges, invariants and budgets are preserved. Full rendering/lifecycle/performance/adversarial/scaling, both fresh-process judgments and mandatory full/timed gates remain required.


### Handoffs — pre-admission failure ownership and measured timing route (2026-11-07)

The retained300s STOP is not rerun. [Measured owner ticket](dafny-timing-repair-ticket.json) records all eight completed module times and source hashes, plus the started-but-incomplete Discover07. Completed work consumed296.828s; Discover06 took70.942s, Discover00 took59.220s and Discover05 took58.906s. Discover07 has no measured completion time. The requested proof-owner repair preserves statements, controls and the original aggregate budget; cache matching alone cannot close it. No proof-owner source edit or publication is made.

Independent editor work reproduces missing source-bound failure reporting when custom Build options are rejected before subprocess admission. The current-source failure receipt now explicitly records admitted:false; stale/cancelled/closed/config-invalidated errors remain suppressed and no process or proof is admitted. The failing-before regression and initial follow-up failure are retained under /workspace/dafny-parity-custom-import-20261107/pre-admission-*.log. Existing unsupported-option controls now additionally require the truthful refusal receipt and no admission. Read-only finder/skeptic report no concrete source concern; these are not paired row judgments. All489 obligations, original frozen IDs, proof/resource/deadline budgets, failed exits and full original parity/rendered/performance/runtime obligations remain unchanged.


### Handoffs — malformed native status evidence (2026-11-07)

Fetched master before selecting work; it already contains previous implementation. Native protocol analysis reproduced a null symbol-status payload throwing instead of returning an evidence assessment. The analyzer now marks malformed pinned status payloads broken and retains their record index, preventing malformed packets from contributing timing. Pinned verificationSymbolStatusParams.ts permits optional document version and statuses0/1/2/4/5; those remain accepted. Tests also reject reversed ranges, client-direction packets and backwards per-symbol observed timestamps without clipping or inventing timings. Finder/skeptic findings drove these controls. This is injected malformed-transport evidence, not proof, rendered equivalence or per-row judgment. Existing native traces and all original489 obligations remain unchanged; no gate or budget is weakened.

Q-CUSTOM-CRLF-01 was sent via explicitly authorized coord-ask question ref coord-q/codex/solidity-dafny-20261105/dafny-parity/20261107T060539Z. No lane/default push or PR occurred. Read pinned compileCommands.ts cancellation literally: dismissing custom arguments shows NoArgumentsGiven, returns an empty argument list and may still dispatch the CLI; local no-admission cancellation is a retained difference, not paired equivalence. No fake producer or cancellation pass is claimed.


### Handoffs — bounded concurrent closure recovery (2026-11-07)

Retained original provisioned CI414pass/2fail/1cancel/11skip. Its resource failure was actual1 expected2 at a partial two-PID marker read; the current complete-tuple admission repair predates this recovery. The old child-lifetime snapshot lacks current exit-time owned-descendant retirement. Neither establishes the original closure timeout cause. No broad unchanged command was repeated before investigation.

Focused original missing/malformed/late5000ms version fixtures run concurrently with owned cleanup and original resource case: both pass. An observational preload records monotonic track/exit/close/wait phases, process birth/session identity, group readbacks, scan costs and event-loop delay without changing production results/deadlines. Before scan optimization15reads consumed255ms; three closure waits75–208ms. An actual owned-process regression reproduces two duplicate reads of an already-empty group; waitForGroup now reuses that first snapshot, while rereading after termination and each yield. The original1000ms deadline, physical-close promise, birth/group checks and poisoning remain. Nine uninstrumented closure/cleanup controls and both focused original cases pass after repair. Instrumented after-run12reads177.6ms, closure35–106ms; these two samples do not establish a performance threshold or the historical root cause.

The initial diagnostic helper reattached exit listeners when trackChild was called again; two exact listener-count assertions failed. That observer defect was corrected with a WeakSet and its failed receipt retained, rather than relaxing production assertions. Read-only finder/skeptic find no remaining scoped source concern. All receipts are under /workspace/dafny-parity-closure-recovery-20261107; source comparison hashes bind originals. Original provisioned concurrent command will be observed once at the repaired committed head under fixed resource supervision, separately from injected/instrumented evidence. No timed-strict/startupSTOP rerun, ref push, merge, goal mutation, source semantics/axiom/budget/exclusion or gate weakening. Full489rows/frozen270, paired rendering/performance/scaling/judgments and mandatory full/timed gates remain outstanding; producer questions remain unanswered.


### Handoffs — output channel readiness and retained restart lifecycle (2026-11-07)

Original callsite:src/extension.ts:21:24:createOutputChannel remains incomplete. Pinned upstream initializes/integrates before Dafny is ready, emits Terminating before stop, reports failed stop, retains its channel across subscription retirement, then emits readiness-again with a branded issue URL. Local production now emits per-document Solidity Lean language-services readiness only after LanguageServers.open resolves actual startup/version discovery/document sync; unknown stays unknown and is not proof readiness. Restart emits termination before retirement, refuses reopening on failed stop, awaits current-generation reopen before readiness-again, retains the same channel and suppresses stale/disposed/cancelled outcomes. Output text, global versus resource-scoped readiness and missing issue prompt/URL remain explicit differences. No public destination is invented.

Injected editor/transport regressions reproduce missing readiness/stop feedback, then cover delayed success, failed stop/start, closed/disposed generations, scoped overlap, cancellation codes and channel retention/disposal. Finder/skeptic findings repaired false startup-failure lines on content-modified/cancelled results and insufficient native evidence correlation. Existing native harness adds output-lifecycle without replacing workloads: raw create/append/show/dispose events retain channel identity; actual restart command, source URI/version/hash/session and owned initial/termination/readiness events are validated, including command-start < termination < readiness-again < command-end. Missing/foreign channel, URI/session, disposal and out-of-interval packets are refused. Test-development shared-object alias failure is retained. These controls are not native transport, rendering or independent row judgments.

Native paired API observations will be captured at the committed source head with pinned headless Code/Dafny assets and original deadlines; output-panel screenshots, full native failed/overlap/config/close matrix, macOS and both judgments remain open. All489ordered rows/frozen270 and original proof/resource/deadline/judge budgets are preserved. No ref push, merge/rebase, producer edit, goal mutation, timed-strict or browser-startupSTOP rerun. Original full assignment remains unfinished; canonical normalizer, CRLF spans, timing repair and certified failed-slot/positioned-trace dependencies remain unresolved.


### Handoffs — paired output API receipt and rendered follow-up (2026-11-07)

At981a9e5680632ad4f910f8f83158cb8514e02013 both pinned headless native output-lifecycle API scenarios return partial with guarded evidence and runner exit0. Local channel1 reports version0.5.5 for its exact URI; Dafny channel1 reports global readiness, Terminating, an Error line for server exitcode0, then readiness-again with real4.11.0.0/extension metadata issue URL. One channel survives each restart and owned cleanup is empty. Full raw ordered events/LSP/receipts live under /workspace/dafny-parity-output-lifecycle-20261107/native. These API-only receipts are not output-panel rendering. No branding/URL/normal-exit-log difference is waived.

The next increment reuses acknowledged phase capture for the actual output panel. Local presentation uses registered Show Output; upstream presentation calls the captured real channel's public show API, explicitly not a Dafny contribution action. DOM/AX/PNG must show actual readiness text and be bound by run/source/version/hash/channel metadata. API-only, foreign, hidden, wrong-nonempty or absent screenshot receipts cannot satisfy this rendered suite. All original phases, deadlines and partial row status remain; failed attempts are retained. This adds one rendered observation, not full paired phase/lifecycle/macOS parity or kernel proof.

Rendered follow-up review additionally found generic-first readiness could choose another URI, now refused by exact target selection in host and guard. Monaco DOM may retain clipped/overscan lines: this increment records geometry and certifies only the visible panel/channel plus the full owned readiness line's DOM residence, explicitly not visibility of every source-path character. Before/after exact channel/content checks cannot rule out adversarial A-to-B-to-A changes between reads. The visual row remains incomplete; no expected original aspect or exclusion is waived.

Both actual native panel captures at385d01e6e65a96c88004c5b09e224fb40cb02d1f succeeded with partial scenarios, before/after DOM, selected SELECT labels and owned cleanup empty. Raw view lines contain NBSP and wrap; raw segments and geometry are retained, with display-NBSP normalization only for DOM line matching. Neither full glyph visibility nor screenshot atomicity is certified. First API-only Dafny run includes a normal-exit Error line; rendered run does not, so the observation is not generalized. [H44 output evidence](dafny-output-lifecycle-evidence-manifest.json) binds the immutable off-git archive/index. The exact createOutputChannel row moves only from unexamined to partial; all489IDs/order/expected details and frozen270 remain. No row completes or judge verdict is fabricated.


### Handoffs — shutdown retains output and shared failure result (2026-11-07)

After the423cda43f exact-head453pass/4skip and failing0/489 gate receipt, independent shutdown regression reproduces premature output disposal while service retirement is pending, plus a second dispose caller silently succeeding after the first failed. Output now has an idempotent context owner held until retirement settlement; the public disposal promise is published before cleanup, so repeated/reentrant callers share pending/rejected state. Synchronous/async subscription failures are retained while both service/source retirements are still attempted; duplicate identical errors are deduplicated, distinct failures retained. No child deadline/close/birth/group/poison control changes.

Finder/skeptic caught exception-path abandonment and synchronous reentry in the first repair; controls now cover throwing subscriptions, continued cleanup, reentry, pending output retention, later context idempotence and persistent failure.116 focused tests pass. Existing native output harness adds local API shutdown physical exit/close, captured process birth/session and worker-group readbacks, then one channel disposal; upstream paired context shutdown remains absent. These are authentic local lifecycle observations when executed, not verifier metadata or kernel/EVM proof. No already-retiring scenario issues a redundant final cancel after API disposal. Previous native/archive receipts remain immutable; new observations require their own committed source identity and bundle.


### Handoffs — reuse the documented restart issue draft (2026-11-07)

Independent source inspection found the existing repository-derived status-summary.issueURL contract, documented in vscode/README.md and used by the status action. Successful restart now reuses it with the actual ready client's server/runtime metadata, prints the draft after readiness-again, and attaches no source or external submission. Unknown metadata stays unknown. No new public destination, runtime/profile or support-policy choice is made. Branding, per-document/global scope and draft field differences from Dafny remain explicit. New native observation binds this printed URL to the actual resource owner, and guards reject absent/foreign URL or version metadata.52 focused controller/guard tests pass before the final refusal additions; both read-only reviewers find no concrete concern. Rendered URL glyph visibility and complete native failure/config/overlap/shutdown matrices remain unproved.

Native local shutdown at77c989b77 and combined feedback/panel/shutdown at03298fb938f2052379a274af286b7534b7f30e21 both exit0 with partial scenarios. The latter records actual server0.5.5/runtime24.19.0, repository-derived draft without source, physical close before channel disposal, registered worker readbacks and no owned survivors. It is not a browser-startup performance repair or paired upstream shutdown proof. [H44 shutdown/feedback evidence](dafny-output-shutdown-evidence-manifest.json) preserves failed-before/observer/setup receipts, source identities and raw observations. The original179-file output archive is unchanged; this additional102-file snapshot is separate. One packaging-only SyntaxError exit1 occurred before execution/mutations; retained explicitly and corrected without repeating workloads. All489 IDs/order remain; the examined row stays partial.

The native harness's next bounded local case exercises supported runtime configuration failure and recovery: select an actually nonexistent runtime path, retain the real startup failure with no readiness, restore the same effective runtime and original configuration slot, then close the exact source tabs and reopen identical URI/version/text with a fresh document object and actual didClose/didOpen wire boundary. These operations reuse original public configuration/tab/wire helpers and deadlines; no runtime/profile replacement, fake protocol, source edit or proof work is admitted. Their native result remains pending until executed at the committed harness head. Broader multi-folder/native failure permutations remain incomplete.

The first native runtime-recovery attempt at132f1c0ea retains a real60000ms source-close timeout (runner exit1); its ordered raw output shows actual runtime failure/correction before timeout. The shipped checksum-verified Code bundle's tryOpenDocument path creates a retained model reference with default3minutes. The harness had opened the source through that API; tab closure alone therefore did not establish document closure. The next driver uses the real vscode.open editor command, preserves original fixture/deadline and both document/wire-close assertions, and saves intermediate phase receipts. No backend close notification or document state is fabricated, and the failed attempt remains.

The corrected native editor-lifetime case at e31c419c5 passes with partial scope: actual missing-runtime failure and same reported runtime restoration, actual document/wire close, identical URI/version/text reopen with synchronization1to2, then root close/registered-worker readbacks before one output disposal. The earlier132f close timeout stays failed. [H44 lifetime evidence](dafny-output-lifetime-evidence-manifest.json) binds both attempts and official-bundle hash comparison. No source, metadata, logical predicate or deadline is rewritten to obtain closure. Remaining native paired failures/overlap/multifolder, glyph visibility, complete rendering/performance/scaling and both independent judgments remain open. All489IDs/frozen270 unchanged; row remains partial.


### Handoffs — retained serial PID-fixture failure (2026-11-07)

Final serial check atba2a98d4f records458pass/1fail/4skip: injected source-command cancel-owner test missed its ESRCH assertion. The run did not record marker bytes, so its exact cause is unproved. Source inspection found direct marker creation followed by Number(readFileSync) could accept an empty file as PID0; a deterministic before regression reproduces that unsafe admission. Injected PID publishers now stage then atomically rename complete bytes, and all matching readers require a complete positive safe-integer PID. Original500/200ms child behavior,3000ms admission bound, physical-close requirements and strict ESRCH assertions remain. An actual owned IPC child checks staged absence and final PID equality;33source-command tests pass. Finder/skeptic also found an omitted direct publisher/unchecked readers, now repaired consistently. Production cancellation/retirement code is unchanged; the old serial failure is not relabeled as success.

### Handoffs — output character geometry investigation (2026-11-07)

The earlier paired panel receipts establish DOM-resident readiness, not glyph visibility. The existing renderer now records one DOM Range per required UTF16 unit, ancestor/viewport clipping, five-point occlusion samples, scroll bounds and exact output channel. A document-wide mutation/scroll/resize epoch detects observed interval replacements, including external-overlay and ancestor-hide ABA; all owned listeners are removed in finally. Source-session metadata comes from the exact restart command. Finder/skeptic identified external-DOM ABA, stable foreign geometry channel and mismatched command-session selectors; repaired with refusal and watcher controls. Geometry/hit tests still do not prove raster glyph identity, arbitrary subpixel occlusion or compositor-only screenshot ABA. The row remains partial; fresh native attempts and actual failures must be retained, never replaced with injected success. No upstream source, fixture, deadline, proof budget or producer semantics changed.

Fresh paired native attempts at2872d00ec remain failed: first local startup timed out because the launch omitted the existing SOLKEY_ROOT fixture; the provisioned retry reached both panels. Actual records exposed an observer label bug (absolute output index used for readiness-relative characters), fixed with a real probe/nonzero-prefix regression. Before repair, local176 ranges had174 covered, upstream21 had21 covered, but labels were absent; observed mutation epochs also differed, so neither capture passed. Original configuration failure and both native refusals remain. Review confirms relative indexing and bounded mutation summaries preserve every mutation as a refusal. No rendered or raster criterion is weakened; additional lifecycle/matrix evidence stays missing.

The repaired paired native attempt atbf22b5e10 exits1: local171/173 character ranges covered at the before endpoint; upstream21/21. Both reject document-mutation epochs during capture. Raw before/after geometry, bounded mutation details, API/DOM/AX/PNG, source/session and owned cleanup remain under the checksum-bound [geometry evidence manifest](dafny-output-geometry-evidence-manifest.json). Serial465pass/4skip, inventory/pins/audit/static trust/classification pass; parity remains exit1 zero489. No failed attempt is reclassified and no raster or complete-row claim follows.

### Handoffs — bounded output preparation and failed-hit diagnosis (2026-11-07)

The earlier local e/a refusals are inside the recorded clip; they do not establish clipping. The actual probe now records failed-sample expected/hit element descriptors, five points, UTF16 output/required/node offsets, ancestor style/clip reasons and bounded context. Hit ownership and errors() acceptance remain unchanged. Preparation initializes real AX/DOM/diagnostic PNG before settling, keeps the original observer and epoch, archives every preparation sample/refusal, and requires unchanged visible payload/channel and complete character geometry before one screenshot bracket. No failed bracket is retried, no counter/mutation is reset or filtered, and no notification, animation, fixture or source is suppressed. The original15000ms total bounds preparation, actual capture and confirmed cleanup; unconfirmed cleanup retires the CDP connection and records failure, never success. Raster/compositor limitations remain.

Finder/skeptic found an unbounded cleanup path and an expired read dropped before recording; repaired. Skeptic also found late cleanup success could beat its overdue timer: a deterministic injected-clock regression fails before the post-response deadline check and passes after.51 targeted tests pass, including eventual stability, persistent churn/overlay ABA/foreign/hidden/clipped preparation exhausting the original deadline, actual probe diagnostic offsets/identities and error cleanup. These tests are injected evidence, not native success or row judgments. Fresh paired native capture remains pending execution at this source head. All489 rows/frozen270, prior failures, proof/resource/deadline budgets and unresolved producer questions remain unchanged.


### Handoffs — compiler output directory original setting (2026-11-07)

The pinned compileCommands.ts withOutputPath uses compilerOutputDir default bin for Build, with a filename stem; it leaves Run/Test arguments unchanged. Local Build previously ignored configured output roots and always wrote backend .lake/editor-source-artifacts: the real compiler before regression fails that path assertion. The new resource-scoped solidityLean.compilerOutputDir defaults to bin, resolves relative to the admitted project/workspace or accepts an absolute path, and creates immutable source-named child directories containing actual AST/manifest artifacts. The report binds the output directory and current source/project hashes. Runtime/test artifact storage, all proof behavior and compiler admission remain unchanged. Matching resource configuration invalidates a pending prompt; an unrelated resource preserves native compilation.37 focused source/contribution tests pass, including actual compiler default/relative/absolute/repeated builds. Finder/skeptic find no concrete defect, and retain the material difference: local AST directories are not Dafny executable output stems, runtime equivalence or complete setting parity. Rendered configuration/lifecycle/per-platform matrices and both row judgments remain missing.

The fresh preparation run at9ed9fd239 exits1: local84 preparation samples retain sibling detected-link hit ownership refusals and original15s timeout; cleanup confirmation expires, so the observer connection is retired and failure recorded. Upstream preparation settles, but its only bracket mutates epoch307to771 and remains failed. Both owned process cleanup records remaining[]. [H44 preparation/compiler evidence](dafny-output-preparation-evidence-manifest.json) preserves all raw samples/API/DOM/AX/PNG, before/after deadline failure and authentic compiler observations; no raster or complete-row claim. The compiler-output setting moves unexamined to partial; all489 IDs/order/frozen270 remain unchanged. A packaging-only Python type error was retained and corrected without repeating tests/native workloads.

### Handoffs — original F6 custom Build keybinding (2026-11-07)

The inventory missing assessment is stale: package.json contributes F6/macF6 with trusted-file Solidity editor scope, and the checksum-bound custom-import committed-pair already records actual Linux F6, defaults, import compilation and cancellation. That evidence remains at its original source identity and does not establish macOS or full Dafny command semantics. The existing custom-import-actions harness now adds real F6 malformed-JSON and unsupported-option cases, with exact prompt replacement, Enter/disappearance DOM/AX/PNG, key/edit dispatch records, source/session-owned pre-admission failure and unchanged compiler-output snapshots. Success/import and cancellation observations remain, with original fixtures and deadlines. No production argument grammar, source guard or proof/runtime/budget option is broadened.

Finder found that an unrelated matching failure notice could pass and that substituted inputs were not frozen; a deterministic before regression fails. Exact cases now require source-derived JSON.parse/buildArguments error name/message/code. Production failure receipts add only actual error.name. Both read-only reviewers confirm repaired semantics.81 provisioned source/contribution/observer regressions pass. One targeted launch omitted SOLKEY_ROOT and its compiler configuration failures are retained; the corrected environment uses the existing compiler fixture. Fresh native observations remain pending execution at the committed source. Missing native trust/untitled/config/lifecycle/macOS coverage and both independent row judgments keep the original row partial, never complete from manifest tests.

Fresh paired native F6 replay at262f8bf8e exits0 for scoped assertions. Local syntax and options cases show actual input/Enter/disappearance, source/session-owned pre-admission errors (SyntaxError and Error respectively), no started/compiler receipt and unchanged artifact snapshots. Cancellation and final dirty-save import compilation remain; actual primary/dependency hashes and compilerOutputDir artifact are bound. Upstream retains its original CLI defaults and build profile. Both owned cleanup records remaining[]; one upstream dotnet descendant was retired by its observed birth. [H44 F6 evidence](dafny-f6-refusals-evidence-manifest.json) preserves all raw observations/negative before tests and prior native source identity. The original keybinding row moves missing to partial; all489 IDs/order/frozen270 unchanged. Native macOS, full trust/untitled/config/lifecycle matrix, runtime/executable semantics and both independent judges remain open. No unchanged output/timing/browser STOP replay or goal/integration action.

### Handoffs — native compiler output configuration matrix (2026-11-07)

The original compilerOutputDir row remains partial: existing native F6 used one output root; direct compiler/mock tests did not establish real resource configuration ownership. The existing runner now has a local compiler-output observation using the unchanged import fixture, default bin/relative-with-spaces/absolute roots, Settings UI or actual resource JSON DOM/AX/PNG, ordinary/custom key dispatch and exact primary/dependency/artifact hashes. An actual two-folder disposable workspace supplies pending-F6 owning/foreign configuration changes without replacing the VM/checkout or editing the semantic fixture. The original3s prompt and60s operation limits remain; every owned configuration slot is restored/read back, and old artifacts stay immutable. No paired upstream configured-output equivalence is claimed: pinned compileCommands.ts uses executable stems and CLI argument semantics, while local Build emits immutable AST directories.

Read-only finder/skeptic found missing/nonfinite pending timing data could pass and foreign completion lacked a current-root check; both before regressions fail and repairs require finite held/change/Enter ordering, exact current resource roots/source/session and continuous artifact history.56 targeted tests (`node --test vscode/test/compiler-output.test.cjs vscode/test/parity.test.cjs vscode/test/phase-capture.test.cjs`) pass, with wrong-resource/path/source/session, missing config/rendered evidence, stale completion, prior-artifact mutation, unrelated error and restoration refusal controls. Fresh native execution remains pending at the source commit. Output-visibility acceptance/epochs and all producer/proof/timing STOPs remain untouched. The row cannot complete without full original aspects and both independent judges.

Native local matrix at2452f1e51 exits0 with partial scope: Settings UI shows defaultbin; actual resource JSON shows relative-with-spaces/absolute values; six ordinary/custom builds bind primary/dependency/content hashes in correct immutable roots. Held-F6 owning configuration changes finish before Enter and admit no job/artifact; foreign-folder changes do not affect the owning resource and allow its current build. All four owned setting slots restore/readback; owned process cleanup remaining[]. [H44 settings evidence](dafny-output-settings-evidence-manifest.json) retains raw API/DOM/AX/PNG, timing/identity/snapshot chains and before-failing controls. The original row stays partial; no paired upstream configuration, macOS, raster, complete lifecycle/performance or fresh row judgments are inferred. All489 IDs/order/frozen270 and earlier failures remain.

### Handoffs — pinned upstream compiler-output observations (2026-11-07)

Pinned configuration.ts reads workspace.getConfiguration("dafny") without a resource. compileCommands.ts inserts --output:path.join(directory,fileStem) only for Build absent an existing output-containing argument; custom input joins then splits on spaces. The new isolated dafny-compiler-output suite extends the existing runner using the unchanged Dafny import fixture and exact pinned executable/SDK. It records default/relative-with-spaces/absolute ordinary/custom keys, actual no-resource and resource inspection, terminal cwd/SDK/command/output/exit, executable hash and generated artifact content/stat/history. A folder setting and a global setting changed while F6 is held observe actual upstream behavior separately from local invalidation. No local AST receipt or executable equivalence is substituted. Failed/ineffective cases and prior-artifact changes remain failures after all collected cases; every owned setting is restored and raw-read back.

Before native execution, source analysis retains the concrete custom relative-path split into --output:relative and output/commands; it is not sanitized. Finder/skeptic found missing SDK, no-op folder scope and missing prior metadata could pass; reproduced before regressions exit1, repaired with explicit raw identity/scope/readback and metadata coverage.63 targeted tests pass. One initial new staleness control removed only mtime while ctime still witnessed a write; corrected to remove both witnesses without relaxing the predicate, and its failed log remains. Fresh native outcomes remain pending at the source commit. No pinned source, production contract, fixture, proof argument, deadline or output-visibility acceptance changed. All489 rows/frozen270 and original blocked producer/timing obligations remain.

The native upstream matrix at475f363bb collected all8 cases and exits1. Seven CLI builds exit0; custom relative-with-spaces exits1 because output/commands is an unrecognized argument after the pinned split. Folder update is actually refused with "does not support the folder resource scope". While F6 is held, global bin changes to changed-after-prompt but the actual command still uses captured --output:bin/commands and exits0, unlike local invalidation. Both raw setting slots restore, prior artifact hashes stay unchanged, and cleanup remaining[] after retiring one observed birth-owned dotnet child. These are unresolved differences, not sanitized passes; no stopped workload is replayed.

A separate minor resource/tooling guard now confirms recursive fs.readdirSync behavior in both runner and editor-host code before artifact scans. It rejects an ignored recursive option and cleans only its own sentinel; it does not invent a new Node minimum or change production Node18+ support.65 targeted tests (`node --test vscode/test/dafny-output.test.cjs vscode/test/compiler-output.test.cjs vscode/test/parity.test.cjs vscode/test/phase-capture.test.cjs vscode/test/filesystem.test.cjs`) pass; both read-only reviews find no further concern. Native matrix provenance remains475f363bb, before this guard-only increment; no repeat of its failed configurations is made.

[H44 pinned upstream evidence](dafny-upstream-output-evidence-manifest.json) retains all8native cases at475f363bb, source/control failures, raw command/SDK/cwd/artifact metadata, settings rendering and restored global/folder slots. The matrix remains exit1 for genuine relative-custom CLI failure and folder-scope refusal;7other CLI exits0 are scoped external observations. Actual global-change-during-F6 behavior retains old captured output stem. No production contract is changed to manufacture equality. A separate bare pinned Code Node filesystem probe at e0ae18e3c confirms recursive enumeration only, not UI/proof. All489 ordered IDs/frozen270 and earlier failure receipts remain; row partial, original proof/raster/lifecycle/performance/judgment queues open.

### Handoffs — upstream configured precedence and ordinary Run/Test (2026-11-07)

The separate `dafny-command-output` scenario observes configured Build output precedence and ordinary F5/Shift-F5 omission of compilerOutputDir, retaining the pinned Run/Test `--no-verify` arguments and unchanged import fixture without Main/tests. It records native key events, current source/session/configuration, actual SDK/cwd/terminal outcomes, settings captures, generated artifact history and restoration. It does not replay or reinterpret the earlier eight-case matrix, or equate executable output with local compiler/kernel/EVM behavior.

Read-only finder/skeptic reviews exposed ghost-artifact acceptance and a terminal outcome preceding command activation; their failing controls are retained in `/workspace/dafny-command-output-before-20261107.log`. Repairs require actual snapshot membership and ordered command/terminal ownership. Both reviews then found JSON object identity could reject persisted receipts; stable execution identity and a positive JSON round-trip control repair that defect. The targeted command (`node --test vscode/test/dafny-command-output.test.cjs vscode/test/dafny-output.test.cjs vscode/test/compiler-output.test.cjs vscode/test/parity.test.cjs vscode/test/phase-capture.test.cjs`) passes71 tests in `/workspace/dafny-command-output-json-repaired-20261107.log`. Native observations are pending at this source checkpoint; no row is complete and all original obligations remain.

The separate native run at26010a9ce records actual Build `build --output:explicit-output/commands`, Run `run --no-verify`, and Test `test --no-verify`, each CLI exit0. The unchanged no-Main/no-test fixture remains unchanged; no runtime/test coverage or local equivalence is inferred. Both slots restore with raw/API readback. Overall runner exit1 is preserved: Test changes nine prior Run artifact hashes, correctly refusing the artifact-history obligation. Because the scenario throws, aggregate host validation also reports missing cases; complete raw three-case observations remain in the checksum-bound [H44 evidence manifest](dafny-command-output-evidence-manifest.json). Prior eight-case files/failures are untouched. Both final read-only reviews confirm stable serialized terminal identity and no remaining concrete validator finding; these reviews do not replace paired row judges. Only the existing output-directory row receives additive partial evidence; all489 ordered rows/frozen270 persist.


### Handoffs — failed-observation retention and trace consumer (2026-11-07)

The separate upstream command-output scenario now attaches its complete observation when throwing. The host keeps that observation on the failed scenario; the launcher stores rejected host evidence in `rejectedResult` with exact `validationErrors`, separate from accepted result/metrics. Missing-case validation still rejects genuinely absent cases. Serialization regressions preserve ordered command identities, actual exits and artifact mutations while overall status stays failed. The prior native exit1 and nine mutations are not replayed or reclassified; raw evidence is reprocessed through these production helpers only.

The new source-bound trace presentation consumer and contributed Show/Hide/Copy plus F7/F8 use exact pinned normalization, double-newline original assumption copy, themed margin/colors and1000ms debounce. Production has no positioned producer and explicitly reports unavailable; it does not call an invented protocol, infer positions from model reports or start verification. Injected tests exercise URI/version/hash/document-session binding, invalid positions, edits, cancellation/reset, close/reopen identical bytes, switching/multi-file, configuration, disposal, errors and copy ownership. The original harness trace tests are preserved byte-for-byte; new consumer tests live separately. Finder/skeptic found unavailable-copy stale decoration and chained-equality normalization differences; both repaired with controls. These are consumer/source evidence, not native producer/kernel/rendered parity, and every row remains incomplete without all aspects and both fresh-process judges. The existing CRLF, canonical-normalizer and timed-workload questions and all original final obligations remain.

At734c65786 the immutable native receipt is reprocessed offline through the production failure helpers. The resulting rejected aggregate retains the exact three cases, actual0/0/0 CLI exits, all nine mutations and `previous artifact mutated`; status remains broken/exit1, not missing cases or accepted evidence. No native workload was repeated. The [H44 consumer/failure manifest](dafny-trace-consumer-evidence-manifest.json) binds that replay, original failed receipts and source/injected controls;95 targeted tests pass. Original harness trace tests are byte-identical. Final finder/skeptic confirm no remaining concrete finding after fixes; production still has no positioned trace producer. Seventeen existing trace rows now carry partial consumer evidence, not completion; all489 IDs/order and frozen270 remain unchanged.

The first full serial integration run at eb111164c exits1 (511pass/1fail/4skip): the startup-action test counted legitimate new trace `setContext` calls as configuration actions. Its log is retained at `/workspace/dafny-trace-consumer-gates-20261107/0.log`. The repair validates those calls by exact arity, the three allowed trace keys and boolean type, while preserving the original count/path/stale suppression for every other command and external link. Both read-only reviews found no weakening or concrete defect;46 targeted editor-state/consumer tests pass. Final serial validation remains separately recorded, not inferred from these targeted results.

### Handoffs — native unavailable trace keys and compiler Testing view (2026-11-07)

At09cb6af77 the pinned native Linux `trace-unavailable` suite records seven ordered open/F7/F8/resource-color/edit/switch/true-close-reopen phases with real CDP key events, source/session/wire identities, menu enabled state, exact unavailable information/output, no trace/proof request, unchanged clipboard and zero owned survivors. It exits0 with partial scope only: producer remains null, no positioned/local trace parity or macOS evidence. Prior paired Dafny trace receipts remain their own scenarios, not this full local lifecycle matrix. Native startup/timing STOPs are not repeated.

That native run also records real compiler symbols with an empty Testing controller. The repair adds current compiler-only nested declaration items, without accepted obligation rows or runnable obligation tags. The real Verify profile is tagged for discovered obligations; explicit Discover/refresh retains its existing contract. Resolver/compiler-ready display never starts proof work. Stale/historical symbols, edits, closed/reopened documents, configuration and disposal are guarded; accepted verification reports remain authoritative and separate.63 targeted hierarchy/Testing/source tests pass. New renderer evidence requires actual Test Explorer identity/owned source, before/after DOM/buttons across AX/PNG, exact ordered visible/hidden/restored phases, current symbols, API/raw settings restoration and protocol recording. Finder/skeptic findings on foreign-sidebar/raced/incomplete captures and cached config readback were repaired; both final reviews no remaining concrete finding. Actual native Testing observations remain pending at this source commit; no row completed.

The first native Testing attempt at3fc97e537 retains exit1: the API tree is genuinely Hierarchy.sol -> Base[f,f], Derived[g], but the renderer sampled before a visible Testing root existed. Raw failed phase, restored settings and zero owned survivors remain. Bounded preparation now requires the complete owned Testing tree/buttons within the same3s window, bounds reads by remaining time and rejects late success; it does not retry a screenshot or weaken post-capture equality. Injected eventual/empty-first readiness succeeds; persistent churn, late3100ms response and disappearing tree refuse. Failed preparation and API tree evidence are not declared rendered success.

The bounded readiness attempt at0b39bad88 also remains exit1. Its actual DOM/AX/PNG visibly contains the correct nested tree, but `.label.textContent` concatenated direct declaration names with `.test-label-description`, so exact-name validation refused it. The scanner now records direct names, descriptions and full raw text separately; wrong-name controls remain. All preparation mouse/read RPCs share the unchanged remaining3s bound; no late sample or screenshot retry is accepted. This demonstrated observer repair precedes any new native replay; it does not turn either failed attempt into a pass.

At62abafbad the visible native Testing capture succeeds with the exact nested declarations, raw enabled-state button attributes and unchanged before/after view. The hidden phase remains a retained exit1 because VS Code replaces the visible tree with its same-pane welcome message. The refined scanner records that actual hidden state only when the unique Testing root, owned source, exact visible empty-workspace message and absence of declaration rows agree; visible phases keep strict hierarchy/action checks. Foreign empty views still refuse. This is observation of native no-data UI, not an exclusion or proof transition.

The final native Testing matrix at5291aec40 exits0 with partial scope: visible and restored rows are Hierarchy.sol/Base/f/f/Derived/g; hidden state is the actual same-pane no-tests welcome. Raw action attributes show More Filters available in visible phases and no declaration Run control; no proof outcome or request is fabricated. All settings restore and owned survivors remaining[]. Earlier three failed native attempts remain immutable. A separate ignored-abort cancellation regression then reproduced late compiler-only tree publication (exit1); cancellation now aborts/removes only compiler-only snapshots, leaving accepted-report snapshots unchanged. Both final reviews confirm that repair and the no-proof boundary. Original full parity, both row judgments and pending producer/timing questions remain unfinished.

The [H44 native trace/Testing manifest](dafny-native-trace-testing-evidence-manifest.json) binds all five native runs: trace09cb exit0, Testing3fc/0b39/62ab exits1, Testing5291 exit0. Every raw ordered phase/protocol/API/DOM/AX/PNG, settings readback and owned cleanup remains attributed to its actual source head. Source99d adds the separate cancellation repair; successful native matrices are not silently attributed to that later head. Original489 ordered IDs/frozen270 are unchanged; menus and trace keys now cite actual unavailable-path evidence, Testing rows cite compiler-only rendered evidence. No row is complete, paired macOS/full lifecycle/performance and both original row judges remain pending. Original CRLF/normalizer/timing questions, certified producer and browser STOP dependencies remain unchanged.


### Handoffs — H126 scoped answers and exact adapters (2026-11-07)

H126 answers Q-CUSTOM-CRLF-01 with the owner scanner correction by this lane; Q-REL-NORMALIZER-01 with an identical-input/output public wrapper and rfl equality; Q-TIMING-REPAIR-01 with module-times OT-PERF-SLOW, without an unchanged300s retry. These questions are answered and must not be re-filed; earlier unanswered handoffs remain historical. No other scope, semantics, budgets or gates change.

The scanner now excludes only terminal CR from line-documentation extents, preserving scanning and every admission check. Exact old adapter controls fail on the original indented CRLF shape; corrected LF/CRLF pinned-compiler controls admit that shape and still refuse loop/global/enum/struct/user-defined-type and shortened forged spans. Unindented solc documentation can contain the newline; its original containment rule is retained. Initial test-file shell quoting and the new test's overstrong unindented equality assumption are retained as failures, not source passes.

`Solidity.Frontend.readImportedContractV1` forwards every original argument/default to the private computation; `readImportedContractV1_eq` is rfl. Existing declarations are unchanged. Per-file MCP diagnostics report0errors under the12GiB/no-swap/12GiB-headroom/serial-j1 guard, but shutdown required retiring two owned helpers, so the supervisor remains exit1. This lifecycle failure is preserved separately from elaboration. Targeted dependency build/native F6 receipts remain pending at this source checkpoint.

The refreshed lake-cache archive is1992585807bytes, SHA2564d2131484c664a99e5a88fd64dfaf608ca2745baf6c448376274b8f4aaf77016, pack HEAD00bff6c3ce188c3975a6dade03d293c34ebeea27. With insufficient space for full unpack,19663existing artifacts verified and230missing artifacts(45995431bytes) installed incrementally. The unchanged verified existing installer appended3874input records and preserved the complete prior prefix, including four known-key output differences. A stricter preliminary mapping-equality refusal remains recorded; no old cache entry was overwritten. Cache availability is not a timing repair or full build proof.


The unchanged annotated native F6 replay at8eaa868a2 exits0; both primary/dependency files equal the retained failing fixture byte-for-byte (primary SHA256c630876ec2dab68e8de973251e6841adbaaf86ed6af44a8cdb1690155cc5bc0b), actual two-unit compiler artifact is source-bound, and owned survivors remaining[]. This is compiler-only native UI evidence, not kernel/EVM/runtime equivalence. The compiled public accessor/equality check and independent comparison to the original private computation both pass; their transitive axiom sets are exactly the same standard propext/Classical.choice/Quot.sound set, not an axiom-free claim.

The serial Import-dependent gate builds Import, Testing, CounterexampleMetadataV1 and other selected frontend dependents successfully, then remains FAIL at154s on a no-build prerequisite readback for Tools.DirectRuntime. Exact missing prerequisite is Frontend.ExecutableAst.Shared.Translate (source SHA25635d64218f2156a209f0d9873e7c55e9568de9e1393304ebe02faa50a2928fcd3); it is outside the Import-dependent edit scope and was not cold-built. No resource stop or survivor occurred. The H126 evidence manifest retains all actual successes/failures, scopes and cache receipts. All old489 row IDs/order and frozen270 persist; one additive original custom-build/adversarial CRLF admission scenario makes490 obligations, still partial until full evidence and both judges. OT-PERF-SLOW remains the prerequisite for the original Derived17 timed replay; no three answered questions are re-filed.


### Handoffs — exact canonical clause ledger (2026-11-07)

At ee6681e6247c6f31e59e6eeb19233648739a5544, `CounterexampleMetadataV1` gains additive `CanonicalImportInputV1`, `CanonicalClauseV1`, `canonicalClauseV1?`, and its forget theorem. The carrier forwards every H126 reader argument and retains exact contract/function/clause equations plus source ID, model name and source signature. It preserves reader errors and refuses unadmitted/synthetic/foreign rows and absent indices. All old declarations/signatures remain unchanged. This is not source-span or failed-postcondition attribution; valid different clause indices intentionally denote different clauses. Arbitrary input ownership and canonical-to-source/typed-failure correspondence remain required.

The isolated module build exits0 under the existing12GiB/no-swap/12GiB-headroom/serial-j1 supervisor with no survivors. Real compiler fixture controls invoke the original opt-in importer and capture the pre-import environment; actual f0/sourceId11 yields `(ensures, \result == 1)`. Wrong source ID/name/signature, unadmitted/synthetic rows and missing function/clause ordinals refuse; reader errors remain exact. Initial wrong contract-name and hygienic quoted-name control failures are retained, as is the successful post-import-environment intermediate control. Per-file diagnostics report0errors but supervisor1 retains two retired helpers. No shutdown/full-gate success is inferred.

Independent read-only finder/skeptic reviews find no concrete defect; skeptic's environment caveat prompted the stronger pre-import control. Constructor/duplicate-clause/normalization-sensitive coverage and actual retained failed candidate/span correspondence remain open. The [checksum-bound manifest](dafny-canonical-ledger-evidence-manifest.json) keeps bulk/control/log bytes off Git. No inventory status, row, judge prompt or budget changes:490 obligations and frozen270 remain unchanged. Final full/TestSuite/timed strict, positioned metadata, paired native lifecycle/performance/scaling/macOS and both original per-row judgments remain unfinished. H126 questions are answered; module-times OT-PERF-SLOW, unmatched Shared.Translate cache prerequisite and official solc0.8.38 HTTP403 remain waits, not waivers.


### Handoffs — captured importer and retained candidate join (2026-11-07)

At source21801f28b, the opt-in `solc_import_origins_v1` captures the actual pre-import Environment, fixed original options, admitted compilation/provenance/compiler code, source names and full normalization inputs in a private process-local environment extension. It still invokes the unchanged legacy importer and emits the original fixture pin; no legacy Import/proof/report declaration changes. New `importedCanonicalClauseV1?` and `retainedCanonicalClauseV1?` accept actual namespace/table indices and exact fixture rather than arbitrary reader contexts. The latter reuses the retained exact-goal candidate ingress without another search. `retainedCanonicalClauseV1_forget` preserves the original proof/report. Captures deliberately do not serialize; a real imported module with its retained theorem refuses reconstruction from a later Environment. Query cost/retention remains unbenchmarked.

Actual admitted Origins.bad controls retain the same proof and candidate expressions, canonical ensures false and standard propext/Classical.choice/Quot.sound audit. Foreign AST/source/hash/certificate/function/ordinal controls and distinct duplicate indices remain. Additional pinned-compiler controls cover an explicit constructor and actual parameter shadowing: raw `\result == amount` becomes canonical `\result == amount_`; wrong spans and crossed constructor/function indices refuse. No selected clause is certified as the failing postcondition and no span is published. Raw origins, exact canonical data and typed aggregate failure remain distinct.

Q-REL-CANONICAL-LEDGER-01 asks whether the producer may factor the local Contract.lean normalization into a shared ordinal-carrying companion with output/forget preservation, or leave that file untouched and continue a proof over its existing full computation. H126's final-reader wrapper alone exposes no local per-clause transformation ledger. No protected producer edit or assumed answer occurred. The three H126 questions remain answered, not re-filed.

The separate owned MCP launcher translates the bridge's TERM to the pinned package's existing interrupt/finally path; shared bridge/package bytes are unchanged. Finder caught repeated TERM interrupting cleanup; skeptic/finder caught unbounded fixture close waits. The genuine before-repair control retains3pass1fail; final4controls pass with idempotent TERM,1000ms accepted closure, confirmed forced cleanup after deadline and exact Linux birth checks. Changed actual per-file diagnostics0errors/supervisor0/retired[] are distinct from injected tests and do not establish the old failure's historical cause. Previous diagnostic supervisor1 and all STOP/failure receipts are untouched. Module build and real controls pass under the unchanged12GiB/no-swap/12GiB-headroom/serial-j1 guard.

The [H44 manifest](dafny-ingress-link-evidence-manifest.json) binds source/control/raw logs off Git. Read-only existing cache/index inspection finds no matching current Shared.Translate trace outputs in the verified pack; it does not resolve the source-matched dependency wait and repeats no failed --no-build or unrelated cold build. Remaining full proof/timed gates, OT-PERF-SLOW, browser+32.20percent STOP, positioned metadata, paired rendered/lifecycle/performance/scaling/macOS and both original per-row judges remain unfinished. All490 ordered rows/frozen270 are unchanged; no row or goal completed, no integration or goal mutation.


### Handoffs — authorized shared normalization and ordinal companion (2026-11-07)

Q-REL-CANONICAL-LEDGER-01 is answered by the incoming user authorization and recorded in dafny-human-decisions.json. Source e8c512eb8 extracts the original constant→enum resolution and parameter/return rewrite into one `normalizeFunctionSpecV1` implementation. `readContract` consumes its resolved/results projections with the original state, binding lists and callback; no duplicated implementation, signature/default/budget change or altered admission/error handling. `normalizeFunctionSpecV1_resolved` and `_results` are rfl equalities to the exact old local expressions. `FunctionSpecNormalizationV1.indexed` numbers all supplied clauses before filtering; its forget and length theorems preserve every original result/error. New proof axioms are only existing propext, and indexed_forget has none.

Per-file diagnostics0errors/supervisor0 and targeted Contract→CounterexampleMetadataV1 rebuild0 use the unchanged12GiB/no-swap/12GiB-headroom/serial-j1 guard with no survivors. The legacy compiled-reader capture confirms helper-loaded=false; after rebuilding helper-loaded=true, all computational fields for Parity, Origins and BindingControls are byte-identical. ScopeScan's proposition field is omitted by proof irrelevance while every feature/diagnostic is retained. This is three-fixture regression evidence, not a whole-importer/compiler correctness theorem. Generic callback controls retain full ordinals, duplicate clauses, original rewrite errors, lexical fields and constant normalization. The initial missing-Repr serializer failure and ambiguous Except-pattern failure remain archived; neither was forced/admitted into a passing proof.

Unchanged admitted retained-candidate/source-negative controls and constructor/shadowing/module-boundary controls pass again in new output directories; original receipts remain untouched. Raw amount versus canonical amount_ remains explicit. Independent read-only finder/skeptic find no equivalence defect and distinguish normalization ordinals from source spans or typed failed-postcondition indices. The [H44 manifest](dafny-normalization-helper-evidence-manifest.json) binds all raw controls/logs off Git.

The local record is currently discarded by the old reader and is not yet transported through the private Import computation. Q-REL-LEDGER-TRANSPORT-01 asks whether those reader/forwarding bodies may be factored into shared internals and versioned ledger-returning companions with forget/equality preservation; H126's Import wrapper-only constraint is not silently expanded. No private Import body change, guessed source mapping, selected-clause failure claim or span publication occurred. All490 ordered rows/frozen270 are unchanged; full metadata/positioned traces, paired rendered/lifecycle/performance/scaling/macOS evidence, original paired row judges and final proof/timing gates remain unfinished. Existing timing/browser STOPs and resource/cache/compiler dependencies are retained; no unchanged stopped workload retried, integration or goal mutation.
