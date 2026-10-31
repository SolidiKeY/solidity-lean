# Dafny VS Code comparison harness

This audit compares the official Dafny extension with `vscode/`, the Solidity
Lean verification extension. Full parity is not established. The
[editor inventory](dafny-editor-features.json) records 88 discovered capabilities,
including explicit missing and unexamined work. This inventory is separate from
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
of 1–4 proof workers each keeps one Lean language server and generated document
alive, reusing imported modules on edits. Workers parallelize files; contracts
and obligations within a file remain serial. The server uses the existing
`solc_import` and `#solkey_test` commands and kernel-checked certificates.
It retains source hashes, compiler pins, import-gap diagnostics and counterexample
validation. Dependency changes invalidate live sessions and checked reports.

The server provides completion, definitions, references, symbols, signatures,
highlights, guarded rename, versioned diagnostics and verification notifications.
The extension adds syntax, gutters, status and Testing integration. Completion
uses a broad lexical fallback for incomplete code; full receiver-aware completion,
workspace symbols, formatting, code actions, project includes and assertion-level
parallel scheduling remain open. See [the implementation record](feature-work/solidity-lsp.md).

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

Local worker settings are applied to concurrent files (maximum four).
The local exact-snapshot proof cache is always enabled; Dafny cache-policy names
do not select equivalent local policies. Local scaling uses the two-file metric,
while Dafny scaling uses the within-file declaration metric. These scopes must
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

## Current persistent LSP validation

The [LSP baseline](../tests/editor-parity/lsp-baseline.md) and
[validation record](../tests/editor-parity/lsp-validation.json) cover the current
implementation after integration with master. All 18 editor launches passed
without broken scenarios; gaps remain classified separately. One-worker local
median changed-buffer verification was 5.17 s versus Dafny's 247 ms; unchanged
local cache hits took 100 ms. These are different operations. The
[implementation record](feature-work/solidity-lsp.md#measured-editor-results)
explains warm-session evidence, cross-file scaling and remaining proof costs.
