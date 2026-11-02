# Offline browser IDE

`web/` builds a static website matching the Solidity Lean VS Code extension.
Monaco, Solidity compilation, language services and Lean proof checking run in
browser workers. After its first complete asset preparation, the website works
with its host stopped and the browser disconnected. Application source stays
in browser storage; no proof backend or WebSocket is required.

## Runtime and correspondence

Monaco 0.55.1 uses the extension's grammar and four proof SVGs. Dark+ token colors,
line numbers, glyph margin, font and pane geometry follow the real extension in
an isolated OpenVSCode Server 1.105.1 profile at 1440 × 900, 14 px and 20 px line height.
Explorer, Outline, search, local changes, Testing, Problems, Output, results,
settings and keyboard commands use the same workbench shell.

A browser worker bundles the unchanged `solc-ast.mjs` compiler frontend and the
extension's AST language services, formatter, project snapshots and report
validation. In-memory platform adapters provide files and SHA-256. They cannot
spawn a process or read the host filesystem. The same-origin soljson 0.8.34
compiler is checksum-verified before execution. Language operations use exact
unsaved snapshots, include closed importers and validate affected compilation roots.
`vscode/src/report.cjs` extracts the native backend's existing pure report parser
so both runtimes use the same validation.

A disposable worker hosts Lean 4.24.0, upstream commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, with explicit browser-port patches.
Emscripten 4.0.15 and GMP 6.2.1 preserve the native 64-bit Lean object/integer
layout while lowering memory access to ordinary WebAssembly. WebAssembly tail
calls prevent compiled frontend call chains from exhausting the browser stack.
The browser does not require the Memory64 proposal or a thread pool.

The port replaces the C++ expression-replacement recursion with an explicit
traversal stack in the browser build. This is trusted substitution code, so it
has direct differential checks against the unchanged recursive implementation:
3,500 mixed-node/shared-DAG cases compare exact results, callback traces, scope
offsets, pruning, cache policies, identity and exception unwinding. Separate
checks exercise 50,000-deep applications and 30,000-deep binders. Both C++ and
Lean-callback variants are covered. The runtime's startup probe exercises 6,000
binder levels, accepts a valid declaration, rejects an ill-typed declaration,
and checks synchronous promise map/bind/drop behavior. Native kernel behavior
and the Solidity core model are not changed.

The generated loader also avoids a linear scan of roughly 180,000 exports on
every symbol lookup. Export membership uses direct lookup; new function-table
entries use a cached symbol index. Build scripts pin and check upstream sources,
GMP layout, native serialized-library version and compiler checksum. The full
patch, traversal oracle and build tools are under `web/tools/lean-wasm/`.

`BrowserFrontend.lean` reuses immutable imported environments, then creates fresh
synchronous command state and a unique main module per check. Unique names keep
project alias caches from colliding across revisions. Existing `solc_import`,
`solc_scoped_problems` and `#solkey_test` retain their admission, kernel and axiom
checks. Only fresh checkpoints matching the selected AST declarations produce
results. Nonzero exits and missing checkpoints are errors. Solidity compilation
alone never produces a proved status.

Proof jobs are serialized. Source/dependency changes terminate obsolete active
workers and invalidate their epochs; late results cannot update the editor.
Cancel, timeout and restart clear owned work. Automatic verification does not
replay an explicit cancellation or a failing job indefinitely.

## Offline preparation and limits

`web/dist` contains only static assets. The optional native comparison server
is development tooling and is excluded from deployment. Static builds force
browser mode even for a URL containing `?backend=native`.

The tested artifact contains 773.6 MiB of assets, including 1,822 proof-library
modules (2,445.1 MiB serialized, compressed per module). The first visit caches
the complete manifest before opening Monaco. A missing manifest, failed asset
or storage quota error prevents an incomplete cache from announcing readiness.
Installation failures surface visibly rather than waiting forever. Build-specific
cache names support updates and remove obsolete application caches.

Hashed libraries are immutable same-origin assets. A lazy filesystem verifies
compressed hashes and retains at most 64 MiB of inflated modules, or one larger
module. It does not preload the entire library into linear memory. CSP limits
application connections to the website origin. HTTPS or localhost is required;
opening `index.html` as a local file is unsupported.

Files/settings use browser storage. Save identifies the named versioned buffer;
typing or switching tabs cannot mark a different snapshot clean. Failed persistence
retains the dirty marker. Export downloads a `.sol` copy; origin storage can be
cleared or evicted, so Export is the durable backup. Proof reports are not stored
as fresh certificates. Local Changes compares snapshots rather than implementing Git.

The prototype supports four open documents, 128 flat workspace filenames and
32 MiB of source snapshots. Storage quotas may be smaller. One proof worker runs
at a time with a 4 GiB linear-memory limit. Use a modern desktop browser with
WebAssembly tail calls and 64-bit integer operations.

## Measured validation

Fourteen real Chromium checks pass with every WebSocket constructor forbidden,
zero external requests and zero uncaught page errors. They cover compilation,
rename/formatting, imported definitions, closed sibling refactoring, missing
imports, failed saves, real kernel proofs, active cancellation, a changed false
specification, certified opt-in counterexamples and fresh compilation/proofs
following a disconnected reload with the static asset server stopped.

Five protocol tests cover partial nonzero outputs, missing checkpoints, wrong
declarations, timeout causes and cancellation. These explicitly use a mock worker
and are not evidence of kernel proof success. Two additional Chromium cases
verify visible failure for a missing asset manifest or required worker asset.
The native frontend build passed 264 jobs; 66 extension/LSP/backend/web transport
regressions also passed during implementation.

| Observation | Real VS Code extension | Browser website |
|---|---:|---:|
| First measured verification | 8,175.2 ms | 74,894.9 ms |
| Repeated checked-result lookup | 173.4 / 147.1 ms | 146.5 ms |
| `increment()`, `reset()`, `one()` | proved | proved |
| `openGoal()` | pending | pending |
| Pending diagnostic and source range | identical | identical |

Browser cold verification includes the first library import. Fresh verification
after stopping the server and reloading offline took 74,139 ms. Editor readiness
was 8,676.3 ms in the functional run and 11,753.4 ms in the comparison run,
including complete first-visit asset caching. Native scripted editor-readiness
includes navigation and is not used as a startup benchmark. These are observations
from one local environment with prepared artifacts, not performance guarantees.

The final Testing/Problems screenshots differ in 27,025 pixels (2.09%) at
pixelmatch's 0.1 threshold with antialiasing ignored. The separate 1000 × 540 code
region differs by 0.02%. Both images were inspected directly. Visible differences
include title/menu controls, native test-run history/filter chrome, some panel
labels and the browser/offline status. Pixel similarity describes these captures,
not complete VS Code feature parity.

Evidence is generated under `web/artifacts/`: `website-report.json`,
`website-reference-report.json`, `native-report.json`, `replace-differential.log`,
`native-problems.png`, `website-problems.png`, `website-offline-proofs.png`,
`side-by-side.png`, `visual-diff.png` and `visual-comparison.json`.
See [web/README.md](../web/README.md) for commands. The reference probe calls the
production extension API and never injects fixture results.

## Milestone review and resource bounds

Read-only finder and skeptic reviews identified and resolved closed-importer
rename, missing-import diagnostics, stale cache cleanup, active cancellation,
nonzero partial checkpoints, output cleanup, timeout causes, automatic replay,
mandatory offline manifests, installation failure handling and loader callback
exceptions. They separately reviewed the iterative replacement's reference
counts, cache decisions, scope offsets, child order and result lifetimes. Final
reviews found no remaining actionable implementation issue and confirmed the
stopped-host offline proof artifact. Neither review used the Lean server.

The writer lock is held throughout changes and checks. Heavy jobs run sequentially.
This environment has no systemd bus: builds use a four-GiB, no-swap Docker cap
and an available-memory guard; browser QA uses an owned-process RSS/available-memory
watchdog with the required 12-GiB host reserve. The complete browser run peaked
at 4.82 GiB aggregate RSS. Task-owned profiles/reference files were moved off the
RAM disk. Interrupted resource/stack-overflow attempts are not passing checks.
