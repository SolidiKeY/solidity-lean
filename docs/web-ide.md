# Offline browser IDE

`web/` builds a [single-file static website](https://solidikey.github.io/solidity-lean/ide/)
matching the Solidity Lean VS Code extension.
Monaco, Solidity compilation, language services and Lean proof checking run in
browser workers. After its first complete asset preparation, the website works
with its host stopped and the browser disconnected. Application source stays
in browser storage; no proof backend or WebSocket is required.
Use **File → Download Offline IDE** to save the original HTML and reopen it offline.

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

The Pages artifact, `web/single-file/index.html`, embeds the entire website in
one file (about 856 MB). Its 1,851 embedded
assets include ESM Monaco, solc, Lean, all proof-library variants, icons, fonts
and license notices. Brotli transport reduces the embedded asset payload to
612 MiB before base64 encoding. Repacking checks that every decoded byte matches
the existing checksum-verified gzip input; the runtime and JS whole-file hashes
remain unchanged. Cached Brotli output is also decoded and compared on every build.

The parser consumes small base64 data blocks, removes their DOM nodes and commits
one Blob at a time to IndexedDB. Databases are isolated by build ID. The completion
marker waits for the editor and actual compiler worker to start; loading failures
invalidate it so reopening retries the original embedded data. The closed asset
broker maps fetch, synchronous library XHR, scripts and nested workers to Blob URLs.
CSP permits no HTTP runtime connections. No service worker or backend is required.
Each worker receives structured-cloned Blob handles and creates its own URLs on
demand. Local-file workers cannot import the parent's `blob:null` URLs. A small
bootstrap queues messages until its embedded entry script has loaded, then replays
them to the installed handler. Checksums use the same SHA-256 implementation when
an opaque worker lacks Web Crypto. Compiler startup errors terminate the owned
worker before reconnecting, including partially initialized workers.
The Brotli decoder streams through 64-KiB input and 1-MiB output buffers so a
large decoded module does not leave a second whole-module allocation in Wasm
memory. Its boundary/size/truncation tests compare against Node's native decoder
and check that 40-MiB output leaves less than 64 MiB of decoder linear memory.

The single HTML supports continued use in a disconnected tab; reopening a hosted
URL offline depends on the browser's document cache. Download and reopen the HTML
for durable offline access. Browser Save Page is unsuitable because embedded data
nodes have already been removed. Original HTML downloads retain those nodes.
IndexedDB and source storage can be cleared or evicted; Export backs up sources.
Allow several GiB of free disk space for tools and temporary browser storage.

`.github/workflows/pages.yml` builds and tests this exact file before publication,
adds it under `/ide/` alongside the existing examples viewer, checks the total
site budget and deploys to GitHub Pages. A second job tests the published URL and
compares its embedded build ID with the generated artifact. The pre-publication
test opens the downloaded file in a fresh offline profile, reopens it using its
stored assets and checks fresh proofs. Local managed Chromium blocks `file://`
navigation; that boundary is tested on the unrestricted GitHub runner instead.

The alternative multi-file development build retains its service-worker cache:

`web/dist` contains only static assets. The optional native comparison server
is development tooling and is excluded from deployment. Static builds force
browser mode even for a URL containing `?backend=native`.

The tested artifact contains 773.7 MiB of assets, including 1,822 proof-library
modules (2,445.3 MiB serialized, compressed per module). The first visit caches
the complete manifest before opening Monaco. A missing manifest, failed asset
or storage quota error prevents an incomplete cache from announcing readiness.
Installation failures surface visibly rather than waiting forever. Build-specific
cache names support updates and remove obsolete application caches.

Hashed libraries are immutable same-origin assets. A lazy filesystem verifies
compressed hashes and retains at most 64 MiB of inflated modules, or one larger
module. It does not preload the entire library into linear memory. CSP limits
application connections to the website origin. HTTPS or localhost is required;
opening the multi-file build's `index.html` as a local file is unsupported.

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

Validation uses the `c6c33c90` frontend baseline after a fresh 264-job rebuild.
Reports record both the static artifact and proof-runtime hashes.

Fourteen real Chromium checks pass with every WebSocket constructor forbidden,
zero external requests and zero uncaught page errors. They cover compilation,
rename/formatting, imported definitions, closed sibling refactoring, missing
imports, failed saves, real kernel proofs, active cancellation, a changed false
specification, certified opt-in counterexamples and fresh compilation/proofs
following a disconnected reload with the static asset server stopped.
The single-file suite also verifies that the only HTTP document requests are
the HTML launch/reopen, that every embedded data node is released and that the
download command is reachable. Its final disconnected check restarts both
workers; the local-file CI variant reopens the HTML instead.

Five protocol tests cover partial nonzero outputs, missing checkpoints, wrong
declarations, timeout causes and cancellation. These explicitly use a mock worker
and are not evidence of kernel proof success. Two additional Chromium cases
verify visible failure for a missing asset manifest or required worker asset.
The native frontend build passed 264 jobs; 66 extension/LSP/backend/web transport
regressions also passed during implementation.
This milestone additionally passed the two streaming-decoder tests and ten
native transport regressions. The final single-file comparison artifact is
`f020402da107…`, with Brotli manifest `16ba39b77198…`; JSON evidence records
the full hashes. The ported Wasm bytes retain their original whole-file digest.

| Observation | Real VS Code extension | Browser website |
|---|---:|---:|
| First measured verification | 8,942.3 ms | 67,219.6 ms |
| Repeated checked-result lookup | 185.5 / 170.6 ms | 172.2 ms |
| `increment()`, `reset()`, `one()` | proved | proved |
| `openGoal()` | pending | pending |
| Pending diagnostic and source range | identical | identical |

Browser cold verification includes the first library import. Fresh verification
after stopping the server and restarting workers offline took 64,691.2 ms in
the first complete single-file run. Editor readiness was 12,832.3 ms there and
16,194.0 ms in the final comparison run, including first-visit embedded-tool
preparation. Reopening using stored tools took 6,684.4 ms. Native scripted editor-readiness
includes navigation and is not used as a startup benchmark. These are observations
from one local environment with prepared artifacts, not performance guarantees.

The final Testing/Problems screenshots differ in 27,061 pixels (2.09%) at
pixelmatch's 0.1 threshold with antialiasing ignored. The separate 1000 × 540 code
region differs by 0.03%. Both images were inspected directly. Visible differences
include title/menu controls, native test-run history/filter chrome, some panel
labels and the browser/offline status. Pixel similarity describes these captures,
not complete VS Code feature parity.

Evidence is generated under `web/artifacts/`: `single-file-report.json`,
`single-file-reference-report.json`, `native-report.json`, `replace-differential.log`,
`native-problems.png`, `single-file-problems.png`, `website-offline-proofs.png`,
and `single-file-comparison/{side-by-side.png,visual-diff.png,visual-comparison.json}`.
The earlier multi-file runs remain in `website-report.json` and
`website-reference-report.json`.
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
The single-file reviews resolved per-build storage isolation, delayed compiler
readiness, retry invalidation, cached Brotli integrity, bounded decoding,
file-origin test APIs, exact published-build assertions and the complete Pages
site budget. Focused Chromium experiments reproduced Blob failures when a
runtime's decoded buffers were queued together; decoding inside the serial
write queue fixed that path. Both final reviews found no further actionable issue.

The first clean Pages build exposed GMP's missing generated limb tables: invoking
the library target alone skipped Automake's `BUILT_SOURCES`. The build now uses
the default target, with unused Info-manual generation disabled. A fresh empty
Docker build passed all layout assertions and the `2^256` arithmetic probe.
The recovery workflow only replaces a failed-IDE run whose commit is an ancestor
of the new push, so a delayed helper cannot cancel a newer build.
The clean file-origin test then exposed cross-worker Blob URL ownership. An
opaque-iframe regression now checks nested imports, fetch, synchronous XHR and
early messages after revoking the parent's URLs; a second case verifies that
heartbeat activity stops after partial startup fails. Completed kernel assets
are cached before browser validation, so a later UI failure preserves that build.

The writer lock is held throughout changes and checks. Heavy jobs run sequentially.
This environment has no systemd bus: builds use a four-GiB, no-swap Docker cap
and an available-memory guard; browser QA uses an owned-process RSS/available-memory
watchdog with the required 12-GiB host reserve. The complete browser run peaked
at 4.80 GiB aggregate RSS in the first complete single-file run. Task-owned profiles/reference files were moved off the
RAM disk. Interrupted resource/stack-overflow attempts are not passing checks.
