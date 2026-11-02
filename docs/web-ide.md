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
calls reduce stack growth along compiled frontend call chains.
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
The linked, memory64-lowered module also receives a pinned Binaryen `-O1`
postpass with tail calls and exception handling enabled. This changes generated
code, not Lean algorithms or proof budgets. A content-checked stamp prevents
reoptimizing an unchanged output; relocation, corruption and optimizer failures
are regression-tested. A failed pass preserves the input and removes its partial
output. The measured pass peaked at 3.76 GiB RSS within the build limit.

`BrowserFrontend.lean` reuses immutable imported environments, then creates fresh
synchronous command state and a unique main module per check. Unique names keep
project alias caches from colliding across revisions. Existing `solc_import`,
`solc_scoped_problems` and `#solkey_test` retain their admission, kernel and axiom
checks. Only fresh checkpoints matching the selected AST declarations produce
results. Nonzero exits and missing checkpoints are errors. Solidity compilation
alone never produces a proved status.

The performance update replaces broad `Lean` imports in the AST, equation
attributes, budget helpers and source frontend with their required modules.
Tactic clients explicitly import assertion, clearing and suggestion helpers.
Declarations, proof bodies and the axiom policy are unchanged. The browser graph
now starts from Testing plus the parsed imports of `BrowserFrontend.lean`, rather
than forcing the umbrella `Lean` module into every package. The pinned parser
finds 1,556 modules instead of 1,822. The first narrowed-import package contained
2,183.4 MiB of serialized libraries instead of 2,445.3 MiB; the final package
with the newer upstream frontend contains 2,185.5 MiB.

The same native build supplies the rebuilt serialized libraries and interpreter
data. Compiling the project importer into additional Wasm was evaluated and
excluded from the release because its memory cost exceeded the available-memory
reserve. The final runtime retains the existing project interpreter and compiled
Lean kernel; the performance changes do not add a second proof implementation.

Proof jobs are serialized. Source/dependency changes terminate obsolete active
workers and invalidate their epochs; late results cannot update the editor.
Cancel, timeout and restart clear owned work. Automatic verification does not
replay an explicit cancellation or a failing job indefinitely.

## Offline preparation and limits

The Pages artifact, `web/single-file/index.html`, embeds the entire website in
one file. `build.json` records its byte size, fingerprint and runtime hashes.
Its assets include ESM Monaco, solc, Lean, all required proof-library variants,
icons, fonts and license notices. Zstandard replaces the earlier release's
Brotli transport. Repacking checks that every decoded byte matches the existing
checksum-verified gzip input, including cached compression output. Transport
changes preserve the input runtime's and JS loader's whole-file hashes.

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
The proof worker reads its owned Blobs with `FileReaderSync`; asynchronous
startup reads use `Blob.arrayBuffer()`. This avoids URL/network machinery and
bulk compressed prefetching in the single-file build. Environment parts and IR
are separate compressed assets: Lean reads IR in a second pass, which formerly
reinflated environments after cache eviction. One last-file view avoids repeated
subarray allocations during small native reads. The decoded cache retains at
most 8 MiB or one larger asset. The HTTP alternative uses authenticated prefetch
with eight in-flight reads, a 768 MiB retention cap, and release after checking.

The pinned Zstandard decoder checks declared frame sizes, error codes and exact
output lengths before copying; native allocations are released in `finally`.
Its tests compare against Node compression, reject malformed streams and verify
retained decoder memory after a 40-MiB output. A Wasm SHA-256 implementation
preserves checksum checks in opaque workers without Web Crypto. Opaque/file
worker smoke tests exercise decoder startup and direct asynchronous/synchronous
reads under the production broker and CSP. Legacy Brotli decoding remains tested.

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

The multi-file artifact's manifest records its complete asset list. The first visit caches
the complete manifest before opening Monaco. A missing manifest, failed asset
or storage quota error prevents an incomplete cache from announcing readiness.
Installation failures surface visibly rather than waiting forever. Build-specific
cache names support updates and remove obsolete application caches.

Hashed libraries are immutable same-origin assets. A lazy filesystem verifies
compressed hashes and retains at most 8 MiB of inflated modules, or one larger
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

The browser's machine-call stack is a separate limit. Complex calldata alias/slice
proof search currently exceeds it during recursive simplification, despite the
same bodies importing successfully. The failed job reports `BROWSER_STACK_LIMIT`
and accepts no proof result. `node web/test/performance.cjs --single --calldata-proofs`
reproduces that known limitation; ordinary listing returns `ready` for both
functions and retains the writable-copy refusal. Listing establishes admission,
not proof success. The default performance test uses listing for this additional
control. General native proof-search parity remains incomplete.

## Measured validation

The original comparison used the `c6c33c90` frontend baseline after a fresh 264-job rebuild.
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
That milestone additionally passed the two streaming-decoder tests and ten
native transport regressions. Its final single-file comparison artifact was
`f020402da107…`, with Brotli manifest `16ba39b77198…`; JSON evidence records
the full hashes. Its transport repacking retained the input Wasm whole-file digest.

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

## Performance follow-up

The final measurement includes upstream `febf70a6`, the narrowed imports and
calldata integration repair, and the optimized browser runtime. A fresh native
`Solidity.Frontend.Testing` build passed all 264 jobs and the four calldata
import-status guards. The nine initial Lean edits had clean per-file diagnostics;
after integration the changed importer and new regression file were checked
again with clean Lean MCP diagnostics. Project serialized artifacts were refreshed
alongside the pinned native standard library before packaging.

The measured HTML is `d21fc01ffc52…`, kernel manifest `b3a70f6bc704…`, with runtime
SHA-256 `f7cd91e0de1180cc701e021cbc2bef47c741b58ead6fe40c9d78932483cd16df`.
It contains 2,877 embedded assets and is 837,616,302 bytes. The Binaryen pass
reduced the linked module from 163,947,747 to 148,152,933 bytes. Static comparison
preserved 170,753 exports and their function signatures, 389 imports and the
32-bit memory contract (4,096 initial / 65,536 maximum pages). The production
helper reproduced the benchmarked output byte for byte and verified a repeat
cache hit. Its guarded production pass peaked at 3.65 GiB aggregate RSS.

A fresh Chromium profile produced these measurements on the managed host:

| Measurement | Time |
|---|---:|
| Editor/compiler/kernel readiness, including initial tool preparation | 17.43 s |
| First proof request, including library import | 23.49 s |
| Page navigation through first proof result | 40.93 s |
| Unchanged cached-result retrieval | 7.55 ms |
| Real proof after a comment edit | 8.81 s |
| Real proof after changing `return 1` to `return 2` | 7.55 s |
| Real proof after updating the postcondition to match `2` | 9.42 s |
| Calldata admission/listing, without executing its proof search | 0.43 s |

The baseline audit measured 63.25 s for its cold proof request and 16.68 s for
fresh startup. Cold proof latency fell by about 63%; navigation through the first
result fell from roughly 80 s to 41 s. Before integrating the newer upstream
frontend and the post-link optimization, the narrower-import/transport update
alone measured 29.08 s for the cold request and 49.11 s through the first result;
that evidence remains in `performance-before-integration-report.json`. These
observations include multiple changes and normal run-to-run variation. Warm
rechecks remain slow; they do not establish parity with Dafny or SolKey. The
original 8.94-s native extension comparison above is historical. Measurements use
locally prepared artifacts and exclude the initial Internet download.

The false-result edit stayed pending; updating its specification made it prove.
Every result matched the exact edited source's SHA-256. The unchanged-source
control retrieved a cached report; its retained kernel timings describe the
original check and are not new execution. All three edited Counter trials ran
new kernel checks with zero library reads. The cold import decoded
2,282,434,832 bytes from the 2,291,674,968-byte package, with no second environment
inflation pass. It used 2,839 direct Blob reads, zero bulk-prefetched bytes and
zero XHR fallbacks. Measured phases included 1.80 s of synchronous reads, 2.39 s
of checksum work and 4.54 s of decompression. Peak aggregate benchmark RSS was
3.89 GiB; the 12-GiB available-memory reserve remained intact. No external
requests, WebSockets or uncaught page errors were recorded.

`node web/test/performance.cjs --single` reproduces the five Counter timing
controls plus the explicitly named calldata admission/listing control. Its report
is `web/artifacts/performance-single-report.json`. Listing returns `ready` for
aliases and slices and `unsupported` for writable copies; those rows are not
proof successes. `--calldata-proofs` remains a known failing deep-simplification
stack diagnostic. The actual stack-limit boundary is also checked separately
for its explicit error and rejection of a proof report.

Focused checks passed for six protocol boundaries, two legacy Brotli cases,
two Zstandard cases, browser SHA-256 without Web Crypto or Node APIs, and optimizer
cache reuse, relocation, corruption and failure cleanup. Opaque-worker lifecycle
coverage passed as well. Full browser evidence is written to
`web/artifacts/single-file-report.json`: all 14 checks passed on this exact HTML,
with zero external requests, WebSockets or page errors. A semantically changed
program (`return 3` with its updated postcondition) proved after both workers
restarted with the server stopped and Chromium disconnected. That fresh offline
check took 26.88 s. The full suite peaked at 4.26 GiB aggregate RSS and preserved
the available-memory reserve. The separate real stack-error boundary passed at
3.99 GiB, retained `BROWSER_STACK_LIMIT`, and accepted no proof report. CI
additionally runs fresh file-origin launch/reopening and verifies the published
build after deployment.

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

The performance follow-up's read-only finder and skeptic reviews found no
remaining actionable implementation issue. They confirmed the parsed import
closure, removal of the importer-compilation experiment, unchanged file bytes
and offsets after splitting IR, checksum verification on direct Blob reads,
bounded decoder/cache lifetime, preserved cancellation and exact source hashes.
Earlier review findings led to disjoint I/O/hash counters, bounded/released HTTP
prefetch, and a semantically changed program/specification in the final offline
proof test. Neither review ran the Lean server or a heavy build.
The final suite exposed a retained HTTP connection postponing the development
server's shutdown. Closing existing connections after stopping acceptance fixed
that harness boundary; a paused, unfinished HTML response also passed a focused
shutdown check. Both reviews accepted the change. The interrupted attempt is
recorded separately and is not counted as a passing run. Final suite evidence
was refreshed to the exact performance artifact before committing. Changed
documentation links resolve; the repository-wide path scan still reports 48
existing missing references in external citations and older records.

Integration brought in upstream `febf70a6`, including frontend and closer
changes. A read-only review identified an inherited calldata regression:
the importer generated `sol_raw_calldata!` but a new branch matched only
`sol_raw!`, refusing aliases and slices. Two native guards reproduced those
failures while an ordinary parameter and writable-copy refusal remained correct.
Removing the redundant branch leaves the existing origin-preserving macro in
control. The final native frontend build passed all 264 jobs and all four
guards; Lean MCP diagnostics were clean for the importer and regression file.
Pages runs the guards before checking the kernel cache. Finder and skeptic
reviews accepted the fix, test controls and CI placement without using Lean.

The subsequent `a3205e6a` integration made `LinearDecision` reachable through
call sharing. Its existing umbrella `Lean` import expanded the browser graph to
1,871 modules and 2,537.9 MiB, producing a 955-MB HTML. The arithmetic helper now
imports `Lean.Elab.Tactic`, retaining `omega` and `grind`; its declarations and
proofs are unchanged. Both the parsed graph tool and packager reject umbrella
`Lean` imports so this regression fails before an expensive Wasm build. Per-file
diagnostics and the rebuilt 313-job frontend plus calldata guards passed. The
browser harness reuses Chromium's initial tab, matching a single IDE tab without
retaining an unused blank renderer. Finder and skeptic reviews accepted the
import and graph guards without using Lean.

The writer lock is held throughout changes and checks. Heavy jobs run sequentially.
This environment has no systemd bus: builds use a four-GiB, no-swap Docker cap
and an available-memory guard; browser QA uses an owned-process RSS/available-memory
watchdog with the required 12-GiB host reserve. The complete browser run peaked
at 4.80 GiB aggregate RSS in the first complete single-file run. Task-owned profiles/reference files were moved off the
RAM disk. Interrupted resource/stack-overflow attempts are not passing checks.
