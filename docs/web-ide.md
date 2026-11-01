# Offline web IDE

`web/` provides an offline local web workbench for Solidity Lean. The visual
reference is the production extension in VS Code's web workbench, running in an
isolated OpenVSCode Server 1.105.1 host with Default Dark+, a 1440 × 900 viewport,
14 px monospace text and 20 px line height. Both run the same `Counter.sol` example.

## Runtime and trust boundary

The browser uses Monaco 0.55.1. Its token patterns are read directly from
`vscode/syntaxes/solidity.tmLanguage.json`; proof decorations use the extension's
four SVGs. Dark+ token colors, line-number width, glyph margin and pane geometry
follow the reference. The workbench includes editor tabs, Explorer, Outline,
search, local change comparisons, verification controls, Testing, Problems,
Output, results, settings and a keyboard command palette.

The Node HTTP/WebSocket server binds `127.0.0.1`. Each browser connection has an
isolated temporary directory under `.lake/web-ide/` and an instance of the
extension's production `LanguageClient`. That launches the unchanged stdio LSP,
pinned solc compiler, bounded worker pool and native Lean kernel. No alternate
proof engine or simulated proof result is used. The core Lean package gains no
dependencies. A WASM port is unnecessary for this local-runtime arrangement;
fully browser-contained kernel checking remains future work.

Compilation, completion, hover, symbols, signature help, references, highlights,
definitions, formatting, guarded rename and quick fixes use the production LSP.
Native version checks are preserved when translating workspace edits to Monaco.
Every edit immediately clears all displayed proofs, synchronizes its buffer and
invalidates imported results. Workspace-sensitive operations synchronize every
open model and materialize all browser workspace files, including unopened and
closed dirty imports. The four-open-document limit is independent of the
128-file/32-MiB workspace limit. Unsupported source constructs retain the native
backend's explicit admission gaps and pending states.

HTTP exposes an explicit asset allowlist and bounded example/bootstrap endpoints.
It has no shell endpoint or generic filesystem API. WebSocket origin and Host
checks restrict browser callers to the local origin; method, path and snapshot
validation prevent workspace traversal and stale calls. Settings retain the
per-session project root. Disconnection disposes the session and process tree,
including when a language-server restart is in flight.

## Offline behavior and storage

After one-time dependency and toolchain preparation, all editor assets, compiler
input and kernel checking stay on the computer. CSP limits connections to the
local origin. There are no external fonts, CDN imports, accounts, telemetry,
hosted proof endpoints or production publication. The browser tests abort and
record any attempted external HTTP request.

The service worker controls the first Monaco load and caches its AMD graph and
workers. A fresh-profile regression visits once, disconnects completely, reloads,
edits and then checks persistence after reconnection. Browser files and settings
are stored locally. Proofs are never persisted as fresh certificates and are
cleared when the backend disconnects. `Ctrl+S` preserves a named, versioned buffer;
typing or switching tabs during its asynchronous work cannot mark another
snapshot clean. Export downloads a `.sol` file. Local Changes compares the current
buffer with its last saved browser snapshot; it is not a Git implementation.

Native Node/Lean is required for fresh proofs. A completely disconnected browser
can edit cached files but cannot run the native kernel. Browser storage is
origin-specific; exporting is the durable backup, and imported disk files are
never overwritten. A change of port creates a different browser storage origin.

## Reproducing the comparison

Run the commands in [web/README.md](../web/README.md). The browser suite exercises
real Monaco rename, formatting and F12, exact unsaved buffers, unopened imports,
rapid multi-file edits, compiler errors, local diffs, settings, disconnected
reload, narrow layout and the command palette. `test:proofs` additionally checks
that `one()` is kernel-proved while `openGoal()` stays pending, compares a warm
repeat, checks the exact proof hover and verifies immediate proof invalidation.

For a real reference editor, install `vscode/` and
`web/test/reference-extension/` only into an isolated VS Code/OpenVSCode profile.
Set `SOLIDITY_LEAN_REFERENCE_REPORT` to an output JSON file. Open
`web/examples/Counter.sol` and run **Solidity Lean Parity: Capture**. This calls the
production extension API three times, records real timings/reports, Testing items,
diagnostics and hover, and leaves its real decorations visible for screenshots.
The probe has no production role and never injects fixture results.

Capture both workbenches with identical viewport, source, theme, font and panel
geometry, then run:

```sh
node web/test/compare.cjs /absolute/path/reference.png /absolute/path/web.png
```

This produces a side-by-side PNG, pixel diff and JSON metrics. It separately
compares the code region so uniform panels cannot hide a different editor.
Pixel comparisons describe only the captured states, not full VS Code parity.
Generated artifacts stay in ignored `web/artifacts/` and can be regenerated.

## Measured result

The completed local comparison passed 57 unit/regression tests (47 existing
extension/LSP checks and 10 web server checks), plus 13 browser integration
checks. The real `Solidity.Frontend.Testing` build passed with 264 jobs. Browser
checks recorded zero external HTTP requests and zero uncaught page errors.

| Observation | Native VS Code extension | Offline web IDE |
|---|---:|---:|
| First measured verification | 7,637.9 ms | 7,879.2 ms |
| Repeated checked-result lookup | 137.3 / 136.5 ms | 144.9 ms |
| `increment()`, `reset()`, `one()` | proved | proved |
| `openGoal()` | pending | pending |
| Proof diagnostics | one pending warning | identical message, code and severity |

The web workbench's fresh-profile startup was 852.4 ms. These are observations
from one local environment with prepared Lean artifacts, not general performance
guarantees. The reference host's scripted editor-readiness time includes UI
navigation delays and is not used as a startup benchmark.

The final 1440 × 900 Problems/Testing screenshots differ in 26,973 pixels (2.08%)
at pixelmatch's 0.1 threshold with antialiasing ignored. The separate 1000 × 540
code region differs by 0.02%. The workbenches share the visible source, token
colors, gutter results, diagnostics and editor geometry. Remaining visible
differences include title/menu controls, native run-history icons, filter chrome,
some panel tabs and the explicit local/offline connection indicator.

`browser-report.json`, `native-report.json`, `unit-test.log`, `native-problems.png`,
`web-problems.png`, `side-by-side.png`, `visual-diff.png` and
`visual-comparison.json` preserve this run's evidence under `web/artifacts/`.
The browser report also records the selected-function gutter run, cached offline
reload and responsive-layout checks. The reference probe and browser reports
were compared directly for exact function statuses and diagnostic equivalence.

## Milestone review

Independent read-only finder and skeptic reviews identified and resolved:
first-load Monaco caching, unopened/closed import snapshots, multi-file edit
synchronization, guarded rename versions, project-root loss after settings
changes, wrong-file individual Testing runs, cross-file definition opening,
completion-kind mapping, save identity and restart/disconnect cleanup. Regressions
cover these boundaries. Neither review used the Lean server.
Follow-up findings about transfer size, cleanup during server shutdown and F12
at the open-editor limit were also fixed; tests cover the transport and teardown
cases. The browser exercises actual native-backed rename and cross-file F12.

The managed environment has no systemd user/system bus. The required sequential
backend rebuild therefore uses an aggregate RSS/12-GiB available-memory watchdog
rather than a systemd scope, and a temporary configuration sets `-j1`. A tried
address-space limit caused thread creation failures by bounding virtual memory;
it was removed, and those interrupted attempts are not passing checks.
The writer lock is held throughout changes and checks. No Lean source or core
representation is changed by this work.
