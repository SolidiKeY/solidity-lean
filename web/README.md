# Solidity Lean browser IDE

A static website modeled on the Solidity Lean VS Code extension. Monaco, Solidity
compilation, language services and the pinned Lean proof runtime execute in browser
workers. Source buffers stay in browser storage. No proof server, Node process,
WebSocket or account is required.

Open the [GitHub Pages IDE](https://solidikey.github.io/solidity-lean/ide/).
**File → Download Offline IDE** saves the complete website as one HTML file
(about 900 MB). Reopen that file in a modern desktop browser for offline use,
including fresh proof checking. Keep the original download: the live page removes
embedded data nodes after preparing tools, so the browser's Save Page command
does not produce the original self-contained artifact. A disconnected hosted
tab keeps working; reopening the hosted URL without a connection is not guaranteed.

Supported scalar checks use a compact generated-C/WASM verifier without loading
a Lean environment. Other programs load the general verifier on demand. The
[compact verifier notes](../docs/compact-verifier.md) describe its limits,
measurements and build step; pass `SOLIDITY_BROWSER_DIRECT` to package that build.

## Build the website

Node 22.15 or newer is required for packaging. Build dependencies and toolchains are needed once on the development machine;
they are not runtime requirements for people opening the website.

```sh
npm ci --prefix web

# Requires Docker, a C++ compiler and the pinned native Lean 4.24/SolKey setup.
# Builds GMP64, Lean 4.24 WASM and serialized proof libraries.
bash web/tools/build-lean-browser.sh

SOLIDITY_BROWSER_LEAN="$PWD/web/.lean-browser-build/assets" npm run build --prefix web
npm run build:single --prefix web
npm run start:single --prefix web
```

Open [http://127.0.0.1:4173](http://127.0.0.1:4173) for the single-file preview.
The optional `npm start` command serves static files
from `web/dist`; it has no compiler, proof or language-server endpoints. Deploy
that directory to any same-origin HTTPS static host for the alternative multi-file
build. It uses a service worker and needs HTTPS or localhost.

The single-file artifact is `web/single-file/index.html`. Copy that one file to
a static host or keep it on disk. It embeds an ESM Monaco bundle, solc, Lean,
proof libraries, icons, fonts and license notices. Its asset broker resolves
page/worker requests to embedded Blob URLs; CSP forbids HTTP runtime requests.
No service worker is used. `build.json` records its fingerprint for deployment
tests and is not needed to run the HTML. The Pages workflow preserves the examples
viewer at `/` and places this HTML at `/ide/`.

The alternative multi-file build's manifest lists its static assets. Its first visit downloads
and caches the editor, compiler and proof libraries.
Wait for preparation to finish before disconnecting. Subsequent reloads and fresh
checks use those local assets, including when the static host is unreachable.
Browser storage is origin-specific and may be cleared by the browser; exporting
files provides a durable backup.

The single-file loader stores Zstandard-compressed tools in IndexedDB, using a
separate database per build and creating one Blob at a time. Reopening the same
HTML reuses that disk-backed storage. Allow browser storage and leave several
GiB of disk headroom. Opening a different copy or location may create a separate
workspace; Export is the durable way to transfer source files. Tool caches from
older builds can be removed in browser site-storage settings after exporting
sources. **Help → Third Party Notices** exports all bundled license notices.

Press **F1** for commands or **Ctrl+Shift+Enter** to verify. **Ctrl+S** saves the
current snapshot in browser storage. **File → Export Current File** downloads a
`.sol` file. Opening a disk file imports a copy. Up to four editor documents and
128 flat workspace filenames (32 MiB total) are supported. Browser storage quotas
may be smaller; failed saves retain the dirty marker and offer Export. Proof workers run one at a time;
editing cancels an obsolete proof. A changed source or dependency immediately
invalidates displayed results.

`LEAN_BROWSER_WORK` selects the intermediate build directory;
`LEAN_BROWSER_NATIVE_PREFIX` selects the pinned native Lean installation;
`LEAN_BROWSER_CA_FILE` supplies the build container's trusted proxy CA when needed.
`SOLIDITY_BROWSER_SOLJSON` selects the locally prepared, checksum-verified compiler.
`SOLIDITY_BROWSER_LEAN` may point to an existing packaged browser runtime.
The proof runtime needs a modern desktop browser with WebAssembly tail calls and
64-bit integer operations. Its linear-memory limit is 4 GiB; browser QA also
measures the complete process tree. The browser does not need the Memory64 proposal.
Complex proof search can hit the browser's separate call-stack limit. The IDE
reports that limit explicitly and accepts no proof result for the failed job.
Calldata alias/slice proof search is a known example; listing those functions
only checks admission. The design record includes a reproducer.
A compiler-only development build is possible without Lean assets; it explicitly
disables proof controls and never treats Solidity compilation as a proof.

## Verification

```sh
lake env lean -j1 --tstack=131072 web/test/CalldataImport.lean # native packaging guard
node web/test/proofs.test.cjs           # failure/cancellation protocol boundaries
node web/test/compression.test.mjs     # legacy Brotli decoder boundaries
node web/test/zstd.test.mjs            # native/Wasm agreement, errors and memory bounds
node web/test/checksum.test.mjs        # SHA-256 without Web Crypto or Node APIs
node web/test/optimize-wasm.test.mjs   # optimizer cache integrity and failure cleanup
npm run test:embedded --prefix web    # worker-owned assets, early messages, startup cleanup
node web/test/embedded-assets.cjs --file # small offline-file check, no Lean build
npm run test:website --prefix web      # real browser compiler and disconnected reload
npm run test:website:proofs --prefix web # real kernel proofs, cancellation and offline proofs
npm run test:single --prefix web       # one HTML, reuse, disconnected fresh workers/proofs
npm run test:performance --prefix web  # fresh startup, cold proofs, real edits and cache control
node web/test/performance.cjs --single --calldata-proofs # known failing deep-simp stack diagnostic
node web/test/website.cjs --single --file --proofs # offline local-file launch and reopening
node web/test/offline-preparation.cjs  # incomplete downloads fail visibly
npm test --prefix web                  # optional native transport regressions
npm run start:native --prefix web      # optional development comparison backend
npm run test:native:proofs --prefix web # legacy native comparison harness
```

Browser tests use `CHROMIUM_PATH`, `/usr/bin/chromium` if present, or Playwright's
installed Chromium. Screenshots and JSON reports are written to `web/artifacts/`.
The full browser suite passes 14 checks, including fresh proofs after stopping
the static server and disconnecting Chromium. No backend connections or external
requests were recorded. The actual extension and browser produce the same three
proved functions, pending function, and positioned diagnostic. The captured
workbenches differ by 2.09% overall and 0.03% in the code region.

The performance update measured 26.56 seconds for the first proof request,
including library import, versus 63.25 seconds in the baseline. Fresh navigation
through the first result took 44.89 seconds. Real edited-source checks took
7.33–9.84 seconds; an unchanged cached-result lookup took 19.45 ms and does not
execute a new proof. Warm checks still need substantial improvement. The original
native extension comparison measured 8.94 seconds and is historical. See
[the design record](../docs/web-ide.md#performance-follow-up) for phases and
limits. These are local observations with prepared artifacts, not general
performance guarantees.

The browser port also runs 3,500 differential expression-traversal cases against
the original recursive Lean implementation, plus deep application/binder tests.
It retains the kernel and axiom checks; compilation alone cannot mark a proof green.

The optional native server is opened at `http://127.0.0.1:4173/?backend=native`.
It is excluded from the static deployment.

For an isolated reference editor configured with the production extension and
parity probe, `node web/test/reference.cjs` captures real extension results and a
screenshot. `REFERENCE_URL` selects the host; `SOLIDITY_LEAN_REFERENCE_REPORT`
selects the probe's JSON output. `node web/test/compare.cjs REFERENCE.png WEB.png`
creates a side-by-side image and measured diff.

See [the design and comparison record](../docs/web-ide.md).

Small-program measurements against the actual pinned Java SolKey prover, native
Lean, and this browser build are recorded in
[the detailed comparison](../docs/browser-simple-benchmarks.md).
`node web/test/measure-simple.cjs --single` performs fresh checks with phase
timings. `node web/test/performance.cjs --single --benchmark` also verifies
that multi-function phase events survive the bounded diagnostic log.
