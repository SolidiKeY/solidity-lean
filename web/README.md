# Solidity Lean offline IDE

A local website IDE modeled on the Solidity Lean VS Code extension, with
Monaco, the extension's syntax grammar and gutter icons, and its production
language server and Lean proof workers. It makes no Internet requests at runtime.

From the repository root, with the existing compiler and Lean setup available:

```sh
# One-time preparation, while dependencies are available.
npm ci --prefix web
LEAN_NUM_THREADS=1 lake build Solidity.Frontend.Testing

# Run locally, including with the Internet disconnected.
npm start --prefix web
```

Open [http://127.0.0.1:4173](http://127.0.0.1:4173). Set `PORT` to use another
port. The server listens only on loopback. The compiler, Lean/Lake and `SOLKEY_ROOT`
use the same configuration as the [VS Code extension](../vscode/README.md).
In the supplied cloud workspace, source `/workspace/.setup/activate.sh` first.

Press **F1** for commands or **Ctrl+Shift+Enter** to verify. **Ctrl+S** saves the
current snapshot to browser storage and the temporary local compiler workspace.
**File → Export Current File** downloads a durable `.sol` file. Opening a file
imports a copy; it does not overwrite the original disk file. Up to four editor
documents and 128 workspace files (32 MiB total) are supported.

Internet access is unnecessary after preparation. Keep the local server running
for compilation and proof checking. After one visit, the service worker also
caches the editor: with the local server unavailable, the app can reload, edit
and export browser-stored buffers. Its connection indicator shows that proof
checking is unavailable, and previous proof results are cleared. A browser-only
Lean/WASM runtime is not included.

```sh
npm test --prefix web                 # transport and session regressions
npm run test:browser --prefix web     # real compiler and browser interactions
npm run test:proofs --prefix web      # also real kernel proofs and warm cache
```

For an already-running isolated reference host configured with the production
extension and parity probe, `node web/test/reference.cjs` captures real extension
results and a screenshot. `REFERENCE_URL` selects that host;
`SOLIDITY_LEAN_REFERENCE_REPORT` selects the probe's JSON output in both the host
and test process. `node web/test/compare.cjs REFERENCE.png WEB.png` creates the
side-by-side image and measured diff.

Browser tests use `CHROMIUM_PATH`, `/usr/bin/chromium` if present, or Playwright's
installed Chromium. They generate screenshots and JSON in `web/artifacts/`.
See [the design, offline contract and comparison record](../docs/web-ide.md).
