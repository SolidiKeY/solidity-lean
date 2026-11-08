# Offline IDE

The production build is static. Save **File → Download Offline IDE** and wait
for complete asset preparation before disconnecting. User source stays in
browser storage. Preserve packaged dependency licenses.

Ordinary generated-C decisions are not fresh kernel certificates. Explicit
certification and legacy general-frontend builds have separate requirements;
Solidity compilation alone is not a proof. Unsupported, cancelled, stale and
failed checks must remain distinguishable.

## Build and test

Build a matching runtime first using
[compact-verifier.md](../docs/compact-verifier.md). From the repository root:

```sh
npm ci --prefix web
SOLIDITY_BROWSER_DIRECT="$PWD/web/.lean-browser-build/direct" npm run build --prefix web
npm run build:single --prefix web
npm run test:single --prefix web
```

[package.json](package.json) and [web/test](test/) define the other maintained
commands. Browser tests use `CHROMIUM_PATH` or an installed Chromium.
Follow [resource bounds](../docs/refactoring-progress.md#resource-bounds-and-resuming-work)
for runtime builds. Build artifacts and checksums must match before deployment.
The optional native comparison server is for development and is excluded from
the static package.
