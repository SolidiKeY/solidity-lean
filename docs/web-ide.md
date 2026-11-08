# Offline browser IDE

The application is [web/](../web/). Build/package commands are in
[web/package.json](../web/package.json); runtime build tools and their pins are
in [web/tools](../web/tools/). Build the compact runtime as described in
[compact-verifier.md](compact-verifier.md), then:

```sh
SOLIDITY_BROWSER_DIRECT="$PWD/web/.lean-browser-build/direct" npm run build --prefix web
npm run build:single --prefix web
node web/test/performance.cjs --single
```

Use **File → Download Offline IDE** to save the packaged HTML. Offline use
requires completed asset preparation; incomplete preparation is a load failure.
Application source is stored in browser storage. Embedded dependency licenses
must remain in the package.

Ordinary generated-C verifier decisions are not per-result kernel
certificates. Explicit certification and the general frontend have their own
admission and trust path; successful Solidity compilation alone is not a proof.
Source/dependency changes invalidate results; late cancelled or stale responses
must not update the document.

## Performance follow-up

Reproduce observations with current scripts and exact artifact hashes. Keep
startup, compilation, native verification and kernel checking scopes separate.
Historical version-specific measurements are retained in Git.
