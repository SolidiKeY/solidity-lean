# Historical validation wrappers

The twenty indexed source/configuration snapshots are copied byte for byte from
the sealed environment evidence archive. Original checks.sh and
remaining-checks.sh are now under historical/; the other indexed paths are unchanged. The repository-relative
[`wrapper-index.json`](../wrapper-index.json) records each archive member, size
and SHA256. They cover build orchestration, per-file diagnostics, compiler
provenance, native/browser controls, closure auditing and evidence packaging.
The generic harnesses they call remain at their original tracked paths.

These are review artifacts, **not a replay launcher**. Original paths, assertions,
output ownership and historical setup failures are preserved. In particular,
`historical/checks.sh` stopped at the first candidate-exclusion setup failure;
`historical/remaining-checks.sh` records the continuation after correcting the
private output path. Their original blanket bypass is preserved only for
historical inspection. The maintained checks.sh and remaining-checks.sh copies
now invoke ../known-stack-continuation.py after a nonzero browser gate. It
permits continuation only for the exact known invariantCountsToBound source
stack overflow with all sibling controls healthy, matching binary/request
identities, retained source/AST bytes and a healthy bounded runner. The failing
wire/fixture hashes are pinned to the reviewed receipt; a new fixture identity
requires review rather than automatic continuation. Any other failure stops the script.
Even when continuation is permitted, the browser gate remains FAIL and the
stack/performance STOPs stay open.
Packaging/manifest generators describe their historical capture and must not be
used to overwrite sealed outputs or current documentation.

No script here was run for this preservation increment. The scripts require the
original prepared VM, private setup shims, pinned toolchains, fixture journals
and bounded execution context. They retain fixed `.lake`/scratch paths and are
not portable execution recipes. Do not run a stopped benchmark unchanged.
Every heavy check still requires the writer lock, 12 GiB/no swap, one job,
`LEAN_NUM_THREADS=1`, `-j1` and the required outer memory reserve.

For read-only source verification from any checkout location, run:

```sh
python3 tests/directruntime-20261104/native-browser/environment/verify-wrapper-index.py
```

To additionally verify the original wrapper members against the sealed archive,
add `--archive /path/to/evidence.tar.gz`. This reads files without executing a
wrapper, extracting an archive, loading Lean or contacting a service.

The index also records the sealed evidence, runtime and incremental-cache
archive hashes and exact original-VM handoff locator. H71 relayed the handoff
metadata; **bulk retrieval and recipient inspection remain coordinator-pending**.
These locators are not public download links. H41 prohibits VM `ship-cache.sh`.
Original failures, pending storage cases, timing STOPs and proof boundaries
remain in the qualification manifest.

The strict continuation guard also needs the six retained baseline source files
under docs/benchmarks/directruntime-2026-11-04/before/existing-controls (H44
external data), the tracked ClosedSpecs source and the actual retained input
source/AST files. Missing inputs fail closed; they are not regenerated here.
