# Historical validation wrappers

These twenty source/configuration snapshots are copied byte for byte from the
sealed environment evidence archive. The repository-relative
[`wrapper-index.json`](../wrapper-index.json) records each archive member, size
and SHA256. They cover build orchestration, per-file diagnostics, compiler
provenance, native/browser controls, closure auditing and evidence packaging.
The generic harnesses they call remain at their original tracked paths.

These are review artifacts, **not a replay launcher**. Original paths, assertions,
output ownership and historical setup failures are preserved. In particular,
`checks.sh` stopped at the first candidate-exclusion setup failure;
`remaining-checks.sh` records the continuation after correcting the private
output path. Its `|| true` retains the browser-negative failure receipt and
continues independent checks; it does not turn that gate into a pass.
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
