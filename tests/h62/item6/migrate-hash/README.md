# Hash migration fixtures and evidence

The production Hash migration patch is applied under explicit coordinator directory-writer authorization.
The candidate patch and bulk generated outputs live in `/workspace/migrate-hash-evidence`.
This is an isolated migration overlay, not a change of live producer ownership.

From `/workspace/migrate-hash`, holding the repository writer lock:

```sh
python3 scripts/h62/item6/migrate-hash/fixture.py
python3 scripts/h62/item6/migrate-hash/census.py
python3 scripts/h62/item6/migrate-hash/measure.py /workspace/.setup/tools/lean-4.24.0-linux /ABS/NEW/old --lake-overlay --pinned-base
python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /ABS/NEW/new --lake-overlay --fixture
python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /ABS/NEW/acceptance --fixture --extra
python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /ABS/NEW/production --production-extra
```

Each output path must be fresh. `measure.py` snapshots/hashes every consumed source,
uses a private cache, disables cache access for native measurements, and enforces
serial `-j1`, a 12 GiB address-space cap, a 4 GiB effective available-memory reserve,
no configured swap, and a 300 second timeout. Acquire
`/tmp/solidity-lean-feature-groups-20261025/writer.lock` around each command.
Generated module names under this test directory never enter the library roots.
The canonical native snapshots instead use identical private minimal Lake configs.

`acceptance.py /workspace/migrate-hash-evidence` audits the final saved run names
`old-lake-clean-3`, `new-lake-clean-2`, `new-acceptance-3`, and `new-production-acceptance-1`; a fresh reproduction
must use those basenames in a new evidence directory. It refuses stale source
hashes, unexpected theorem axioms and input mutation. It records module time/RSS
growth without stopping the lane; matched full-build growth is a root cut-over
escalation. Production acceptance is in `new-production-acceptance-1`.
The official release archive must match the supplied coordinator toolchain pin.

The 19 finite kernel controls supplement the 97 original universal theorem proofs;
they make no external EVM/solc claim. The inventory covers 121 named declarations
and four anonymous instances. No helper or test is registered as a production module.
Full handoff and outstanding gates: [h62-6-migrate-hash.md](../../../../docs/feature-work/h62-6-migrate-hash.md).

For a clean full-repository baseline/probe use `full_measure.py TOOLCHAIN NEW_OUTPUT`
(and `--migrated` for the new arm). It creates a detached pinned private worktree,
builds the entire 6,389-module closure with both `+module:o` and `+module:o.noexport` serially, then invokes the
unchanged `run-lean.sh` after serial executable linking. Module timeout is 300s; final aggregate gate timeout is
1800s. Both arms have identical private package configuration and fresh caches.
The new full probe is blocked outside Hash at `Solidity.Syntax.Raw`; no full-build
comparison is available. The saved old baseline terminated at its 300s native
command cap after 18 / 6389 modules; no active controller remains. Inspect
`/workspace/migrate-hash-evidence/baseline-controller.json` and its output directory
and the preserved summary before root-gate disposition. No restart or budget
change is authorized by the latest relay. Do not duplicate or terminate another owner.

For H70 static provenance, `python3 scripts/h62/item6/migrate-hash/source_provenance.py`
verifies the immutable exact 2a18 commit package without invoking Lean, applying
source or restarting any controller. The manifest and source bundle live in
`/workspace/migrate-hash-evidence/source-provenance-2a18afcdb`; this differs from
the latest receipt-head bundle. Preserve root-gate holds and await coordinator
consumption; static bundle verification is not a full gate or cut-over approval.
