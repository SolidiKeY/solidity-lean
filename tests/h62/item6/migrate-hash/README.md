# Hash migration fixtures and evidence

The production Hash files remain unchanged pending exact-file owner coordination.
The candidate patch and bulk generated outputs live in `/workspace/migrate-hash-evidence`.
This is an isolated migration overlay, not a change of live producer ownership.

From `/workspace/migrate-hash`, holding the repository writer lock:

```sh
python3 scripts/h62/item6/migrate-hash/fixture.py
python3 scripts/h62/item6/migrate-hash/census.py
python3 scripts/h62/item6/migrate-hash/measure.py /workspace/.setup/tools/lean-4.24.0-linux /ABS/NEW/old --lake-overlay
python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /ABS/NEW/new --lake-overlay --fixture
python3 scripts/h62/item6/migrate-hash/measure.py /workspace/migrate-hash-toolchains/lean-4.35.0-linux /ABS/NEW/acceptance --fixture --extra
```

Each output path must be fresh. `measure.py` snapshots/hashes every consumed source,
uses a private cache, disables cache access for native measurements, and enforces
serial `-j1`, a 12 GiB address-space cap, a 4 GiB effective available-memory reserve,
no configured swap, and a 300 second timeout. Acquire
`/tmp/solidity-lean-feature-groups-20261025/writer.lock` around each command.
Generated module names under this test directory never enter the library roots.
The canonical native snapshots instead use identical private minimal Lake configs.

`acceptance.py /workspace/migrate-hash-evidence` audits the final saved run names
`old-lake-clean-3`, `new-lake-clean-2`, and `new-acceptance-3`; a fresh reproduction
must use those basenames in a new evidence directory. It refuses stale source
hashes, unexpected theorem axioms, input mutation, or >10% wall slowdown for any
module or the combined Hash build. It reports RSS increases for escalation.
The official release archive must match the supplied coordinator toolchain pin.

The 19 finite kernel controls supplement the 97 original universal theorem proofs;
they make no external EVM/solc claim. The inventory covers 121 named declarations
and four anonymous instances. No helper or test is registered as a production module.
Full handoff and outstanding gates: [h62-6-migrate-hash.md](../../../../docs/feature-work/h62-6-migrate-hash.md).
