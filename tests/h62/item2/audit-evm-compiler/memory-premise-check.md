# Checking MemoryPremiseAudit under the repository lakefile

`tests` is intentionally not a registered Lake library. `lake lean` attempts
Lake target resolution for its imports and can report unknown module prefix
`tests`. Use `lake env` and compile the two audit helpers explicitly:

```sh
LEAN_NUM_THREADS=1 lake env python3 scripts/h62/item2/audit-evm-compiler/check_memory_premises.py --evidence /tmp/h62-memory-premise-check
```

Choose a new or empty evidence directory for each run; reused output is rejected
before any receipt is changed. Run from the repository root while holding the
repository writer lock. The runner checks KeySort, then compiles JointImpossible, JointWitness and
MemoryPremiseAudit serially with `-j1` into a fresh evidence-directory library.
That library precedes other Lean search paths. No alternate lakefile, central
registration, prebuilt audit helpers or theorem change is required.

Prerequisite: the unchanged core imports must already be built and available
on Lake's search path. If Lake fetched them into its content cache, materialize
them using `python3 scripts/ci/restore-lake-artifacts.py` after the normal core
build. The runner does not claim to build the core or complete full-library gates.
A worker with a validated private core library may prepend its directory to
`LEAN_PATH` before `lake env`; the saved summary records that exact search path.
The coordinator can use its own materialized core build without a VM-specific path.
