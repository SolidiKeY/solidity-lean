# Shared-checkout resource policy

## Resource bounds and resuming work

Acquire `/tmp/solidity-lean-feature-groups-20261025/writer.lock` before shared
writes or Lean checks, then reread Git status. Preserve unrelated work and
other sessions' processes.

Keep heavy checks sequential. Use a hard systemd scope with `MemoryMax=12G`
and `MemorySwapMax=0`, plus an available-memory guard retaining a 12 GiB host
reserve. A current explicit coordinator decision may select a different gate
cap; do not infer an exception from a previous run. Keep at most four LSP files
open. Use `LEAN_NUM_THREADS=1` and explicit `-j1` for large fresh proof checks.
Do not change committed proof budgets to fit a machine.

Keep private artifact caches on disk under `.lake/refactor-cache`, not the
RAM-backed `/tmp`. Virtual address reservations are not resident-memory usage.
A memory stop or missing object is not a passing check.

## Validation

Rebuild `Solidity.Frontend.Testing` before JavaScript regressions that request
`build:false`, and `Solidity.Tools.Upstream` before its production import checks.
Follow [contributing.md](contributing.md#checks) for current gates. Historical
refactoring attempts and timings remain in Git; they are not current validation.
