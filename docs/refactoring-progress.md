# Shared-checkout resource policy

## Resource bounds and resuming work

Acquire `/tmp/solidity-lean-feature-groups-20261025/writer.lock` before shared
writes or Lean checks, then reread Git status. Preserve unrelated work and
other sessions' processes.

Keep heavy checks sequential.

- On the host, where systemd is available: use a hard systemd scope with
  `MemoryMax=12G` and `MemorySwapMax=0`, plus an available-memory guard
  retaining a 12 GiB host reserve. A current explicit coordinator decision may
  select a different gate cap; do not infer an exception from a previous run.
- On a cloud VM without systemd (H232, a standing rule for every lane): the VM
  is the isolation. Run heavy checks one at a time with nothing heavy alongside,
  record "no systemd scope on the cloud VM (H232)" under limitations, and do
  not ask for or wait on a scope. The host pre-gate (16 GiB, no swap) enforces
  the memory cap on every head before it can merge.

Keep at most four LSP files open. Use `LEAN_NUM_THREADS=1` and explicit `-j1` for large fresh proof checks.
Do not change committed proof budgets to fit a machine.

Keep private artifact caches on disk under `.lake/refactor-cache`, not the
RAM-backed `/tmp`. Virtual address reservations are not resident-memory usage.
A memory stop or missing object is not a passing check.

## Validation

Rebuild `Solidity.Frontend.Testing` before JavaScript regressions that request
`build:false`, and `Solidity.Tools.Upstream` before its production import checks.
Follow [contributing.md](contributing.md#checks) for current gates. Historical
refactoring attempts and timings remain in Git; they are not current validation.
