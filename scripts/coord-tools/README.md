# Coordinator tools

gate.sh runs from the current checkout: `gate.sh per-file FILE...`, `gate.sh touched`, `gate.sh checkpoint`, or `gate.sh full`. It writes one status line per gate and `gates.tsv` plus individual logs under `GATE_LOGS` (default a temporary `coord-gates` directory). `GATE_BASE` selects the touched comparison base (default `origin/master`). Exit 0 means all gates passed, 1 means at least one failed, and 2 means invalid usage or setup.

`seal.sh DIR [BASE]` creates a bundle of BASE..HEAD (default `origin/master`), a manifest, and SHA256SUMS, then verifies the seal. `seal.sh --verify DIR` checks file inventory, hashes, bundle tip and pack integrity. It uses `TMPDIR` for the temporary indexing repository. Exit 0 indicates success; nonzero indicates invalid usage, an empty range, or verification failure.

`handoff.sh [NOTES-FILE]` writes HANDOFF.md and CLOUDVM-RESULT.json and prints the JSON result. Set `HANDOFF_OUT` for the output directory, `HANDOFF_BATCH`, `HANDOFF_SLUG`, `HANDOFF_BASE` (default origin/master), `HANDOFF_STATUS` (default partial), `HANDOFF_CHECKPOINTS` (comma-separated name=status), and `HANDOFF_GATES` (colon-separated gate log directories). Exit 0 means written; nonzero means invalid inputs or a refused done status. Done requires passing gates and a clean tracked tree.

`disk.sh [--free]` reports free disk and cgroup memory. `--free`, or free space below `DISK_MIN_FREE_BYTES` (default 2 GiB), removes exited containers, extra worktree builds, and older verified seals only. Set `DISK_REPO`, `DISK_CGROUP`, and colon-separated `DISK_EVIDENCE_ROOTS` to choose the repository, cgroup and evidence roots. Exit 0 means the report/cleanup completed; nonzero means invalid usage or an error.

`try-tactics.sh MODULE GOAL [CANDIDATE...]` checks the standard tactics followed by supplied candidates against a proposition file or the type of a declaration name. It writes scratch files outside the checkout and prints one result and log path per attempt; `TMPDIR` chooses their parent. `TRY_TACTICS_BACKEND` selects the backend (lake, mcp, or auto). Exit 0 means at least one passed, 1 means none passed, and 2 means invalid usage.
