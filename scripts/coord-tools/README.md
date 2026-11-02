# Coordinator tools

gate.sh runs from the current checkout: `gate.sh per-file FILE...`, `gate.sh touched`, `gate.sh checkpoint`, or `gate.sh full`. It writes one status line per gate and `gates.tsv` plus individual logs under `GATE_LOGS` (default a temporary `coord-gates` directory). `GATE_BASE` selects the touched comparison base (default `origin/master`). Exit 0 means all gates passed, 1 means at least one failed, and 2 means invalid usage or setup.

`seal.sh DIR [BASE]` creates a bundle of BASE..HEAD (default `origin/master`), a manifest, and SHA256SUMS, then verifies the seal. `seal.sh --verify DIR` checks file inventory, hashes, bundle tip and pack integrity. It uses `TMPDIR` for the temporary indexing repository. Exit 0 indicates success; nonzero indicates invalid usage, an empty range, or verification failure.
