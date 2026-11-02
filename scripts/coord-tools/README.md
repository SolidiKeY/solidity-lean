# Coordinator tools

gate.sh runs from the current checkout: `gate.sh per-file FILE...`, `gate.sh touched`, `gate.sh checkpoint`, or `gate.sh full`. It writes one status line per gate and `gates.tsv` plus individual logs under `GATE_LOGS` (default a temporary `coord-gates` directory). `GATE_BASE` selects the touched comparison base (default `origin/master`). Exit 0 means all gates passed, 1 means at least one failed, and 2 means invalid usage or setup.
