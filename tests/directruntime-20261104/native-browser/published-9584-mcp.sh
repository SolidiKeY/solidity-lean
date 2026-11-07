#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LEAN_LSP_MAX_OPEN_FILES=1 LAKE_CACHE_DIR=
export LEAN_MCP_SOCKDIR="$PWD/.lake/native-browser-9584-mcp-sockets"
mkdir -p "$LEAN_MCP_SOCKDIR" .lake/native-browser-mcp-bin
cat > .lake/native-browser-mcp-bin/lake <<'SHIM'
#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == serve ]]; then
 exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake "$@" -j1
fi
exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake "$@"
SHIM
chmod +x .lake/native-browser-mcp-bin/lake
export PATH="$PWD/.lake/native-browser-mcp-bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
trap 'python3 scripts/coord-tools/lean-mcp stop' EXIT
python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/Shared/Scope.lean
python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/ControlTuple/IntrinsicControls.lean
