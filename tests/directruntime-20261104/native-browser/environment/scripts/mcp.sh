#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LEAN_LSP_MAX_OPEN_FILES=1 LAKE_CACHE_DIR=
export LEAN_MCP_SOCKDIR="$PWD/.lake/nb-env-mcp"
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
python3 scripts/coord-tools/lean-mcp diag Solidity/KeySort.lean
python3 scripts/coord-tools/lean-mcp diag Solidity/Tools/DirectRuntime.lean
python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/Shared/Intrinsic.lean
python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/Shared/Compose.lean

python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/Shared/Translate.lean
python3 scripts/coord-tools/lean-mcp diag tests/directruntime-20261104/native-browser/fixed-byte/MarkerControls.lean

python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/ControlTuple/Adapter.lean

python3 scripts/coord-tools/lean-mcp diag tests/directruntime-20261104/native-browser/address/MarkerIdentityControls.lean

python3 scripts/coord-tools/lean-mcp diag Solidity/Tools/SourceCounterexample.lean

python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/Shared/Boundary.lean
python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/Shared/Scope.lean
python3 scripts/coord-tools/lean-mcp diag Solidity/Frontend/ExecutableAst/Memory/Reader.lean
python3 scripts/coord-tools/lean-mcp diag tests/directruntime-20261104/native-browser/environment/MetadataControls.lean
