#!/bin/bash
set -eu
case " $* " in
  *' serve '*|*' lean '*) exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f /workspace/solidity-lean/.world-bounded.toml "$@" -j1 ;;
  *) exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f /workspace/solidity-lean/.world-bounded.toml "$@" ;;
esac
