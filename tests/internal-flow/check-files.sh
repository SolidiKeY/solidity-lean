#!/usr/bin/env bash
set -euo pipefail
out=${1:?absolute evidence directory required}
# One genuine Lake environment; every source still gets a fresh Lean CLI process.
exec lake env node tests/internal-flow/raw-source-driver.mjs "$out"
