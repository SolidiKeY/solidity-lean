#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
git ls-files -z --cached --others --exclude-standard | node scripts/check-trust.mjs
