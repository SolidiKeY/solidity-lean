#!/usr/bin/env bash
set -euo pipefail
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
export NATIVE_BROWSER_NATIVE_OUTPUT="$PWD/.lake/native-browser-readbounds-6513/native"
timeout --kill-after=10s 300s bash tests/directruntime-20261104/native-browser/hardening-native-build.sh
