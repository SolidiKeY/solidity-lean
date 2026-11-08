#!/usr/bin/env bash
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
git status --short
python3 tests/directruntime-20261104/native-browser/readbounds/serial-build.py /workspace/scratch/readbounds-serial-plan-execute.json --expected-sha256 3c14c1b2bc7328258d8133663e10d9bb842b14da9e54b2611b73a679e99eb59d --run /workspace/scratch/browser-chain/readbounds-6513/dependency-targets
