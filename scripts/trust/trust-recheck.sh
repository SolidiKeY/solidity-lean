#!/usr/bin/env bash
# Fresh kernel replay guards against trusting deserialized declaration bodies.
# lean4checker uses Lean's kernel; this is not a second kernel implementation.
# Dependency installation is an explicit opt-in, never a core Lake dependency.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export LEAN_NUM_THREADS=1
revision=da26eb05e9959402afcb9bd6dfe5dc4f700f70d6
checker_dir=${TRUST_CHECKER_DIR:-"$PWD/.lake/trust-checker-$revision"}
if [[ ! -d "$checker_dir/.git" ]]; then
  if [[ ${TRUST_INSTALL_CHECKER:-0} != 1 ]]; then
    echo "A04 blocked: approved lean4checker v4.24.0 ($revision) dependency unavailable; set TRUST_INSTALL_CHECKER=1 only after dependency authorization" >&2
    exit 2
  fi
  if [[ -e "$checker_dir" ]]; then echo 'refusing to overwrite an existing checker path' >&2; exit 2; fi
  git init -q "$checker_dir"
  git -C "$checker_dir" fetch --depth=1 https://github.com/leanprover/lean4checker.git "$revision"
  git -C "$checker_dir" checkout --detach FETCH_HEAD
fi
[[ $(git -C "$checker_dir" rev-parse HEAD) == "$revision" ]] || { echo 'checker revision mismatch' >&2; exit 2; }
[[ -z $(git -C "$checker_dir" status --porcelain) ]] || { echo 'checker sources are dirty' >&2; exit 2; }
cmp lean-toolchain "$checker_dir/lean-toolchain" || { echo 'checker toolchain mismatch' >&2; exit 2; }
lean --version
lake --version
bash scripts/check-trust.sh
node scripts/trust/trust-closure.mjs --source-ceilings
(
  cd "$checker_dir"
  lake build lean4checker
)
checker="$checker_dir/.lake/build/bin/lean4checker"
[[ -x "$checker" ]] || { echo 'checker binary unavailable' >&2; exit 2; }
echo "checker-source: https://github.com/leanprover/lean4checker.git $revision"
sha256sum "$checker"
# --fresh includes theorem proofs and their transitive dependencies, a superset
# of A01's definition/type closure. Replaying only A01's list would be unsound.
trust_overlay=$(node scripts/trust/trust-replay-inputs.mjs)
trust_sysroot=$(lean --print-prefix)
sha256sum "$trust_overlay/MANIFEST.json"
# Override Lake's normal project paths after `lake env` constructs its context.
# Unlisted project objects cannot silently fall back to stale .lake/build files.
timeout "${TRUST_REPLAY_TIMEOUT:-300}" lake env env \
  LEAN_PATH="$trust_overlay:$trust_sysroot/lib/lean" "$checker" --fresh Solidity.Theorems
echo 'TRUST_FRESH_KERNEL_REPLAY_PASS'
