#!/usr/bin/env bash
# The fast checks: every check of lean.yml's `checks` job, none of which needs a Lean build.
# CI's `checks` job and `scripts/coord-tools/gate.sh` (touched, checkpoint, full) both run
# this one script, so a tree that passes the lane gate cannot turn `checks` red.
# Needs node >= 22, python3 and the full Git history (the H107/H112 shrink-only baselines
# compare every merge parent). Writes nothing in the tree: logs go to $TMPDIR, else the Git directory.
#
# Usage: scripts/ci/checks-fast.sh [--list] [--serial] [NAME...]
#   NAME...   run only the named checks (see --list)
#   --serial  one check at a time (default: up to CHECKS_FAST_JOBS, default nproc, at once)
# Prints "PASS|FAIL <name> <seconds>s" per check and the tail of each failing log.
# Exit 0: every check passed; 1: a check failed (a missing status record counts as failed);
# 2: usage error, or no writable storage for logs and status records.
set -uo pipefail
root=$(git rev-parse --show-toplevel) || exit 2
cd "$root" || exit 2

# name<TAB>command, in lean.yml's former step order.
checks=$(cat <<'EOF'
trust-test	node --test scripts/check-trust.test.mjs
trust	bash scripts/check-trust.sh
private-paths	bash scripts/check-private-paths.sh
evidence-files	bash scripts/check-evidence-files.sh
site-exporter	node --test scripts/site/export.test.mjs
dafny-features	node scripts/check-dafny-features.mjs
axiom-pin-tests	node --test scripts/check-axiom-pins.test.mjs tests/h62/item5/statement-graph/h112-tooling.test.mjs
w0-tooling	python3 -B tests/h62/item5/statement-graph/test_w0_tooling.py -v
doc-paths	bash scripts/check-doc-paths.sh
doc-navigation	python3 scripts/check-doc-navigation.py
axiom-pins	node scripts/check-axiom-pins.mjs
layers	node scripts/check-layers.mjs
roots	bash scripts/coord-tools/register.sh --check
fragments	bash scripts/coord-tools/fragments.sh --check
slow-partition	python3 -B tests/h55/module-times/test_slow_examples.py
solidity-features	python3 scripts/solidity-feature-audit.py --check
lean-budget-test	python3 -B scripts/lean-budget/test_check.py
lean-budget	python3 -B scripts/lean-budget/check.py
hygiene-test	python3 -B scripts/hygiene/test_check.py
checks-fast-test	python3 -B scripts/hygiene/test_checks_fast.py
hygiene	python3 -B scripts/hygiene/check.py
EOF
)

jobs=${CHECKS_FAST_JOBS:-$(nproc 2>/dev/null || echo 2)}
selected=()
# No here-strings below: bash before 5.1 backs them with a file in $TMPDIR or /tmp, which can be full.
for arg in "$@"; do
  case "$arg" in
    --list) printf '%s\n' "$checks" | cut -f1; exit 0;;
    --serial) jobs=1;;
    -*) echo "checks-fast: unknown option $arg" >&2; exit 2;;
    *) printf '%s\n' "$checks" | grep -q "^$arg	" || { echo "checks-fast: unknown check $arg" >&2; exit 2; }
       selected+=("$arg");;
  esac
done
case "$jobs" in ''|*[!0-9]*|0) echo "checks-fast: CHECKS_FAST_JOBS must be a positive integer" >&2; exit 2;; esac

# The environment CI gives these checks; a gate run without it could pass where CI fails.
if [ "$(git rev-parse --is-shallow-repository)" != false ]; then
  echo "checks-fast: shallow clone; the shrink-only baselines need full history (git fetch --unshallow)" >&2; exit 1
fi
node_major=$(node -p 'process.versions.node.split(".")[0]' 2>/dev/null) || node_major=0
if [ "${node_major:-0}" -lt 22 ]; then echo "checks-fast: node >= 22 required (have ${node_major:-none})" >&2; exit 1; fi

untracked=$(git ls-files --others --exclude-standard | wc -l)
[ "$untracked" -eq 0 ] || echo "checks-fast: warning: $untracked untracked file(s) are checked here but absent from CI's checkout; commit or remove them"

# Logs and status records: under an explicit $TMPDIR, else under Git's own directory, which
# lives beside the checkout on disk (a RAM-backed /tmp can be full: missing status records
# once turned whole runs red with empty error tails). When the caller sets no TMPDIR, the
# checks get one inside that directory too. Storage that cannot be written stops the run
# (exit 2) before any check starts; a check whose status record is missing or malformed
# fails as a storage error, never as a pass. A killed run (SIGKILL) can leave a
# checks-fast.* directory behind there; a later run does not remove it.
child_tmp=
if [ -n "${TMPDIR:-}" ]; then spool=$TMPDIR; else
  spool=$(git rev-parse --git-common-dir 2>/dev/null) && [ -n "$spool" ] && [ -d "$spool" ] && spool=$(cd "$spool" && pwd) || {
    echo "checks-fast: storage error: cannot locate the Git directory for logs; set TMPDIR" >&2; exit 2; }
fi
logs=$(mktemp -d "$spool/checks-fast.XXXXXXXX" 2>/dev/null) || {
  echo "checks-fast: storage error: cannot create a log directory in $spool; free space or set TMPDIR" >&2; exit 2; }
if [ -z "${TMPDIR:-}" ]; then child_tmp=$logs/tmp; mkdir "$child_tmp" 2>/dev/null || child_tmp=bad; fi
if [ "$child_tmp" = bad ] || ! { echo probe > "$logs/.probe" && [ "$(cat "$logs/.probe")" = probe ]; } 2>/dev/null; then
  rm -rf "$logs"; echo "checks-fast: storage error: cannot write status records in $logs; free space or set TMPDIR" >&2; exit 2
fi
rm -f "$logs/.probe"
# Interrupted: stop the running checks, then remove their logs (unless kept).
on_signal() {
  trap - INT TERM; kill $(jobs -p) 2>/dev/null; wait 2>/dev/null
  [ -n "${CHECKS_FAST_KEEP_LOGS:-}" ] || rm -rf "$logs"; exit "$1"
}
trap 'on_signal 130' INT; trap 'on_signal 143' TERM
names=()
while IFS=$'\t' read -r name cmd; do
  if [ ${#selected[@]} -gt 0 ] && ! printf '%s\n' "${selected[@]}" | grep -qx -- "$name"; then continue; fi
  names+=("$name")
  while [ "$(jobs -rp | wc -l)" -ge "$jobs" ]; do wait -n 2>/dev/null || true; done
  (
    [ -z "$child_tmp" ] || export TMPDIR=$child_tmp
    start=$(date +%s)
    bash -c "$cmd" >"$logs/$name.log" 2>&1 </dev/null; status=$?
    echo "$status $(( $(date +%s) - start ))" > "$logs/$name.status"
  ) &
done < <(printf '%s\n' "$checks")
wait

failed=0
if [ ${#names[@]} -eq 0 ]; then failed=1; echo "FAIL (no check ran: the check list could not be read)"; fi
# status_of NAME: "<exit> <seconds>" from the record, or "storage <reason>" when it is unusable.
status_of() {
  local s=() f="$logs/$1.status"
  [ -f "$f" ] || { echo "storage missing"; return; }
  read -r -a s < "$f" 2>/dev/null || { echo "storage unreadable"; return; }
  case "${s[0]:-}:${s[1]:-}" in *[!0-9:]*|:*|*:) echo "storage malformed"; return;; esac
  echo "${s[0]} ${s[1]}"
}
for name in "${names[@]}"; do
  rec=$(status_of "$name"); status=${rec%% *}; seconds=${rec#* }
  if [ "$status" = 0 ]; then echo "PASS $name ${seconds}s"
  elif [ "$status" = storage ]; then
    failed=1; echo "FAIL $name (storage error: status record $seconds in $logs; free space or set TMPDIR)"
  else failed=1; echo "FAIL $name ${seconds}s (exit $status)"; fi
done
for name in "${names[@]}"; do
  rec=$(status_of "$name")
  [ "${rec%% *}" = 0 ] && continue
  echo "--- $name: last 40 lines"
  if [ -s "$logs/$name.log" ]; then tail -n 40 "$logs/$name.log"; else echo "(no log output: storage error or a silent failure)"; fi
done
[ -n "${CHECKS_FAST_KEEP_LOGS:-}" ] && echo "checks-fast: logs in $logs" || rm -rf "$logs"
exit "$failed"
