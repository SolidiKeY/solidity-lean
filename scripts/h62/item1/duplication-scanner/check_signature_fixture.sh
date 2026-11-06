#!/usr/bin/env bash
# Compile and inspect isolated fixtures. This is not a provenance attestation.
set -euo pipefail

if [[ $# -ne 1 || "$1" != /* ]]; then
  echo "usage: $0 ABSOLUTE_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../../../.." && pwd)"
source_dir="$repo_root/tests/h62/item1/duplication-scanner"
mkdir -p "$1"
work="$(mktemp -d "$1/h62-signature.XXXXXXXX")"
trap 'printf "signature fixture evidence: %s\n" "$work"' EXIT

mkdir -p /tmp/solidity-lean-feature-groups-20261025
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock -x 9
cd "$repo_root"
git status --short --branch > "$work/git-status.log"
git rev-parse HEAD > "$work/git-head.log"
command -v lake >/dev/null
export LEAN_NUM_THREADS=1
export LEAN_PATH="$work"
cg_rel="$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup)"
[[ "$cg_rel" == "/" ]] || { echo "nested or missing unified cgroup is unsupported" >&2; exit 1; }
cg_dir="/sys/fs/cgroup"

guard() {
  local host_available host_swap cg_max cg_current swap_max swap_current
  local cg_available usable cap current_limit
  host_available="$(awk '/MemAvailable:/ {print $2}' /proc/meminfo)"
  host_swap="$(awk '/SwapTotal:/ {print $2}' /proc/meminfo)"
  [[ -r "$cg_dir/memory.max" && -r "$cg_dir/memory.current" &&
     -r "$cg_dir/memory.swap.max" && -r "$cg_dir/memory.swap.current" ]] || {
    echo "cgroup memory controls unavailable" >&2
    return 1
  }
  read -r cg_max < "$cg_dir/memory.max"
  read -r cg_current < "$cg_dir/memory.current"
  read -r swap_max < "$cg_dir/memory.swap.max"
  read -r swap_current < "$cg_dir/memory.swap.current"
  [[ "$host_available" =~ ^[0-9]+$ && "$host_swap" =~ ^[0-9]+$ &&
     "$cg_max" =~ ^[0-9]+$ && "$cg_current" =~ ^[0-9]+$ &&
     "$swap_current" =~ ^[0-9]+$ && ( "$swap_max" == max || "$swap_max" =~ ^[0-9]+$ ) ]] || {
    echo "unbounded or malformed resource controls" >&2
    return 1
  }
  cg_available=$(((cg_max - cg_current) / 1024))
  [[ "$host_available" -gt 4194304 && "$cg_available" -gt 4194304 &&
     "$swap_current" -eq 0 && ( "$host_swap" -eq 0 || "$swap_max" == 0 ) ]] || {
    echo "resource guard failed: host_available_kib=$host_available cgroup_available_kib=$cg_available host_swap_kib=$host_swap cgroup_swap_max=$swap_max cgroup_swap_current=$swap_current" >&2
    return 1
  }
  usable="$cg_available"
  (( host_available >= usable )) || usable="$host_available"
  cap=$((usable - 4194304))
  (( cap <= 12582912 )) || cap=12582912
  current_limit="$(ulimit -v)"
  if [[ "$current_limit" == unlimited || "$current_limit" -gt "$cap" ]]; then
    ulimit -v "$cap"
  fi
  printf 'host_available_kib=%s cgroup_available_kib=%s cgroup_max_bytes=%s cgroup_current_bytes=%s host_swap_kib=%s cgroup_swap_max=%s cgroup_swap_current=%s virtual_limit_kib=%s\n' \
    "$host_available" "$cg_available" "$cg_max" "$cg_current" "$host_swap" "$swap_max" "$swap_current" "$(ulimit -v)" >> "$work/resources.log"
}

run_check() {
  local label="$1" status
  shift
  guard
  if timeout 120 "$@" > "$work/$label.log" 2>&1; then
    printf '%s exit=0\n' "$label" >> "$work/status.log"
  else
    status=$?
    printf '%s exit=%s\n' "$label" "$status" >> "$work/status.log"
    cat "$work/$label.log" >&2
    return "$status"
  fi
}

{
  lake --version
  lake env lean --version
} > "$work/versions.log"
[[ "$(lake env lean --short-version)" == "4.24.0" ]] || {
  echo "unexpected Lean version" >&2
  exit 1
}

lean_command="$(lake env which lean)"
lake_command="$(command -v lake)"
sha256sum "$lean_command" "$lake_command" "$repo_root/lean-toolchain" \
  "$script_dir/check_signature_fixture.sh" "$script_dir/observe_signature_environment.py" \
  "$source_dir/SignatureFingerprint.lean" "$source_dir/SignatureEnvironment.lean" \
  "$source_dir/SignatureEnvironmentProbe.lean" "$source_dir/SignatureObservedConsumer.lean" \
  "$source_dir/SignatureConsumer.lean" "$source_dir/SignatureMissing.lean" "$source_dir/SignatureAxioms.lean" \
  "$source_dir/check_signature_records.py" "$source_dir/signature-records.expected.jsonl" > "$work/prebuild.sha256"

run_check build lake env lean -j1 --tstack=131072 --root="$source_dir" \
  -o "$work/SignatureFingerprint.olean" "$source_dir/SignatureFingerprint.lean"

run_check environment_build lake env lean -j1 --tstack=131072 --root="$source_dir" \
  -o "$work/SignatureEnvironment.olean" "$source_dir/SignatureEnvironment.lean"

search_path="$(lake env printenv LEAN_PATH)"
IFS=: read -r -a search_dirs <<< "$search_path"
for module in SignatureFingerprint SignatureEnvironment; do
  matches=0
  for dir in "${search_dirs[@]}"; do
    if [[ -f "$dir/$module.olean" ]]; then
      matches=$((matches + 1))
      [[ "$(realpath "$dir/$module.olean")" == "$work/$module.olean" ]] || {
        echo "shadowing $module.olean: $dir" >&2
        exit 1
      }
    fi
  done
  [[ "$matches" -eq 1 ]] || { echo "expected exactly one $module artifact" >&2; exit 1; }
done

sha256sum -c "$work/prebuild.sha256" > "$work/prebuild-after-build.log"
extra_args=(
  --extra "lean_command_path=$lean_command"
  --extra "lake_command_path=$lake_command"
  --extra "lean_toolchain=$repo_root/lean-toolchain"
  --extra "fingerprint_source=$source_dir/SignatureFingerprint.lean"
  --extra "environment_source=$source_dir/SignatureEnvironment.lean"
  --extra "probe_source=$source_dir/SignatureEnvironmentProbe.lean"
  --extra "consumer_source=$source_dir/SignatureObservedConsumer.lean"
  --extra "record_checker=$source_dir/check_signature_records.py"
  --extra "expected_records=$source_dir/signature-records.expected.jsonl"
  --extra "snapshot_tool=$script_dir/observe_signature_environment.py"
  --extra "driver=$script_dir/check_signature_fixture.sh"
  --extra "fingerprint_olean=$work/SignatureFingerprint.olean"
  --extra "environment_olean=$work/SignatureEnvironment.olean"
  --extra "checkout_head=$work/git-head.log"
  --extra "checkout_status=$work/git-status.log"
)
run_check probe_before lake env lean -j1 --tstack=131072 --root="$source_dir" \
  "$source_dir/SignatureEnvironmentProbe.lean"
run_check snapshot_before python3 -B "$script_dir/observe_signature_environment.py" capture \
  "$work/probe_before.log" "${extra_args[@]}"
run_check observed_consumer lake env lean -j1 --tstack=131072 --root="$source_dir" \
  "$source_dir/SignatureObservedConsumer.lean"
run_check probe_after lake env lean -j1 --tstack=131072 --root="$source_dir" \
  "$source_dir/SignatureEnvironmentProbe.lean"
run_check snapshot_after python3 -B "$script_dir/observe_signature_environment.py" capture \
  "$work/probe_after.log" "${extra_args[@]}"
run_check observation_verify python3 -B "$script_dir/observe_signature_environment.py" verify \
  "$work/snapshot_before.log" "$work/probe_before.log" "$work/observed_consumer.log" \
  "$work/probe_after.log" "$work/snapshot_after.log"

run_check consumer lake env lean -j1 --tstack=131072 --root="$source_dir" \
  "$source_dir/SignatureConsumer.lean"
run_check missing lake env lean -j1 --tstack=131072 --root="$source_dir" \
  "$source_dir/SignatureMissing.lean"
run_check axioms lake env lean -j1 --tstack=131072 --root="$source_dir" \
  "$source_dir/SignatureAxioms.lean"
python3 -B "$source_dir/check_signature_records.py" "$work/consumer.log" > "$work/records.log"
sha256sum -c "$work/prebuild.sha256" > "$work/prebuild-after-run.log"
sha256sum "$script_dir/check_signature_fixture.sh" "$source_dir/SignatureFingerprint.lean" "$source_dir/SignatureConsumer.lean" \
  "$source_dir/SignatureMissing.lean" "$source_dir/SignatureAxioms.lean" "$source_dir/check_signature_records.py" \
  "$source_dir/SignatureEnvironment.lean" "$source_dir/SignatureEnvironmentProbe.lean" "$source_dir/SignatureObservedConsumer.lean" \
  "$script_dir/observe_signature_environment.py" \
  "$source_dir/signature-records.expected.jsonl" "$work/SignatureFingerprint.olean" "$work/SignatureEnvironment.olean" \
  "$work/environment_build.log" "$work/probe_before.log" "$work/snapshot_before.log" \
  "$work/observed_consumer.log" "$work/probe_after.log" "$work/snapshot_after.log" "$work/observation_verify.log" \
  "$work/git-head.log" "$work/prebuild.sha256" "$work/prebuild-after-build.log" "$work/prebuild-after-run.log" "$work/versions.log" "$work/build.log" "$work/consumer.log" "$work/missing.log" \
  "$work/axioms.log" "$work/records.log" "$work/status.log" "$work/git-status.log" "$work/resources.log" > "$work/SHA256SUMS"
cat "$work/status.log" "$work/records.log"
