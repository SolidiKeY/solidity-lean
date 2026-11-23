#!/usr/bin/env bash
# Done tests of a factory task step, run by gate.sh in touched mode when the factory passes them:
#   task-gate.sh scope   every file the head changes since GATE_BASE matches a glob of GATE_TASK_SCOPE
#                        (one per line), a generated root or a bookkeeping file (regenerated at merge),
#                        or a glob of GATE_TASK_ALLOW;
#   task-gate.sh goal    the @[goal] GATE_TASK_GOAL is proved: its check module pins `proved` and builds.
set -uo pipefail
root=$(git rev-parse --show-toplevel) || exit 2
cd "$root" || exit 2
case "${1:-}" in
  scope)
    [ -n "${GATE_TASK_SCOPE:-}" ] || { echo "task-gate: GATE_TASK_SCOPE is not set" >&2; exit 2; }
    base=$(git merge-base "${GATE_BASE:-origin/master}" HEAD) || exit 2
    globs=()
    while IFS= read -r g; do [ -n "$g" ] && globs+=("$g"); done <<< "$GATE_TASK_SCOPE"$'\n'"${GATE_TASK_ALLOW:-}"
    globs+=(Solidity.lean SolidityExamples.lean Bridge/SolidityBridge.lean Solidity/Goals.lean
      docs/module-map.md 'docs/module-map/*.md' docs/README.md TERRA-TODO.md scripts/g07-axiom-pins.json '*.d/*')
    outside=()
    while IFS= read -r -d '' f; do
      ok=0
      for g in "${globs[@]}"; do
        # shellcheck disable=SC2053  # the glob is meant to match
        if [[ $f == $g ]] || [[ $f == ${g%/}/* ]]; then ok=1; break; fi
      done
      [ "$ok" = 1 ] || outside+=("$f")
    done < <(git diff -z --name-only --no-renames "$base" HEAD)
    if [ "${#outside[@]}" -gt 0 ]; then
      echo "task-gate: files outside the task's write scope:" >&2
      printf '  %s\n' "${outside[@]}" >&2
      exit 1
    fi
    echo "task-gate: every changed file is inside the write scope";;
  goal)
    # The goal's check module (Solidity/Examples/Goals/<Name>.lean, H666) pins its `#roadmap_goal` line with
    # #guard_msgs; building it fails when the pinned status is not the real one.
    [ -n "${GATE_TASK_GOAL:-}" ] || { echo "task-gate: GATE_TASK_GOAL is not set" >&2; exit 2; }
    [[ $GATE_TASK_GOAL =~ ^[A-Za-z_][A-Za-z0-9_.\']*$ ]] || { echo "task-gate: invalid goal name" >&2; exit 2; }
    pin="proved $GATE_TASK_GOAL ←"
    file=$(grep -lF -- "$pin" Solidity/Examples/Goals/*.lean 2>/dev/null | head -1)
    if [ -z "$file" ]; then
      echo "task-gate: no goal check module pins '$pin' (Solidity/Examples/Goals/<Name>.lean)" >&2
      exit 1
    fi
    module=${file%.lean}; module=${module//\//.}
    lake build "$module" || { echo "task-gate: $module does not build: its pinned status is not the real one" >&2; exit 1; }
    echo "task-gate: $GATE_TASK_GOAL is proved ($module)";;
  *) echo "usage: task-gate.sh scope|goal" >&2; exit 2;;
esac
