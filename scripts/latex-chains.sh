#!/usr/bin/env bash
# Write every worked chain of Examples/Chains (a theorem stating a chain,
# kernel-checked) as a LaTeX fragment to <dir>/<File>/<Example>.tex, for a
# document to \input.  --macros (the default) writes the write-up's macros
# (`macros.sty`), --plain amsmath only; --opts passes the commands' options
# verbatim (docs/latex.md).  Modules default to every Examples/Chains file.
# usage: scripts/latex-chains.sh [--plain] [--opts '<options>'] <dir> [Module …]
set -euo pipefail

backend=" (macros := true)"
extra=""
while [ $# -gt 0 ]; do
  case "$1" in
    --plain) backend=""; shift ;;
    --macros) backend=" (macros := true)"; shift ;;
    --opts) extra="$extra ${2:?--opts needs an argument}"; shift 2 ;;
    *) break ;;
  esac
done
opts="$backend$extra"
if [ $# -lt 1 ]; then
  echo "usage: scripts/latex-chains.sh [--plain] [--opts '<options>'] <dir> [Module …]" >&2
  exit 2
fi
mkdir -p "$1"
dir="$(realpath "$1")"
shift

cd "$(dirname "$0")/.."
if [ $# -eq 0 ]; then
  set -- Solidity/Examples/Chains/*.lean
fi
# `Storage`, `Storage.lean` or a path to it
mods=()
for m in "$@"; do
  m="$(basename "$m" .lean)"
  [ -f "Solidity/Examples/Chains/$m.lean" ] || { echo "no Solidity/Examples/Chains/$m.lean" >&2; exit 2; }
  mods+=("$m")
done
set -- "${mods[@]}"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

{
  echo "import Solidity.Tools.Latex"
  for m in "$@"; do echo "import Solidity.Examples.Chains.$m"; done
  echo
  for m in "$@"; do
    echo "#latex_chains_files \"$dir/$m\"$opts Solidity.Examples.Chains.$m"
  done
} > "$scratch/Chains.lean"

# `lake lean`, not `lake env lean`: see scripts/latex-sol.sh
lake lean "$scratch/Chains.lean" -- --tstack=131072
