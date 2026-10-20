#!/usr/bin/env bash
# Print a Solidity function's obligation as LaTeX; with --derivation, the
# derivation the strategy finds from it.  --macros writes the write-up's
# macros (`macros.sty`); --opts passes the commands' options verbatim, e.g.
# --opts '(labels := tag) (past := false)' (docs/latex.md).
# --program checks a refined program trace; --json writes its checked pairs.
# usage: scripts/latex-sol.sh [--derivation|--program|--json] [--macros] [--reads 'r, ...'] [--opts '<options>'] <file.sol> <Contract.function>
set -euo pipefail

kind=obligation
opts=""
reads=""
while [ $# -gt 0 ]; do
  case "$1" in
    --derivation) kind=derivation; shift ;;
    --program) kind=program; shift ;;
    --json) kind=program_trace_json; shift ;;
    --macros) opts="$opts (macros := true)"; shift ;;
    --reads) reads=" reads [${2:?--reads needs an argument}]"; shift 2 ;;
    --opts) opts="$opts ${2:?--opts needs an argument}"; shift 2 ;;
    *) break ;;
  esac
done
if [ $# -ne 2 ] || [[ ! "$2" =~ ^[^.]+\.[^.]+$ ]]; then
  echo "usage: scripts/latex-sol.sh [--derivation|--program|--json] [--macros] [--reads 'r, ...'] [--opts '<options>'] <file.sol> <Contract.function>" >&2
  exit 2
fi
if [ -n "$reads" ] && [ "$kind" != program ] && [ "$kind" != program_trace_json ]; then
  echo "--reads requires --program or --json" >&2
  exit 2
fi
sol="$(realpath "$1")"
contract="${2%.*}"
fn="${2##*.}"
base="$(basename "$sol" .sol)"

cd "$(dirname "$0")/.."
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
module=Solidity.Tools.LatexSolkey
command="#latex_${kind}_file"
case "$kind" in
  program) module=Solidity.Tools.ProgramTrace ;;
  program_trace_json) module=Solidity.Tools.ProgramTrace; command="#program_trace_json_file" ;;
esac

# hash 0x0 is a placeholder: solc-ast.mjs writes the fixture's hash in
cat > "$scratch/Latex.lean" <<LEAN
import $module

solc_import "$base.ast.json" hash 0x0 as SolLatex.«$contract»

$command "$scratch/out.tex"$opts$reads SolLatex.«$contract».«$fn»
LEAN

node scripts/solc-ast.mjs --source "$sol" --out "$scratch/$base.ast.json" \
  --wrapper "$scratch/Latex.lean" >&2

# `lake lean` builds the imports and hands `lean` their artifacts by path
# (`--setup`).  Not `lake env lean`: with the artifact cache
# (`enableArtifactCache`) a module fetched from the cache is not copied to
# `.lake/build/lib`, so `LEAN_PATH` there can hold stale or missing `.olean`s,
# and the interpreter then misses code an import needs ("unknown declaration
# 'Solidity.Frontend.ImportRow.declName'").
status=0
diag="$(lake lean "$scratch/Latex.lean" -- --tstack=131072 2>&1)" || status=$?
if [ -n "$diag" ]; then printf '%s\n' "$diag" >&2; fi
[ "$status" -eq 0 ] || exit "$status"
cat "$scratch/out.tex"
