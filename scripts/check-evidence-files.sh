#!/usr/bin/env bash
# Lane evidence (receipts, handoffs, provenance, checksum manifests, resource and validation
# records) belongs in the private coordination repository, not in this public one: lanes archive
# it with `scripts/coord-tools/coord-evidence` and cite the printed path. Under tests/ and
# Bridge/tests/ this rejects
#   - any non-Lean file in an evidence/, handoff/, retirement/, receipts/ or resumed/ directory;
#   - data files (not code) whose name marks them as receipts, handoffs, provenance, relays,
#     owner tickets/requests, validation summaries, resource records or sha256 manifests.
# Real fixtures read by a checker keep ordinary names; add a true exception to `allow` with why.
set -euo pipefail
cd "$(dirname "$0")/.."

allow=(
  # keeps the directory that Solidity.Frontend.NumericLiteralProofs.{Audit,Fixtures} write into at build time
  tests/sol-numeric-literals/evidence/.gitignore
)

scope='^(tests|Bridge/tests)/'
dirs='(^|/)(evidence|handoff|h82-handoff|retirement|receipts?|resumed)/'
names='(^|/)[^/]*(receipt|RECEIPT|HANDOFF|handoff|SHA256SUMS|provenance|PROVENANCE|owner-ticket|OWNER-TICKET|owner-request|relay|validation-summary|resource)[^/]*$|[.]sha256$'
code='[.](lean|py|mjs|js|cjs|sh|ts)$'

hits=$(git ls-files --cached --others --exclude-standard | grep -E "$scope" | grep -vE '[.]lean$' \
  | awk -v d="$dirs" -v n="$names" -v c="$code" '$0 ~ d || ($0 ~ n && $0 !~ c)' \
  | grep -vxF -f <(printf "%s\n" "${allow[@]}" | grep -v "^#" | sed "/^$/d") || true)
if [ -n "$hits" ]; then
  printf '%s\n' "$hits" | sed -n '1,40p'
  echo "evidence-files: $(printf '%s\n' "$hits" | wc -l) evidence file(s) in the public tree;" \
    "archive them with scripts/coord-tools/coord-evidence and remove them from the branch" >&2
  exit 1
fi
echo "evidence-files: OK"
