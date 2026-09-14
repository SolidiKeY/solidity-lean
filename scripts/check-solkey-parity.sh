#!/usr/bin/env bash
# Parity press button: elaborate the ported solkey corpus and compare the
# per-obligation verdicts against tests/solkey/expected.tsv.
#
# The corpus (Solidity/Examples/Solkey/*.lean, generated
# by scripts/solkey-port.mjs) is one `theorem … := by sol_wp` per solkey
# function. Each module is elaborated once with `lake env lean --json`,
# and every diagnostic is attributed to the theorem whose span contains
# it — so one Lean invocation per contract yields a verdict per
# obligation, rather than one invocation per obligation.
#
#   ./scripts/check-solkey-parity.sh              check against expected.tsv
#   ./scripts/check-solkey-parity.sh --update     rewrite expected.tsv from
#                                                 the observed verdicts
#   ./scripts/check-solkey-parity.sh --only Solc* elaborate just these
#                                                 contracts (iteration loop)
#
# Modules are elaborated in parallel: they are independent files over the
# same cached dependencies, so wall time is the slowest module rather than
# their sum.
#
# Statuses: proved (sol_wp closes it) | open (it does not) | unsupported
# (no theorem: the construct is outside the fragment, reason in the note).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

UPDATE=0
ONLY=""
while [ $# -gt 0 ]; do
  case "$1" in
    --update) UPDATE=1 ;;
    --only) shift; ONLY="$1" ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

# Dependencies only — `sol_wp` and what it needs, not the whole library:
# the corpus modules are elaborated one by one below, so that a failing
# theorem does not abort the run.
lake build Solidity.Wp.Verifier >/dev/null

UPDATE=$UPDATE ONLY=$ONLY python3 - <<'PYTHON'
import json, os, re, subprocess, sys, collections, fnmatch
from concurrent.futures import ThreadPoolExecutor

EXPECTED = "tests/solkey/expected.tsv"
CORPUS = "Solidity/Examples/Solkey"
update = os.environ["UPDATE"] == "1"
only = os.environ.get("ONLY") or ""

rows = []
for line in open(EXPECTED):
    line = line.rstrip("\n")
    if not line or line.startswith("#"):
        continue
    parts = line.split("\t")
    parts += [""] * (5 - len(parts))
    rows.append(parts[:5])

contracts = []
for _, contract, _, _, _ in rows:
    if contract not in contracts:
        contracts.append(contract)
if only:
    contracts = [c for c in contracts if fnmatch.fnmatch(c, only)]
    if not contracts:
        print(f"--only {only} matched no contract", file=sys.stderr)
        sys.exit(2)

def theorem_spans(path):
    """name -> (start_line, end_line), 1-based inclusive."""
    spans, current, start = {}, None, None
    lines = open(path).read().split("\n")
    for i, line in enumerate(lines, start=1):
        match = re.match(r"^theorem\s+(\S+)\s*:", line)
        if match:
            if current:
                spans[current] = (start, i - 1)
            current, start = match.group(1), i
    if current:
        spans[current] = (start, len(lines))
    return spans

def lean_name(contract, function):
    return f"solkey_{contract.replace('Solc', 'solc_', 1) if contract.startswith('Solc') else contract}_{function}"

def elaborate(contract):
    """Elaborate one module; return (contract, spans, failures, fatal)."""
    path = os.path.join(CORPUS, f"{contract}.lean")
    if not os.path.exists(path):
        return contract, {}, {}, None
    spans = theorem_spans(path)
    # `maxErrors` defaults to 100, which a corpus module can exceed; every
    # theorem has to get a verdict, so the cap is lifted.
    proc = subprocess.run(["lake", "env", "lean", "--json",
                           "-DmaxErrors=4000", path],
                          capture_output=True, text=True)
    failures, fatal = {}, None
    # Lean exits 0 with no errors and 1 when a module has them. Anything
    # else — 137 for an OOM kill, a crash, a bad flag — produces no
    # diagnostics, and "no diagnostics" must never be read as "everything
    # proved". This silently reported a module of 167 failing theorems as
    # fully proved.
    if proc.returncode not in (0, 1):
        return contract, spans, {}, (0, f"lean exited {proc.returncode} "
                                        f"(no diagnostics): {proc.stderr[:160]}")
    for raw in proc.stdout.split("\n"):
        raw = raw.strip()
        if not raw:
            continue
        try:
            diagnostic = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if diagnostic.get("severity") != "error":
            continue
        line = diagnostic.get("pos", {}).get("line", 0)
        for name, (start, end) in spans.items():
            if start <= line <= end:
                failures.setdefault(name, diagnostic.get("data", "").split("\n")[0])
                break
        else:
            # A diagnostic belonging to no theorem is a module-level problem
            # (a bad import, a parse error before the first theorem): it
            # invalidates every verdict in the module, so it is fatal.
            fatal = (line, diagnostic.get("data", "")[:200])
    return contract, spans, failures, fatal

failed = {}       # lean theorem name -> first error message
elaborated = set()

# The modules are independent files over the same cached dependencies, so
# they elaborate concurrently and wall time is the slowest one, not the sum.
# Three at a time, not one per core: a corpus module holds every
# intermediate term of a few hundred `sol_wp` proofs, and running the
# larger ones concurrently exhausted memory (the kill is now caught above
# rather than silently reported as success, but it is better avoided).
with ThreadPoolExecutor(max_workers=min(3, len(contracts))) as pool:
    results = list(pool.map(elaborate, contracts))

for contract, spans, failures, fatal in results:
    if fatal is not None:
        print(f"  {contract}: error outside every theorem at line {fatal[0]}: "
              f"{fatal[1]}", file=sys.stderr)
        sys.exit(2)
    if not spans:
        print(f"  {contract}: no module (nothing ported)")
        continue
    elaborated |= set(spans)
    failed.update(failures)
    print(f"  {contract}: {len(spans) - len(failures)}/{len(spans)} proved")

observed, mismatches = [], []
for suite, contract, function, status, note in rows:
    if status == "unsupported":
        observed.append([suite, contract, function, status, note])
        continue
    # With --only, contracts that were not elaborated keep whatever verdict
    # they already had: a filtered run is an iteration aid, and must never
    # silently rewrite the rows it did not measure.
    if only and contract not in contracts:
        observed.append([suite, contract, function, status, note])
        continue
    name = lean_name(contract, function)
    if name not in elaborated:
        mismatches.append(f"{contract}.{function}: no theorem in the corpus "
                          f"(expected {name})")
        observed.append([suite, contract, function, "unsupported",
                         note or "not emitted by the translator"])
        continue
    got = "open" if name in failed else "proved"
    detail = note
    if got == "open":
        reason = failed[name]
        detail = f"{note}; {reason}" if note else reason
    observed.append([suite, contract, function, got, detail])
    if not update and status != got:
        mismatches.append(f"{contract}.{function}: expected {status}, got {got}")

if update:
    with open(EXPECTED, "w") as handle:
        for row in observed:
            handle.write("\t".join(row) + "\n")
    print(f"updated {EXPECTED}")

tally = collections.Counter(row[3] for row in observed)
print("-" * 50)
print("  ".join(f"{status}: {count}" for status, count in sorted(tally.items())),
      f"  (of {len(observed)} solkey obligations)")

if mismatches:
    for message in mismatches:
        print("MISMATCH:", message)
    sys.exit(1)
if not update:
    print("OK: every obligation matches expected.tsv")
PYTHON
