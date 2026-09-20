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
#   ./scripts/check-solkey-parity.sh --calculus   the same, against the
#                                                 rule-table corpus
#
# `--calculus` swaps the corpus for Solidity/Examples/Derivations/Solkey/*,
# whose declarations are `sol_calculus` commands rather than `theorem`s, and
# the table for tests/solkey/expected-calculus.tsv. One runner rather than
# two: the attribution logic and the exit-code caution below are the part
# that is easy to get wrong, and they are the same either way.
# scripts/check-calculus-parity.sh is the wrapper.
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
MODE=wp
while [ $# -gt 0 ]; do
  case "$1" in
    --update) UPDATE=1 ;;
    --only) shift; ONLY="$1" ;;
    --calculus) MODE=calculus ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

# Dependencies only — the tactic and what it needs, not the whole library:
# the corpus modules are elaborated one by one below, so that a failing
# theorem does not abort the run.
if [ "$MODE" = calculus ]; then
  lake build Solidity.Tactics.Derivation Solidity.Semantics >/dev/null
else
  lake build Solidity.Wp.Verifier >/dev/null
fi

UPDATE=$UPDATE ONLY=$ONLY MODE=$MODE python3 - <<'PYTHON'
import json, os, re, subprocess, sys, collections, fnmatch
from concurrent.futures import ThreadPoolExecutor

mode = os.environ.get("MODE", "wp")
if mode == "calculus":
    EXPECTED = "tests/solkey/expected-calculus.tsv"
    CORPUS = "Solidity/Examples/Derivations/Solkey"
else:
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
    parts += [""] * (6 - len(parts))
    rows.append(parts[:6])

contracts = []
for _, contract, _, _, _, _ in rows:
    if contract not in contracts:
        contracts.append(contract)
if only:
    contracts = [c for c in contracts if fnmatch.fnmatch(c, only)]
    if not contracts:
        print(f"--only {only} matched no contract", file=sys.stderr)
        sys.exit(2)

DECL = re.compile(r"^(?:theorem\s+(\S+)\s*:|sol_calculus\s+(\S+)\s)")

def doc_start(lines, line):
    """The first line of the doc comment attached to `line`, or `line`.

    A `sol_calculus` command *includes* its doc comment, so Lean reports the
    command's errors at the `/--`. A span that began at the keyword would
    push those errors into the previous obligation's span, or — for the
    first one — out of every span, where the runner reads them as a fatal
    module-level problem."""
    above = line - 1
    if above < 1 or not lines[above - 1].rstrip().endswith("-/"):
        return line
    while above >= 1 and not lines[above - 1].lstrip().startswith("/--"):
        above -= 1
    return above if above >= 1 else line

def theorem_spans(path):
    """name -> (start_line, end_line), 1-based inclusive."""
    spans, current, start = {}, None, None
    lines = open(path).read().split("\n")
    for i, line in enumerate(lines, start=1):
        match = DECL.match(line)
        if match:
            name = match.group(1) or match.group(2)
            begin = doc_start(lines, i)
            if current:
                spans[current] = (start, begin - 1)
            current, start = name, begin
    if current:
        spans[current] = (start, len(lines))
    return spans

def lean_name(contract, function):
    return f"solkey_{contract.replace('Solc', 'solc_', 1) if contract.startswith('Solc') else contract}_{function}"

def modules_for(contract):
    """Every module holding this contract's obligations.

    One file normally; the rule-table corpus splits a contract into
    `<Contract>/PartNN.lean` because a single module of it is a
    single-threaded elaboration of tens of thousands of pinned taclet
    applications. The parts are independent files over the same cached
    dependencies, so they are separate tasks below."""
    direct = os.path.join(CORPUS, f"{contract}.lean")
    if os.path.exists(direct):
        return [direct]
    parts = os.path.join(CORPUS, contract)
    if os.path.isdir(parts):
        return sorted(os.path.join(parts, name)
                      for name in os.listdir(parts) if name.endswith(".lean"))
    return []

def elaborate(task):
    """Elaborate one module; return (contract, spans, failures, fatal)."""
    contract, path = task
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
tasks = [(contract, module)
         for contract in contracts for module in modules_for(contract)]
workers = 6 if mode == "calculus" else 3
with ThreadPoolExecutor(max_workers=max(1, min(workers, len(tasks)))) as pool:
    results = list(pool.map(elaborate, tasks))

tally_per_contract = collections.defaultdict(lambda: [0, 0])
for contract, spans, failures, fatal in results:
    if fatal is not None:
        print(f"  {contract}: error outside every theorem at line {fatal[0]}: "
              f"{fatal[1]}", file=sys.stderr)
        sys.exit(2)
    elaborated |= set(spans)
    failed.update(failures)
    tally_per_contract[contract][0] += len(spans)
    tally_per_contract[contract][1] += len(failures)

for contract in contracts:
    total, bad = tally_per_contract[contract]
    if total == 0:
        print(f"  {contract}: no module (nothing ported)")
        continue
    print(f"  {contract}: {total - bad}/{total} proved")

# The `note` column is the porter's and is never rewritten here; the `reason`
# column is this script's. Keeping them apart is what makes `--update`
# idempotent: with one column, a second run appends the reason to the reason
# the first run wrote, and the table degrades every time it is re-pinned.
observed, mismatches = [], []
for suite, contract, function, status, note, reason in rows:
    if status == "unsupported":
        observed.append([suite, contract, function, status, note, reason])
        continue
    # With --only, contracts that were not elaborated keep whatever verdict
    # they already had: a filtered run is an iteration aid, and must never
    # silently rewrite the rows it did not measure.
    if only and contract not in contracts:
        observed.append([suite, contract, function, status, note, reason])
        continue
    name = lean_name(contract, function)
    if name not in elaborated:
        mismatches.append(f"{contract}.{function}: no theorem in the corpus "
                          f"(expected {name})")
        observed.append([suite, contract, function, "unsupported", note,
                         "not emitted by the translator"])
        continue
    got = "open" if name in failed else "proved"
    observed.append([suite, contract, function, got, note,
                     failed[name] if got == "open" else ""])
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
      f"  (of {len(observed)} solkey obligations"
      + (", by the rule table alone)" if mode == "calculus" else ")"))

if mismatches:
    for message in mismatches:
        print("MISMATCH:", message)
    sys.exit(1)
if not update:
    print("OK: every obligation matches expected.tsv")
PYTHON
