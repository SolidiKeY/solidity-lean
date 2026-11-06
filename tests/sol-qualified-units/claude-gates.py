#!/usr/bin/env python3
"""Claude-VM gate driver for SOL-QN (replaces the Codex Docker runner here).

The Codex runner (`run-candidate-gates.py`) needs Docker and a /tools Lean
copy, neither present on Claude VMs, whose repository settings also deny
`lean`/`lake build` in a shell. This driver produces the same evidence files
under `tests/sol-qualified-units/claude-evidence/`:

  compiler   run the three pinned-compiler scripts (solc, signature-probes,
             resolution-probes) with SOL_QN_SOLJSON naming a pinned artifact
  probe M    write the Lean input for M in {axioms, declarations, queries}
             to claude-evidence/probe-M.lean, to be elaborated by the Lean
             language server (lean_diagnostic_messages on that file)
  record M [F] record probe M: axioms parses the language server's saved
             diagnostics JSON F; declarations/queries read the file the probe
             itself wrote (probe-M.out); writes the log, report and receipt
  runlean L  record a ./run-lean.sh log L as the build/keysort/repository gates

Every receipt binds the owned sources, inputs, this driver and lakefile.
Nothing here is evidence that the old Codex seals hold.
"""
if not __debug__:
    raise SystemExit("Optimized Python disables required assertions; rerun without -O/PYTHONOPTIMIZE.")

import ast
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests/sol-qualified-units"))
from query_gate import lean_queries, compare_queries

OUT = ROOT / "tests/sol-qualified-units/claude-evidence"
# Base commit of this Claude lane (moved4 batch).
REPOSITORY_BASE = "aec9adf1ad8666a7e591e42a537069a93dc858cb"
LANE = ROOT / "Solidity/Frontend/QualifiedUnits"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sources():
    scope = json.loads((ROOT / "tests/sol-qualified-units/scope.json").read_text())
    paths = [str(p.relative_to(ROOT)) for p in sorted(LANE.rglob("*.lean"))] + scope["inputs"]
    return {path: sha(ROOT / path) for path in sorted(paths)}


def available():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    return 0


def receipt(mode, passed, log, command, exit_code):
    (OUT / f"gate-{mode}.json").write_text(json.dumps({
        "mode": mode, "passed": passed, "repository_base": REPOSITORY_BASE,
        "lakefile_sha256": sha(ROOT / "lakefile.toml"), "process_exit": exit_code,
        "sources": sources(), "runner_sha256": sha(__file__), "command": command,
        "minimum_available_bytes": available(),
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "log_sha256": sha(log)}, indent=2) + "\n")


def theorem_names():
    names = []
    for path in sorted(LANE.rglob("*.lean")):
        text = path.read_text()
        namespace = re.search(r"^namespace (Solidity\.Frontend\.QualifiedUnits[\w.]*)", text, re.M)[1]
        names += [namespace + "." + name for name in re.findall(r"^theorem (\S+)", text, re.M)]
    return names


def output_file(mode):
    return OUT / f"probe-{mode}.out"


def probe_text(mode):
    target = json.dumps(str(output_file(mode).relative_to(ROOT)))
    if mode == "queries":
        text = lean_queries(json.loads((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_text()))
        head = '#eval IO.println ("RESOLVER_QUERY_REPORT " ++ '
        assert text.count(head) == 1
        text = text.replace(head, '#eval do\n  let report := ("RESOLVER_QUERY_REPORT " ++ ')
        tail = "]).compress)\nend QualifiedUnitsQueryAudit\n"
        assert text.endswith(tail)
        return text[:-len(tail)] + "]).compress)\n  IO.FS.writeFile " + target + " (report ++ \"\\n\")\n  IO.println report\nend QualifiedUnitsQueryAudit\n"
    text = "import Lean\n" if mode == "declarations" else ""
    for path in sorted(LANE.rglob("*.lean")):
        text += "import " + str(path.relative_to(ROOT).with_suffix("")).replace("/", ".") + "\n"
    if mode == "axioms":
        return text + "".join(f"#print axioms {name}\n" for name in theorem_names())
    runner = (ROOT / "tests/sol-qualified-units/run-candidate-gates.py").read_text()
    block = re.search(r"stdin \+= '(\\nopen Lean in.*?)'\n", runner, re.S)[1]
    block = ast.literal_eval("'" + block + "'")
    line = '  logInfo m!"DECLARATION_INVENTORY {(Json.mkObj [("modules", toJson (modules.map (fun n => n.toString))), ("declarations", Json.arr rows)]).compress}"\n'
    assert block.endswith(line)
    return text + block[:-len(line)] + '  let report := s!"DECLARATION_INVENTORY {(Json.mkObj [("modules", toJson (modules.map (fun n => n.toString))), ("declarations", Json.arr rows)]).compress}"\n  IO.FS.writeFile ' + target + ' (report ++ "\\n")\n  logInfo report\n'



def messages(diagnostics):
    data = json.loads(Path(diagnostics).read_text())
    if "result" in data:
        data = data["result"]
    items = data["items"]
    errors = [i for i in items if i["severity"] == "error"]
    assert not errors, "probe elaboration errors: " + "; ".join(e["message"][:200] for e in errors)
    assert not data.get("partial") and not data.get("timed_out"), "incomplete probe elaboration"
    return [i["message"] for i in sorted(items, key=lambda i: (i["line"], i["column"]))]


def compiler():
    os.environ.setdefault("SOL_QN_EVIDENCE", str(OUT.relative_to(ROOT)))
    assert "SOL_QN_SOLJSON" in os.environ, "SOL_QN_SOLJSON must name a pinned soljson artifact"
    ok = True
    for mode, script in [("solc", "solc-fixtures.mjs"), ("signature-probes", "h27-location-probe.mjs"),
                         ("resolution-probes", "resolution-barrier-probe.mjs")]:
        command = ["node", "tests/sol-qualified-units/" + script]
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = OUT / f"candidate-{mode}.log"
        log.write_text(result.stdout)
        passed = result.returncode == 0
        if mode == "solc" and passed:
            report = json.loads(result.stdout[result.stdout.index("{"):])
            report["matrix_sha256"] = sha(ROOT / "tests/sol-qualified-units/compiler-matrix.json")
            report["runner_sha256"] = sha(__file__)
            report["fixture_script_sha256"] = sha(ROOT / "tests/sol-qualified-units/solc-fixtures.mjs")
            (OUT / "solc-report.json").write_text(json.dumps(report, indent=2) + "\n")
            passed = report["compiler_fixtures_pass"]
        receipt(mode, passed, log, command, result.returncode)
        print(f"GATE {mode} {'pass' if passed else 'fail'}")
        ok = ok and passed
    return ok


def record(mode, diagnostics):
    probe = OUT / f"probe-{mode}.lean"
    assert probe.read_text() == probe_text(mode), "stale probe input"
    lines = messages(diagnostics) if mode == "axioms" else [output_file(mode).read_text().rstrip("\n")]
    log = OUT / f"candidate-{mode}.log"
    log.write_text("\n".join(lines) + "\n")
    passed = False
    if mode == "axioms":
        expected = json.loads((ROOT / "tests/sol-qualified-units/axiom-pins.json").read_text())
        observed = {}
        for match in re.finditer(r"^'([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log.read_text(), re.M):
            observed[match[1]] = [] if match[2] is None else [name.strip() for name in match[2].split(",")]
        assert set(observed) == set(theorem_names()), "axiom report coverage"
        (OUT / "observed-axioms.json").write_text(json.dumps(observed, indent=2) + "\n")
        passed = observed == expected
        with log.open("a") as out:
            out.write(f"AXIOM_PINS_{'PASS' if passed else 'FAIL'} {len(observed)}\n")
    elif mode == "declarations":
        match = re.search(r"DECLARATION_INVENTORY (\{.*\})", log.read_text())
        assert match, "missing declaration inventory"
        result = json.loads(match[1])
        for row in result["declarations"]:
            row["axioms"] = sorted(row["axioms"])
        result["declarations"].sort(key=lambda row: row["name"])
        result["modules"].sort()
        result.update({"sources": sources(), "runner_sha256": sha(__file__), "input_sha256": sha(probe),
                       "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()})
        (OUT / "declaration-report.json").write_text(json.dumps(result, indent=2) + "\n")
        pins = json.loads((ROOT / "tests/sol-qualified-units/declaration-pins.json").read_text())
        passed = pins == {"modules": result["modules"], "declarations": result["declarations"]}
        with log.open("a") as out:
            out.write(f"DECLARATION_PINS_{'PASS' if passed else 'FAIL'} {len(result['declarations'])}\n")
    elif mode == "queries":
        match = re.search(r"RESOLVER_QUERY_REPORT (\[.*\])", log.read_text())
        assert match, "missing resolver query report"
        matrix = json.loads((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_text())
        report = json.loads((OUT / "solc-report.json").read_text())
        assert report["matrix_sha256"] == sha(ROOT / "tests/sol-qualified-units/compiler-matrix.json"), "stale compiler evidence"
        observed = json.loads(match[1])
        result = compare_queries(observed, matrix, report)
        result.update({"observed": observed, "sources": sources(), "matrix_sha256": report["matrix_sha256"],
                       "query_gate_sha256": sha(ROOT / "tests/sol-qualified-units/query_gate.py"),
                       "runner_sha256": sha(__file__), "input_sha256": sha(probe),
                       "compiler_report_sha256": sha(OUT / "solc-report.json")})
        (OUT / "query-report.json").write_text(json.dumps(result, indent=2) + "\n")
        passed = result["compiler_agreement"]
        with log.open("a") as out:
            out.write("DIRECT_DIFFERENTIAL " + ("PASS" if passed else "FAIL") + " " + json.dumps(result["mismatches"]) + "\n")
    receipt(mode, passed, log, ["lean_diagnostic_messages", str(probe.relative_to(ROOT))], 0)
    print(f"GATE {mode} {'pass' if passed else 'fail'}")
    return passed


def runlean(path):
    text = Path(path).read_text()
    log = OUT / "candidate-run-lean.log"
    keep = [line for line in text.splitlines() if not line.startswith(("✔", "info:", "⚠", "warning:"))]
    log.write_text("\n".join(keep) + "\n")
    exit_match = re.search(r"^EXIT (\d+)$", text, re.M)
    exit_code = int(exit_match[1]) if exit_match else None
    built = all(f"Built {m}" in text or f"Replayed {m}" in text for m in
                [str(p.relative_to(ROOT).with_suffix("")).replace("/", ".") for p in sorted(LANE.rglob("*.lean"))])
    errors = [line for line in text.splitlines() if re.search(r"\berror\b", line) and not line.startswith(("✔", "info:"))]
    passed = exit_code == 0 and not errors
    for mode in ["build", "keysort", "repository"]:
        ok = passed and (built if mode == "build" else True)
        if mode == "keysort":
            ok = ok and bool(re.search(r"^parsed \d+ taclets", text, re.M) or "solkeycheck" in text)
        receipt(mode, ok, log, ["./run-lean.sh"], exit_code)
        print(f"GATE {mode} {'pass' if ok else 'fail'}")
    return passed


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    command = sys.argv[1:]
    if command == ["compiler"]:
        sys.exit(0 if compiler() else 1)
    if len(command) == 2 and command[0] == "probe":
        (OUT / f"probe-{command[1]}.lean").write_text(probe_text(command[1]))
        print(OUT / f"probe-{command[1]}.lean")
        sys.exit(0)
    if len(command) == 3 and command[0] == "record" and command[1] == "axioms":
        sys.exit(0 if record(command[1], command[2]) else 1)
    if len(command) == 2 and command[0] == "record":
        sys.exit(0 if record(command[1], None) else 1)
    if len(command) == 2 and command[0] == "runlean":
        sys.exit(0 if runlean(command[1]) else 1)
    raise SystemExit(__doc__)
