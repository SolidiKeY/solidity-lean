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
  record M F record probe M from the language server's diagnostics JSON F
             (saved as probe-M.diagnostics.json; must have no errors);
             declarations/queries also read the file the probe itself wrote
             (probe-M.out, deleted by `probe`); sources must be unchanged
             since `probe`
  gatelog L  record `scripts/coord-tools/gate.sh full` output L (its own
             PASS/FAIL lines and per-gate logs) as the build/repository gates

The SolKey taclet checker (solkeycheck) is in no gate since master a897dac76
(H89), so this driver no longer runs it.

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
# gate.sh failures that do not come from this branch (coordinator note, moved4
# follow-up). Each has a guard in `gatelog`; they stay listed in the repository
# receipt and the lane doc. The checker pins the same name set.
MASTER_ONLY = {
    "doc-paths": "missing-file references in files this branch does not change from origin/master",
    "axiom-pins": "repository-wide axiom-pin inventory: 0 errors, unrecorded pins outside this lane",
    "testsuite": "environment: the sibling ../solkey TestSuite.sol is not the imported AST's revision",
    "corpus": "environment: the same sibling ../solkey TestSuite.sol revision check as testsuite",
}
SIBLING_PIN = re.compile(r"^\S*/TestSuite\.sol has sha256 [0-9a-f]{64}, but tests/solc/TestSuite\.ast\.json was imported from [0-9a-f]{64}: ")


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


def receipt(mode, passed, log, command, exit_code, extra=None):
    # No monitored run exists on the language-server path: minimum_available_bytes
    # is null, and the point-in-time reading is recorded under its own name.
    data = {
        "mode": mode, "passed": passed, "repository_base": REPOSITORY_BASE,
        "lakefile_sha256": sha(ROOT / "lakefile.toml"), "process_exit": exit_code,
        "sources": sources(), "runner_sha256": sha(__file__), "command": command,
        "minimum_available_bytes": None, "available_bytes_at_record": available(),
        "compiler_artifacts_sha256": sha(ROOT / "tests/sol-qualified-units/compiler-artifacts.json"),
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "log_sha256": sha(log)}
    data.update(extra or {})
    (OUT / f"gate-{mode}.json").write_text(json.dumps(data, indent=2) + "\n")


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
    os.environ["SOL_QN_EVIDENCE"] = str(OUT.relative_to(ROOT))
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
    probed = json.loads((OUT / f"probe-{mode}.sources.json").read_text())
    assert probed == sources(), "sources changed between probe and record"
    saved = OUT / f"probe-{mode}.diagnostics.json"
    if Path(diagnostics).resolve() != saved.resolve():
        saved.write_bytes(Path(diagnostics).read_bytes())
    lines = messages(saved)
    if mode != "axioms":
        out = output_file(mode)
        assert out.stat().st_mtime >= probe.stat().st_mtime, "probe output older than probe input"
        lines = [out.read_text().rstrip("\n")]
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
    receipt(mode, passed, log, ["lean_diagnostic_messages", str(probe.relative_to(ROOT))], None,
            {"diagnostics_sha256": sha(saved), "probe_sources_sha256": sha(OUT / f"probe-{mode}.sources.json")})
    print(f"GATE {mode} {'pass' if passed else 'fail'}")
    return passed


def gatelog(path):
    """Record `scripts/coord-tools/gate.sh full` output: its own PASS/FAIL lines."""
    text = Path(path).read_text()
    rows = re.findall(r"^(PASS|FAIL) (\S+) (\d+)s (\S+)$", text, re.M)
    status = {name: result for result, name, _, _ in rows}
    for required in ["build-touched", "run-lean", "trust", "orphans", "layers", "roots", "fragments", "doc-paths", "axiom-pins",
                     "testsuite", "corpus", "automatic-strict"]:
        assert required in status, "gate.sh did not run " + required
    summary = OUT / "gate-sh-summary.log"
    summary.write_text("".join(f"{r} {n} {t}s\n" for r, n, t, _ in rows))
    logs = {name: Path(log) for _, name, _, log in rows}
    build_log = OUT / "candidate-build.log"
    lines = [l for l in logs["run-lean"].read_text().splitlines() if not l.startswith(("info:", "⚠", "warning:"))]
    build_log.write_text("\n".join(lines) + "\n")
    # Lane modules reached by the gated run: those run-lean built, replayed or fetched,
    # plus the touched modules build-touched compiled (Lake then finds them up to date).
    built = set(re.findall(r"(?:Built|Replayed|Fetched) (Solidity\.Frontend\.QualifiedUnits\.\w+)\b", logs["run-lean"].read_text()))
    targets = re.search(r"^targets: (.*)$", logs["build-touched"].read_text(), re.M)
    touched = {m for m in (targets[1].split() if targets else []) if m.startswith("Solidity.Frontend.QualifiedUnits.")}
    lane = {str(p.relative_to(ROOT).with_suffix("")).replace("/", ".") for p in LANE.rglob("*.lean")}
    covered = built | (touched if status["build-touched"] == "PASS" else set())
    receipt("build", status["run-lean"] == "PASS" and status["build-touched"] == "PASS" and covered == lane, build_log,
            ["scripts/coord-tools/gate.sh", "full"], None,
            {"gate_sh": status, "lane_modules_built_or_replayed": sorted(built), "lane_modules_build_touched": sorted(touched),
             "lane_modules_missing": sorted(lane - covered)})
    repo_log = OUT / "candidate-repository.log"
    failed = sorted(name for name, result in status.items() if result != "PASS")
    master_only = {name: MASTER_ONLY[name] for name in failed if name in MASTER_ONLY}
    lane_failures = [name for name in failed if name not in MASTER_ONLY]
    if "axiom-pins" in master_only:
        text = logs["axiom-pins"].read_text()
        # 0 errors, and no finding names this lane.
        assert re.search(r"^axiom-pins: .*, 0 errors, \d+ unrecorded changes$", text, re.M), "axiom-pins errors"
        assert "QualifiedUnits" not in text, "axiom-pins finding inside the lane"
    if "doc-paths" in master_only:
        missing = [l for l in logs["doc-paths"].read_text().splitlines() if l.startswith("missing:")]
        assert missing, "doc-paths failed without missing references"
        for line in missing:
            citing = re.match(r"missing:\s+(\S+) cites ", line)
            assert citing, "unparsed doc-paths line: " + line
            unchanged = subprocess.run(["git", "diff", "--quiet", "origin/master", "--", citing[1]], cwd=ROOT).returncode == 0
            assert unchanged and "qualified" not in line.lower(), "doc-paths finding inside the branch: " + line
    for name in ("testsuite", "corpus"):
        if name in master_only:
            lines = [l for l in logs[name].read_text().splitlines() if l.strip()]
            assert lines and all(SIBLING_PIN.match(l) for l in lines), name + " failed for another reason"
    repo_log.write_text(summary.read_text() + "".join(f"MASTER_ONLY {n}: {r}\n" for n, r in master_only.items())
                        + f"LANE_FAILURES {json.dumps(lane_failures)}\n")
    # Repository-wide failures that master already has are recorded, not hidden: the
    # receipt passes only when every other gate passes.
    receipt("repository", not lane_failures, repo_log, ["scripts/coord-tools/gate.sh", "full"], None,
            {"gate_sh": status, "master_only_failures": master_only, "lane_failures": lane_failures})
    print("gate.sh:", status)
    return status


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    command = sys.argv[1:]
    if command == ["compiler"]:
        sys.exit(0 if compiler() else 1)
    if len(command) == 2 and command[0] == "probe":
        output_file(command[1]).unlink(missing_ok=True)
        (OUT / f"probe-{command[1]}.sources.json").write_text(json.dumps(sources(), indent=2) + "\n")
        (OUT / f"probe-{command[1]}.lean").write_text(probe_text(command[1]))
        print(OUT / f"probe-{command[1]}.lean")
        sys.exit(0)
    if len(command) == 3 and command[0] == "record":
        sys.exit(0 if record(command[1], command[2]) else 1)
    if len(command) == 2 and command[0] == "gatelog":
        status = gatelog(command[1])
        sys.exit(0 if status.get("run-lean") == "PASS" else 1)
    raise SystemExit(__doc__)
