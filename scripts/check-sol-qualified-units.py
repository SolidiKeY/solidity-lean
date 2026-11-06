#!/usr/bin/env python3
"""Qualified-unit scope audit. Default acceptance fails closed while work is pending.

--claude-vm audits tests/sol-qualified-units/claude-evidence/ (claude-gates.py receipts).

--signature-foundation-only audits bounded H27 evidence and explicitly leaves G12 pending.
--inventory-only checks the recorded source/declaration inventory, not completion.
Default runs all gates serially; saved-evidence audits enforce freshness and actual outcomes.
"""
if not __debug__:
    raise SystemExit("Optimized Python disables required assertions; rerun without -O/PYTHONOPTIMIZE.")

import argparse
import fcntl
import subprocess
import hashlib
import json
import re
import runpy
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tests/sol-qualified-units"))
from query_gate import lean_queries, compare_queries


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()



def audit(inventory_only=False, foundation_only=False, claude=False):
    ev = ROOT / ("tests/sol-qualified-units/claude-evidence" if claude else "tests/sol-qualified-units/evidence")
    runner_file = ROOT / ("tests/sol-qualified-units/claude-gates.py" if claude else "tests/sol-qualified-units/run-candidate-gates.py")
    artifacts = json.loads((ROOT / "tests/sol-qualified-units/compiler-artifacts.json").read_text())
    artifact_shas = {a["sha256"] for a in artifacts["artifacts"]}
    scope = json.loads((ROOT / "tests/sol-qualified-units/scope.json").read_text())
    matrix = json.loads((ROOT / "tests/sol-qualified-units/constructors.json").read_text())
    syntax = ROOT / "Solidity/Source/Syntax.lean"
    assert hashlib.sha256(syntax.read_bytes()).hexdigest() == matrix["syntax_sha256"], "syntax pin changed"
    ctors = runpy.run_path(str(ROOT / "scripts/source-ctors.py"))["constructors"]()
    assert [r["constructor"] for r in matrix["rows"]] == [n for n, _ in ctors], "constructor inventory drift"
    for row, (name, args) in zip(matrix["rows"], ctors):
        expected = [{"position": i, "name": n, "type": t} for i, (n, t) in enumerate(args) if "IdPath" in t or t == "MapKey"]
        assert row["direct_fields"] == expected, f"path field inventory: {name}"
        assert row["syntax_children"] == [i for i, (_, t) in enumerate(args) if t.startswith("Syn")], f"syntax children: {name}"
    actual = {}
    constructors = {}
    for path in sorted((ROOT / "Solidity/Frontend/QualifiedUnits").rglob("*.lean")):
        text = path.read_text()
        nested = []
        for match in re.finditer(r"^inductive (\w+)[\s\S]*?(?=^(?:def|theorem|inductive|instance|namespace|end)\b|\Z)", text, re.M):
            nested.extend(match[1] + "." + n for n in re.findall(r"^  \| (\w+)", match[0], re.M))
        if nested:
            constructors[str(path.relative_to(ROOT))] = nested
        actual[str(path.relative_to(ROOT))] = re.findall(r"^(?:def|theorem|inductive|structure|abbrev|instance)\s+(\S+)", text, re.M)
        assert not re.search(r"\b(sorry|axiom|native_decide)\b", re.sub(r"/-[\s\S]*?-/", "", text)), f"trust violation: {path}"
        assert not re.search(r"set_option\s+maxHeartbeats", text), f"proof budget override: {path}"
    assert actual == scope["modules"], "module/declaration inventory drift"
    assert constructors == scope["inductive_constructors"], "inductive constructor inventory drift"
    declaration_pins = json.loads((ROOT / scope["reflection_pins"]).read_text())
    declaration_report = json.loads((ev / "declaration-report.json").read_text())
    assert {"modules": declaration_report["modules"], "declarations": declaration_report["declarations"]} == declaration_pins, "reflected declaration inventory drift"
    assert set(declaration_report["modules"]) == {p[:-5].replace("/", ".") for p in actual}, "reflected module scope mismatch"
    all_declarations = {row["name"]: row for row in declaration_report["declarations"]}
    assert len(all_declarations) == len(declaration_report["declarations"]), "duplicate reflected declaration"
    if claude:
        partial_helpers = set(json.loads((ROOT / "tests/sol-qualified-units/partial-helpers.json").read_text())["partial_helpers"])
        assert all(name.endswith("._unsafe_rec") for name in partial_helpers), "non-generated partial helper"
    else:
        partial_baseline = json.loads((ev / "compiler-helper-baseline.json").read_text())
        partial_helpers = set(partial_baseline["partial_helpers"])
    assert {name for name, row in all_declarations.items() if row["partial"]} == partial_helpers, "new partial helper"
    assert not any(row["unsafe"] or row["axiom"] or not set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for row in all_declarations.values()), "reflected trust violation"
    for path, names in actual.items():
        namespace = re.search(r"^namespace (Solidity\.Frontend\.QualifiedUnits[\w.]*)", (ROOT / path).read_text(), re.M)[1]
        assert all(namespace + "." + name in all_declarations for name in names), "source declaration missing from reflection"
    for path, digest in declaration_report["sources"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, "stale declaration audit " + path
    if not claude:
        for path, digest in {**partial_baseline["byte_identical_source_sha256"], **partial_baseline.get("h27_reviewed_source_sha256", {})}.items():
            assert sha(ROOT / path) == digest, "changed compiler-helper baseline " + path
    g0 = json.loads((ROOT / "tests/sol-qualified-units/g0-kernel-helpers.json").read_text())
    assert g0["syntax_sha256"] == sha(ROOT / "Solidity/Source/Syntax.lean"), "G0 syntax drift"
    for helper in g0["helpers"]:
        text = (ROOT / helper["file"]).read_text()
        start = re.search(r"^def " + re.escape(helper["definition"]) + r"\b", text, re.M).start()
        tail = text[start:]
        end = re.search(r"\n(?:def|theorem|end|@\[)", tail)
        body = tail[:end.start()] if end else tail
        assert helper["eliminator"] + " (motive := fun c (" in body, "missing G0 generalized eliminator"
        names = re.findall(r"\(«([^»]+)» :=", body)
        assert len(names) == len(set(names)) == helper["constructors"] and set(names) == {n for n, _ in ctors}, "G0 constructor coverage"
    for statement in g0["preserved_theorem_statements"]:
        text = (ROOT / statement["file"]).read_text()
        start = re.search(r"^theorem " + re.escape(statement["name"]) + r"\b", text, re.M).start()
        tail = text[start:]
        end = re.search(r":=|\n  \|", tail).start()
        assert hashlib.sha256(" ".join(tail[:end].split()).encode()).hexdigest() == statement["sha256"], "weakened theorem statement"
    for twin in g0["twins"]:
        text = (ROOT / "Solidity/Frontend/QualifiedUnits/References.lean").read_text()
        assert "@[implemented_by " + twin["implementation"] + "]" in text, "missing executable twin"
        assert twin["theorem"] in all_declarations, "missing twin equivalence theorem"
    pins = json.loads((ROOT / "tests/sol-qualified-units/axiom-pins.json").read_text())
    observed = {}
    for match in re.finditer(r"^'([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", (ev / "candidate-axioms.log").read_text(), re.M):
        observed[match[1]] = [] if match[2] is None else [name.strip() for name in match[2].split(",")]
    assert observed == pins, "axiom pin drift"
    expected_theorems = set()
    for path in actual:
        prefix = re.search(r"^namespace (Solidity\.Frontend\.QualifiedUnits[\w.]*)", (ROOT / path).read_text(), re.M)[1] + "."
        expected_theorems.update(prefix + name for name in re.findall(r"^theorem (\S+)", (ROOT / path).read_text(), re.M))
    assert all(sorted(axioms) == all_declarations[name]["axioms"] for name, axioms in pins.items()), "theorem/reflected axiom disagreement"
    assert set(pins) == expected_theorems, "theorem/axiom gate coverage mismatch"
    assert all(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"} for axioms in pins.values()), "unexpected axiom"
    signature_matrix = json.loads((ROOT / "tests/sol-qualified-units/signature-normalization-matrix.json").read_text())
    signature_theorems = {name for name in expected_theorems if any(name.startswith("Solidity.Frontend.QualifiedUnits." + area + ".") for area in ["TypePaths", "SignatureNormalization", "SignatureHiding", "NormalizationControls", "SignatureMembers", "SignatureMemberControls", "SignatureResolution", "SignatureResolutionControls", "MergeSpecification"])}
    assert len(signature_matrix["rows"]) == len(signature_theorems), "signature matrix row count"
    assert {row["kernel_theorem"] for row in signature_matrix["rows"]} == signature_theorems, "signature matrix coverage"
    signature_probe = json.loads((ev / "h27-location-probe.json").read_text())
    assert signature_probe["compiler_fixtures_pass"] and signature_probe["script_sha256"] == sha(ROOT / "tests/sol-qualified-units/h27-location-probe.mjs"), "stale signature compiler probes"
    assert signature_probe["version"] == artifacts["version"] == "0.8.38+commit.1835d247.Emscripten.clang" and signature_probe["sha256"] in artifact_shas, "signature compiler pin"
    assert [row["id"] for row in signature_probe["rows"]] == signature_matrix["compiler_probe_ids"], "signature probe coverage"
    assert [[row["id"], row["accepted"], [e["code"] for e in row["errors"]]] for row in signature_probe["rows"]] == signature_probe["expected"], "signature probe outcome mismatch"
    resolution_matrix = json.loads((ROOT / "tests/sol-qualified-units/resolution-probe-matrix.json").read_text())
    resolution_probe = json.loads((ev / "resolution-barrier-probe.json").read_text())
    assert resolution_probe["compiler_fixtures_pass"] and resolution_probe["script_sha256"] == sha(ROOT / "tests/sol-qualified-units/resolution-barrier-probe.mjs"), "stale resolution probe driver"
    assert resolution_probe["version"] == signature_probe["version"] and resolution_probe["sha256"] == signature_probe["sha256"], "resolution compiler pin"
    assert [r["id"] for r in resolution_probe["rows"]] == [r["id"] for r in resolution_matrix["rows"]], "resolution probe row inventory"
    for expected, observed_probe in zip(resolution_matrix["rows"], resolution_probe["rows"]):
        assert observed_probe["accepted"] == expected["accepted"] and [e["code"] for e in observed_probe["errors"]] == expected["error_codes"], "resolution probe outcome"
        assert observed_probe["source_sha256"] == expected["source_sha256"] == hashlib.sha256(observed_probe["source"].encode()).hexdigest(), "resolution probe source"
        assert expected["kernel_theorems"] and all("Solidity.Frontend.QualifiedUnits." + n in pins for n in expected["kernel_theorems"]), "resolution probe missing kernel links"
    for row in matrix["rows"]:
        assert row["kernel_fixture"] is not None, "unwitnessed constructor " + row["constructor"]
        assert "Solidity.Frontend.QualifiedUnits." + row["kernel_fixture"] in pins, "unrun constructor fixture"
    compiler = json.loads((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_text())
    report = json.loads((ev / "solc-report.json").read_text())
    assert report["version"] == compiler["version"] == artifacts["version"] and report["sha256"] in artifact_shas, "compiler pin mismatch"
    assert compiler["sha256"] in artifact_shas, "matrix compiler pin not in artifact pins"
    assert report["matrix_sha256"] == hashlib.sha256((ROOT / "tests/sol-qualified-units/compiler-matrix.json").read_bytes()).hexdigest(), "stale compiler matrix evidence"
    assert [r["id"] for r in report["rows"]] == [r["id"] for r in compiler["rows"]], "compiler fixture inventory drift"
    for row, result in zip(compiler["rows"], report["rows"]):
        assert result["passed"] and result["accepted"] == row["accepted"], "compiler outcome mismatch " + row["id"]
        assert result["error_codes"] == sorted(row["error_codes"]), "refusal code mismatch"
        assert sorted(e["text"] for e in result["errors"]) == sorted(row["error_texts"]), "refusal span mismatch"
        for unit, path in row["sources"].items():
            assert result["source_sha256"][unit] == hashlib.sha256((ROOT / "tests/sol-qualified-units" / path).read_bytes()).hexdigest(), "stale fixture source " + path
        assert row["kernel_theorems"], "unlinked compiler fixture " + row["id"]
        assert all("Solidity.Frontend.QualifiedUnits." + t in pins for t in row["kernel_theorems"]), "unrun paired kernel fixture"
    query_links = json.loads((ROOT / "tests/sol-qualified-units/resolution-query-links.json").read_text())
    assert len(query_links) == sum(len(row["queries"]) for row in compiler["rows"]), "query/kernel link count"
    assert {(link["id"], link["reference"]) for link in query_links} == {(row["id"], q["reference"]) for row in compiler["rows"] for q in row["queries"]}, "query/kernel coverage"
    for link in query_links:
        row = next(row for row in compiler["rows"] if row["id"] == link["id"])
        assert link["kernel_theorem"] in row["kernel_theorems"] and "Solidity.Frontend.QualifiedUnits." + link["kernel_theorem"] in pins, "unrun paired resolver observation"
    metadata = json.loads((ev / ("gate-build.json" if claude else "candidate-build.json")).read_text())
    for path, expected in metadata["sources"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, "stale kernel build " + path
    sources = {path: sha(ROOT / path) for path in sorted([*actual, *scope["inputs"]])}
    assert metadata["sources"] == declaration_report["sources"] == sources, "incomplete source binding"
    runner_sha = sha(runner_file)
    for saved in [metadata, declaration_report, report]:
        assert saved["runner_sha256"] == runner_sha, "stale runner evidence"
    assert report["fixture_script_sha256"] == sha(ROOT / "tests/sol-qualified-units/solc-fixtures.mjs"), "stale compiler driver"
    if claude:
        gates = runpy.run_path(str(runner_file))
        for kind in ["axioms", "declarations", "queries"]:
            assert (ev / f"probe-{kind}.lean").read_text() == gates["probe_text"](kind), "stale probe " + kind
        assert declaration_report["input_sha256"] == sha(ev / "probe-declarations.lean"), "stale reflected input"
    else:
        for kind, saved in [("declarations", declaration_report)]:
            assert saved["input_sha256"] == sha(ev / f"{kind}-input.lean.txt"), "stale reflected input"
    query = json.loads((ev / "query-report.json").read_text())
    assert query["sources"] == sources and query["runner_sha256"] == runner_sha, "stale query source/runner"
    assert query["matrix_sha256"] == report["matrix_sha256"], "stale query matrix"
    assert query["query_gate_sha256"] == sha(ROOT / "tests/sol-qualified-units/query_gate.py"), "stale query comparator"
    assert query["compiler_report_sha256"] == sha(ev / "solc-report.json"), "stale query compiler graph"
    if claude:
        assert query["input_sha256"] == sha(ev / "probe-queries.lean"), "stale query commands"
    else:
        assert query["input_sha256"] == hashlib.sha256(lean_queries(compiler).encode()).hexdigest() == sha(ev / "queries-input.lean.txt"), "stale query commands"
    recomputed = compare_queries(query["observed"], compiler, report)
    assert all(query[key] == value for key, value in recomputed.items()), "query comparison/report disagreement"
    if foundation_only:
        assert recomputed["compiler_agreement"], "signature-aware differential disagreement"
        assert not any(row["resolution_gap"] for row in compiler["rows"]), "unresolved query gap marker"
        sources = {path: sha(ROOT / path) for path in sorted([*actual, *scope["inputs"]])}
        runner_sha = sha(runner_file)
        assert declaration_report["sources"] == sources and declaration_report["runner_sha256"] == runner_sha, "stale foundation reflection"
        assert declaration_report["input_sha256"] == sha(ev / ("probe-declarations.lean" if claude else "declarations-input.lean.txt")), "stale foundation input"
        for mode in ["build", "axioms", "declarations", "signature-probes", "resolution-probes", "keysort", "solc", "queries"]:
            saved = json.loads((ev / f"gate-{mode}.json").read_text())
            assert saved["passed"] and saved["mode"] == mode and saved["process_exit"] == 0, "foundation gate failure " + mode
            assert saved["sources"] == sources and saved["runner_sha256"] == runner_sha, "stale foundation gate " + mode
            assert saved["minimum_available_bytes"] >= 4 * 1024**3, "foundation reserve " + mode
            assert saved["lakefile_sha256"] == sha(ROOT / "lakefile.toml"), "foundation Lake drift"
            assert saved["log_sha256"] == sha(ev / f"candidate-{mode}.log"), "foundation log drift"
            subprocess.run(["git", "merge-base", "--is-ancestor", saved["repository_base"], "HEAD"], cwd=ROOT, check=True)
        print(f"SIGNATURE_FOUNDATION_PASS: {len(actual)} modules, {len(all_declarations)} declarations, {len(pins)} theorem pins, {len(signature_matrix['rows'])} H27 theorem rows, 7 supplementary compiler probes, 17 direct queries; full G12 acceptance pending")
        return
    gate_results = {}
    for mode in ["build", "axioms", "declarations", "solc", "queries", "signature-probes", "resolution-probes", "keysort", "repository"]:
        saved = json.loads((ev / f"gate-{mode}.json").read_text())
        assert saved["mode"] == mode and saved["runner_sha256"] == runner_sha and saved["sources"] == sources, "stale gate evidence " + mode
        assert saved["lakefile_sha256"] == sha(ROOT / "lakefile.toml"), "stale Lake configuration " + mode
        subprocess.run(["git", "merge-base", "--is-ancestor", saved["repository_base"], "HEAD"], cwd=ROOT, check=True)
        assert saved["log_sha256"] == sha(ev / f"candidate-{mode}.log"), "changed gate log " + mode
        assert saved["minimum_available_bytes"] >= 4 * 1024**3, "reserve gate " + mode
        gate_results[mode] = saved["passed"]
    print("DIRECT_DIFFERENTIAL: " + ("pass" if recomputed["compiler_agreement"] else "fail " + ", ".join(recomputed["mismatches"])))
    for path in scope["inputs"]:
        assert (ROOT / path).is_file(), f"unverified input: {path}"
    print(f"INVENTORY_PASS: {len(actual)} modules, {sum(map(len, actual.values()))} top-level declarations, {len(ctors)} constructor rows")
    for path, declarations in actual.items():
        print(path + ": " + ", ".join(declarations))
    if not inventory_only:
        assert recomputed["compiler_agreement"], "DIRECT_DIFFERENTIAL_FAIL: " + ", ".join(recomputed["mismatches"])
        assert all(gate_results.values()), "required gate failures: " + ", ".join(k for k, v in gate_results.items() if not v)
        pending = [q["id"] for q in scope["queue"] if q["status"] != "done"]
        assert scope["acceptance_complete"] and not pending, "ACCEPTANCE_PENDING: " + ", ".join(pending)
        assert not any(row["resolution_gap"] for row in compiler["rows"]), "unresolved inherited-overload differential gap"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--signature-foundation-only", action="store_true", help="audit saved H27 foundation evidence; does not complete G12 acceptance")
    parser.add_argument("--audit-only", action="store_true", help="audit saved evidence without rerunning gates")
    parser.add_argument("--claude-vm", action="store_true", help="audit claude-evidence/ produced by tests/sol-qualified-units/claude-gates.py (no Docker runner)")
    args = parser.parse_args()
    try:
        failures = []
        if not args.inventory_only and not args.audit_only and not args.signature_foundation_only and not args.claude_vm:
            gates = []
            for mode in ["build", "axioms", "declarations", "solc", "queries", "signature-probes", "resolution-probes", "keysort", "repository"]:
                command = [sys.executable, str(ROOT / "tests/sol-qualified-units/run-candidate-gates.py"), mode]
                result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a") as lock:
                    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    (ev / f"controller-{mode}.log").write_text(result.stdout)
                status = "pass" if result.returncode == 0 else "fail"
                print(f"GATE {mode} {status}; tests/sol-qualified-units/evidence/candidate-{mode}.log")
                gates.append({"command": command, "exit": result.returncode, "status": status})
                if result.returncode:
                    failures.append(mode)
            with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                (ev / "acceptance-gates.json").write_text(json.dumps(gates, indent=2) + "\n")
        audit(args.inventory_only, args.signature_foundation_only, args.claude_vm)
        assert not failures, "gate failures: " + ", ".join(failures)
    except (AssertionError, OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
