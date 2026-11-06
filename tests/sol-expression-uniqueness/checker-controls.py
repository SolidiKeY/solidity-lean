#!/usr/bin/env python3
"""Negative audit controls; these do not test Lean uniqueness."""
from contextlib import redirect_stdout, redirect_stderr
import importlib.util
import io
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True

root = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("eu_audit", root / "scripts/check-sol-expression-uniqueness.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
read = audit.read
pins = read("source-pins.json")
import tempfile

# A synthetic gate.sh log: it tests the checker's log logic, not Lean. The real
# kernel evidence is an actual gate.sh run (docs/feature-work/expression-uniqueness.md).
def gate_log(digest=None, exit_line="SOL_EU_EXIT 0", gate=True, extra=""):
    text = "SOL_EU_HEAD 0\nSOL_EU_SOURCES "+(digest or audit.source_digest())+"\n"
    text += ("SOL_EU_FULL_GATE ./run-lean.sh\n" if gate else "")
    text += extra+"Build completed successfully (5510 jobs).\n"+exit_line+"\n"
    handle = tempfile.NamedTemporaryFile("w", suffix=".log", delete=False)
    handle.write(text)
    handle.close()
    return handle.name

GOOD_LOG = gate_log()


def reject_pins(value):
    def changed(name):
        return value if name == "source-pins.json" else read(name)
    with patch.object(audit, "read", changed), patch.object(sys, "argv", ["audit", "--inventory"]):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            try:
                audit.main()
            except ValueError:
                return
    raise AssertionError("invalid source pins accepted")


def require_positive_baseline():
    for mode in (["--inventory"], ["--proof"], ["--checkpoint", "--build-log", GOOD_LOG]):
        with patch.object(sys, "argv", ["audit", *mode]):
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                assert audit.main() == 0, "positive baseline failed: "+mode


require_positive_baseline()
print("POSITIVE_BASELINE_PASS: inventory, proof-scope and checkpoint acceptance")

reject_pins({})
for name in pins:
    reject_pins({k: v for k, v in pins.items() if k != name})
reject_pins(dict(pins, unexpected="0" * 64))
for name in pins:
    corrupt = dict(pins)
    corrupt[name] = "0" * 64
    reject_pins(corrupt)
open_rows = [r for r in read("obligations.json") if r["status"] not in {"proved", "proved-inventory", "pass"}]
if open_rows:
    with patch.object(sys, "argv", ["audit", "--build-log", GOOD_LOG]):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            assert audit.main() == 1, "open obligations must keep full acceptance closed"
print(f"CHECKER_CONTROLS_PASS: empty, {len(pins)} missing, extra, {len(pins)} corrupt pins; open obligations keep full acceptance closed")


def reject_data(name, value, mode="--inventory"):
    def changed(item):
        return value if item == name else read(item)
    argv = ["audit", mode] + (["--build-log", GOOD_LOG] if mode == "--checkpoint" else [])
    with patch.object(audit, "read", changed), patch.object(sys, "argv", argv):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            try:
                audit.main()
            except ValueError:
                return
    raise AssertionError("invalid checkpoint evidence accepted: "+name)

reject_data("constructor-controls.json", read("constructor-controls.json")[:-1])
reject_data("declarations.json", read("declarations.json")[:-1])
bad = read("registration-manifest.json")
bad["modules"] = bad["modules"][:-1]
reject_data("registration-manifest.json", bad)
bad = read("axioms.json")
bad.pop(next(iter(bad)))
reject_data("axioms.json", bad)
bad = read("axioms.json")
bad[next(iter(bad))] = ["sorryAx"]
reject_data("axioms.json", bad)
bad = read("obligations.json")
next(r for r in bad if r["id"] == "EU-07")["status"] = "pass"
reject_data("obligations.json", bad)


def reject_log(path, why):
    with patch.object(sys, "argv", ["audit", "--checkpoint", "--build-log", path]):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            try:
                audit.main()
            except ValueError:
                return
    raise AssertionError("invalid build log accepted: "+why)

reject_log(gate_log(digest="0"*64), "stale source digest")
reject_log(gate_log(exit_line="SOL_EU_EXIT 1"), "failed run-lean")
reject_log(gate_log(gate=False), "not the full gate")
reject_log(gate_log(extra="error: Solidity/Frontend/ExpressionUniqueness/AxiomPins.lean:1:0: x\n"), "error line")
reject_log(gate_log(extra="✖ [1/2] Building Solidity.Frontend.ExpressionUniqueness.AxiomPins\n"), "failed job")
reject_log("/nonexistent/gate.log", "missing log")
print("CHECKPOINT_NEGATIVE_CONTROLS_PASS: missing controls/modules/declarations/axioms, forbidden axiom, false closure; stale, failed, partial, erroring and missing build logs")

bad = read("constructor-controls.json")
bad[0]["theorem"] = "Solidity.Frontend.ExpressionUniqueness.negFamily_certified"
reject_data("constructor-controls.json", bad)
bad = read("constructor-controls.json")
for row in bad:
    row["theorem"] = "Solidity.Frontend.ExpressionUniqueness.constructor_ident"
reject_data("constructor-controls.json", bad)
bad = read("constructor-controls.json")
bad[0]["input"] = "wrong-input"
reject_data("constructor-controls.json", bad)
print("REVIEW_REGRESSION_CONTROLS_PASS: remapped/duplicated fixture theorem, and changed input rejected")


report_path = audit.AREA/"AxiomPins.lean"
report = report_path.read_text()
read_text = Path.read_text

def reject_report(value):
    def changed(path, *args, **kwargs):
        return value if path == report_path else read_text(path, *args, **kwargs)
    with patch.object(Path, "read_text", changed), patch.object(sys, "argv", ["audit", "--checkpoint", "--build-log", GOOD_LOG]):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            try:
                audit.main()
            except ValueError:
                return
    raise AssertionError("invalid actual axiom report accepted")

first_name = next(iter(read("axioms.json")))
reject_report(report+"\n/-- info: '"+first_name+"' does not depend on any axioms -/\n")
reject_report(report.replace("Classical.choice", "sorryAx", 1))
reject_report(report.replace("Quot.sound] -/", "Quot.sound -/", 1))
reject_report(report.replace("#guard_msgs in #print axioms", "#print axioms", 1))
require_positive_baseline()
print("AXIOM_REPORT_CONTROLS_PASS: actual wrapped standard lists accepted; duplicate, forbidden, unterminated and unguarded pins rejected")


reject_data("constructor-identity.json", read("constructor-identity.json")[:-1])
bad = read("constructor-identity.json")
bad[0]["theorem"] = bad[1]["theorem"]
reject_data("constructor-identity.json", bad)
bad = read("operators.json")
bad[-1]["constructors"] = bad[-1]["constructors"][:-1]
reject_data("operators.json", bad)
reject_data("boundaries.json", read("boundaries.json")[:-1])
with patch.object(audit, "original_target_text", lambda: "∀ a, a = a"), patch.object(sys, "argv", ["audit", "--inventory"]):
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        try:
            audit.main()
        except ValueError:
            pass
        else:
            raise AssertionError("changed original theorem target accepted")
by_name = {r["name"]: r for r in read("declarations.json")}
bad = {name: dict(row) for name, row in by_name.items()}
name = "Solidity.Frontend.ExpressionUniqueness.certifiedYieldUnique"
bad[name]["source_signature"] = "theorem certifiedYieldUnique (h : CertifiedYieldUnique) : CertifiedYieldUnique"
with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
    try:
        audit.audit_complete_proof(bad, [r["constructor"] for r in read("constructors.json")], read("constructors.json"))
    except ValueError:
        pass
    else:
        raise AssertionError("circular public uniqueness premise accepted")
require_positive_baseline()
print("COMPLETE_PROOF_CONTROLS_PASS: omitted/remapped constructor step, missing intrinsic operator/boundary, changed original target and added circular public premise rejected")

reject_data("recursive-cases.json", read("recursive-cases.json")[:-1])
bad = read("recursive-cases.json")
bad[0]["categories"] = ["list.expr"]
reject_data("recursive-cases.json", bad)
require_positive_baseline()
print("RECURSIVE_CASE_CONTROLS_PASS: missing recursive constructor or optional/parameter category rejected")

if not (audit.DATA/"evidence").is_dir():
    print("KERNEL_ENVIRONMENT_CONTROLS_SKIPPED: the H44 Codex-VM evidence and kernel-*.json dumps are not in this checkout")
    sys.exit(0)


# A positive external baseline must pass before any corruption is credited.
with patch.object(sys, "argv", ["audit", "--proof", "--external-evidence"]):
    assert audit.main() == 0, "external baseline failed"

def reject_external(name, value):
    def changed(item):
        return value if item == name else read(item)
    with patch.object(audit, "read", changed), patch.object(sys, "argv", ["audit", "--proof", "--external-evidence"]):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            try:
                audit.main()
            except (ValueError, OSError):
                return
    raise AssertionError("invalid external evidence accepted: "+name)

reject_external("kernel-module-declarations.json", read("kernel-module-declarations.json")[:-1])
reject_external("kernel-declarations.json", read("kernel-declarations.json")[:-1])
bad = read("kernel-declarations.json")
bad.append(bad[0])
reject_external("kernel-declarations.json", bad)
bad = read("environment-summary.json")
bad["audit"]["source_sha256"] = "0"*64
reject_external("environment-summary.json", bad)
bad = read("environment-summary.json")
bad["extra_names_also_kernel"] = 0
reject_external("environment-summary.json", bad)
for role in ("names", "audit"):
    run = read("environment-summary.json")[role]
    path = "evidence/"+run["stem"]+".inside.json"
    bad = read(path)
    bad["verification_hashes"][run["source"]] = "0"*64
    reject_external(path, bad)
    bad = read(path)
    bad["exit"] = 1
    reject_external(path, bad)
require_positive_baseline()
print("KERNEL_ENVIRONMENT_CONTROLS_PASS: omitted/duplicate kernel rows, module omission, stale actual verifier hash, failed command and hidden compiler/logical overlap rejected")

reject_external("kernel-emissions.json", read("kernel-emissions.json")[:-1])
bad = read("kernel-emissions.json")
bad.append(bad[0])
reject_external("kernel-emissions.json", bad)
bad = read("kernel-module-declarations.json")
next(row for row in bad if row["ownership"])["ownership"][0]["owner"] = "Solidity.Source.Syntax"
reject_external("kernel-module-declarations.json", bad)
require_positive_baseline()
print("KERNEL_OWNER_CONTROLS_PASS: missing/duplicated emissions and changed actual kernel ownership rejected; repeated metadata copies require identical types/axioms")

bad = read("environment-compression.json")
next(row for row in bad if row["original"].endswith("environment-audit-gates-sealed/1.log"))["compressed_sha256"] = "0"*64
reject_external("environment-compression.json", bad)
bad = read("kernel-declarations.json")
bad[0]["type_expr_sha256"] = "0"*64
reject_external("kernel-declarations.json", bad)
require_positive_baseline()
print("STREAMED_TYPE_TRACE_CONTROLS_PASS: corrupted lossless archive provenance and changed compact type hashes rejected; full trace preserved and full repeated types compared")
