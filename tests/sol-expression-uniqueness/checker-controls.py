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
runs = read("audit-runs.json")
proof_inside = "evidence/"+runs["proof_stem"]+".inside.json"
proof_outer = "evidence/"+runs["proof_stem"]+".outer.json"
signature_inside = "evidence/"+runs["signature_stem"]+".inside.json"
signature_outer = "evidence/"+runs["signature_stem"]+".outer.json"


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
    for mode in ("--inventory", "--checkpoint"):
        with patch.object(sys, "argv", ["audit", mode]):
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                assert audit.main() == 0, "positive baseline failed: "+mode


require_positive_baseline()
print("POSITIVE_BASELINE_PASS: inventory and checkpoint acceptance")

reject_pins({})
for name in pins:
    reject_pins({k: v for k, v in pins.items() if k != name})
reject_pins(dict(pins, unexpected="0" * 64))
for name in pins:
    corrupt = dict(pins)
    corrupt[name] = "0" * 64
    reject_pins(corrupt)
with patch.object(sys, "argv", ["audit"]):
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        assert audit.main() == 1, "inventory must not substitute for proof acceptance"
print(f"CHECKER_CONTROLS_PASS: empty, {len(pins)} missing, extra, {len(pins)} corrupt pins; default acceptance stays blocked")


def reject_data(name, value, mode="--inventory"):
    def changed(item):
        return value if item == name else read(item)
    with patch.object(audit, "read", changed), patch.object(sys, "argv", ["audit", mode]):
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
bad = read(proof_inside)
bad["source_hashes"] = {}
reject_data(proof_inside, bad, "--checkpoint")
bad = read(proof_inside)
bad["memory_swap_max"] = 1
reject_data(proof_inside, bad, "--checkpoint")
bad = read(proof_outer)
bad["minimum_parent_headroom_bytes"] = 0
reject_data(proof_outer, bad, "--checkpoint")
bad = read("evidence/compiler-0.8.38.json")
bad["observations"][0]["id"] = "missing-class"
reject_data("evidence/compiler-0.8.38.json", bad, "--checkpoint")
print("CHECKPOINT_NEGATIVE_CONTROLS_PASS: missing controls/modules/declarations/axioms, forbidden axiom, false closure, stale sources, swap/reserve and compiler-class corruption")

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
bad = read(signature_inside)
bad["exit"] = 1
reject_data(signature_inside, bad, "--checkpoint")
bad = read(signature_outer)
bad["resource_stop"] = True
reject_data(signature_outer, bad, "--checkpoint")
print("REVIEW_REGRESSION_CONTROLS_PASS: remapped/duplicated fixture theorem, changed input, failed signature command and resource stop rejected")

bad = read("audit-runs.json")
bad["proof_stem"] = "../outside"
reject_data("audit-runs.json", bad, "--checkpoint")
bad = read("audit-runs.json")
bad["signature_stem"] = "signature-audit-second"
reject_data("audit-runs.json", bad, "--checkpoint")
print("AUDIT_REFERENCE_CONTROLS_PASS: invalid and stale run references rejected")

bad = read(signature_inside)
bad["source_hashes"]["Solidity/Elsewhere/AxiomPins.lean"] = "0" * 64
reject_data(signature_inside, bad, "--checkpoint")
require_positive_baseline()
print("SIGNATURE_SNAPSHOT_CONTROLS_PASS: only the separately checked generated pin path is excluded; other extra paths rejected")
