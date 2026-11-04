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
