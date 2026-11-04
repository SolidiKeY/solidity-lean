#!/usr/bin/env python3
"""Audit SOL-EU inventory; default acceptance fails while any obligation is open.

--inventory checks coverage and source pins only. It is never a proof gate.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "tests/sol-expression-uniqueness"


def read(name):
    return json.loads((DATA / name).read_text())


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", action="store_true")
    args = parser.parse_args()
    pins = read("source-pins.json")
    required = {"Solidity/Frontend/Checked/" + name + ".lean"
                for name in ("Print", "Prec", "Parser", "Check", "Token", "ExprExamples")}
    required |= {"Solidity/Source/Syntax.lean",
                 "tests/upstream/grammar-0.8.38/SolidityParser.g4"}
    require(set(pins) == required, "source pin inventory differs from mandatory inputs")
    for name, expected in pins.items():
        current = (ROOT / name).read_bytes()
        frozen = subprocess.check_output(["git", "show", BASE + ":" + name], cwd=ROOT)
        require(hashlib.sha256(current).hexdigest() == expected,
                "working source pin mismatch: " + name)
        require(hashlib.sha256(frozen).hexdigest() == expected,
                "frozen base pin mismatch: " + name)
    syntax = (ROOT / "Solidity/Source/Syntax.lean").read_text()
    block = syntax.split("  -- Expressions, one constructor per labelled alternative.")[1]
    block = block.split("  -- Simple statements.")[0]
    constructors = re.findall(r"^  \| (\w+)", block, re.M)
    ledger = read("constructors.json")
    require([x["constructor"] for x in ledger] == constructors,
            "constructor ledger differs from intrinsic Syntax, including order")
    for row in ledger:
        for field in ("boundary", "precNode", "layout", "root_reconstruction", "uniqueness", "controls"):
            require(bool(row[field]), "empty constructor field: " + field)
        require(0 <= row["level"] <= 16, "invalid precedence level")
    obligations = read("obligations.json")
    require([x["id"] for x in obligations] == [f"EU-{i:02}" for i in range(1, 15)],
            "obligation IDs missing, duplicated, or reordered")
    manifest = read("registration-manifest.json")
    require(manifest["base"] == BASE, "registration base mismatch")
    modules = sorted(p.relative_to(ROOT).as_posix() for p in
                     (ROOT / "Solidity/Frontend/ExpressionUniqueness").rglob("*.lean"))
    require(modules == manifest["modules"], "module registration inventory mismatch")
    # This inventory checkpoint intentionally carries no Lean modules/declarations.
    # Acceptance cannot be enabled merely by flipping obligation status fields.
    require(not modules and not manifest["declarations"],
            "new Lean work requires extending declaration/axiom/fixture acceptance")
    print(f"INVENTORY_PASS: {len(ledger)} intrinsic expression constructors; "
          f"{len(pins)} exact base/working source pins; {len(obligations)} obligations")
    for row in obligations:
        print(f'{row["id"]}: {row["status"]}: {row["obligation"]}')
    if not args.inventory:
        print("ACCEPTANCE_BLOCKED: no uniqueness proof or kernel validation; "
              "inventory coverage does not establish SOL-EU", file=sys.stderr)
        return 1
    print("Inventory only; no RUNTIME_GATE_PASS or proof acceptance claimed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, IndexError, OSError, subprocess.CalledProcessError) as error:
        print("AUDIT_FAIL: " + str(error), file=sys.stderr)
        sys.exit(2)
