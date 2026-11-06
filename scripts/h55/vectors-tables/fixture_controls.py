#!/usr/bin/env python3
"""Reproduce frozen StatementGrammar fixture control modules outside the checkout."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
AREA = Path("Solidity/Frontend/StatementGrammarH28")
DATA = AREA / "FixtureData.lean"
CONTROL = AREA / "FixtureControls"
MANIFEST = ROOT / "tests/h55/vectors-tables/fixture-controls-manifest.json"
BASE = "4d3790eadb8a5212233bc7d5e345817476b2f590"
COUNT = 45

def names(): return [f"Case{i:02}.lean" for i in range(COUNT)]
def sha(b): return hashlib.sha256(b).hexdigest()
def render(i):
    if type(i) is not int or not 0 <= i < COUNT: raise ValueError("fixture index")
    return ("import Solidity.Frontend.StatementGrammarH28.FixtureData\n\n"
            "namespace Solidity.Frontend.StatementGrammarH28\n"
            f"theorem statementFixture{i}_checked : statementFixtureCheck statementFixture{i} = true := by decide +kernel\n"
            f"#print axioms statementFixture{i}_checked\n"
            "end Solidity.Frontend.StatementGrammarH28\n").encode()

def inventory(root):
    data = (root / DATA).read_bytes()
    ids = [int(x) for x in re.findall(rb"^def statementFixture([0-9]+) : StatementFixture :=$", data, re.M)]
    if ids != list(range(COUNT)): raise ValueError("fixture definition inventory/order")
    directory = root / CONTROL
    actual_names = sorted(p.name for p in directory.glob("*.lean"))
    if actual_names != names(): raise ValueError("control file inventory/order")
    files = {}
    for i, name in enumerate(names()):
        original = (directory / name).read_bytes()
        if original != render(i): raise ValueError(f"{name}: source differs from generated output")
        files[name] = sha(original)
    return {"base": BASE, "data_sha256": sha(data), "controls": files}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("manifest", "check", "emit"))
    parser.add_argument("--output", type=Path)
    a = parser.parse_args()
    if (a.mode == "emit") != (a.output is not None): parser.error("--output is required only for emit")
    actual = inventory(ROOT)
    if a.mode == "manifest":
        if MANIFEST.exists(): raise ValueError("manifest already exists")
        MANIFEST.write_text(json.dumps(actual, indent=2) + "\n")
    else:
        if actual != json.loads(MANIFEST.read_text()): raise ValueError("frozen manifest differs")
        if a.mode == "emit":
            dest = a.output.resolve()
            if dest.is_relative_to(ROOT): raise ValueError("output must be outside checkout")
            dest.mkdir(parents=True, exist_ok=False)
            for i, name in enumerate(names()): (dest / name).write_bytes(render(i))
        print("PASS: 45 fixture definitions and 45 complete control files reproduced")

if __name__ == "__main__": main()
