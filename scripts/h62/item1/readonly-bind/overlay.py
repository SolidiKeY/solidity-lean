#!/usr/bin/env python3
"""Generate or verify the isolated, exact-source readonly bind overlay."""
import argparse
import hashlib
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
SRC = ROOT / "Solidity/Lowering/Readonly"
OUT = ROOT / "tests/h62/item1/readonly-bind/overlay/Solidity/Lowering/Readonly"
HASHES = {
    "CapturePhases": "fa7e4f374182b22a722ef0096643bb5988bf766acd534b309fec831f24ae8e6e",
    "CaptureFailures": "3d4a39dd18dd65b90dabf47b939574137ba4e1afb918a0c5d35f503c5f2bd26c",
    "EnvironmentCredit": "ac8c9ca216d9eda7d33cb00c9b00f3b7f6ba6835aeda98bad5dbc7745a1662d4",
}
PATTERN = re.compile(r"private theorem run_bind \{α β : Type\}.*?  cases r <;> rfl\n", re.S)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, digest in HASHES.items():
        data = subprocess.run(["git", "show", "c6f550e281a7e5affa9a99bc2cdaed556dec00e4:Solidity/Lowering/Readonly/" + name + ".lean"], cwd=ROOT, check=True, capture_output=True).stdout
        if hashlib.sha256(data).hexdigest() != digest:
            raise SystemExit("source hash mismatch: " + name)
        text, count = PATTERN.subn("", data.decode("utf-8"), count=1)
        if count != 1:
            raise SystemExit("helper not found exactly once: " + name)
        text = "import Solidity.Source.Hoare\n" + text
        text = re.sub(r"(?<![\w.])run_bind\b", "Solidity.Source.Hoare.run_bind", text)
        target = OUT / (name + ".lean")
        if args.check:
            if not target.exists() or target.read_text(encoding="utf-8") != text or (SRC / (name + ".lean")).read_text(encoding="utf-8") != text:
                raise SystemExit("overlay drift: " + name)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text, encoding="utf-8")
        print(name + ": OK")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
