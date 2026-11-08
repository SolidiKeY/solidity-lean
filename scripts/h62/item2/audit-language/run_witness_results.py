#!/usr/bin/env python3
"""Guard stale witness audit credit by binding bounded execution to before/after inputs.

Uses the existing serial resource wrapper. Outputs are private evidence; a local
binding is an internal consistency record, not an authentication authority.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from witness_results import ROOT, snapshot, audit_command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("plan", "generated", "binding"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", args.label):
        raise ValueError("invalid runtime label")
    output = Path("/workspace/sol-numeric-literals-gate-output")
    receipt_path, log_path = [output / (args.label + suffix) for suffix in (".json", ".log")]
    for path in (args.binding, receipt_path, log_path):
        if path.exists() or path.is_symlink() or path.resolve().is_relative_to(ROOT):
            raise ValueError("new external evidence paths required")
    before = snapshot(args.plan, args.generated)
    command = audit_command(args.generated)
    result = subprocess.run([sys.executable, str(ROOT / "tests/sol-numeric-literals/runtime/check.py"),
                             args.label] + command, cwd=ROOT)
    if result.returncode:
        raise SystemExit(result.returncode)
    after = snapshot(args.plan, args.generated)
    if before != after:
        raise ValueError("audit inputs changed during run")
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    record = dict(before=before, after=after, command=command,
                  receipt_sha256=sha(receipt_path), log_sha256=sha(log_path))
    with args.binding.open("x") as out:
        out.write(json.dumps(record, sort_keys=True, indent=2) + "\n")


if __name__ == "__main__":
    main()
