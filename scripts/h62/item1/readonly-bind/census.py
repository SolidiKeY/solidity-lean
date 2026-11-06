#!/usr/bin/env python3
"""Report frozen readonly run_bind declarations and direct textual consumers."""
import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[4]
FILES = {
    "CapturePhases.lean": ("compose",),
    "CaptureFailures.lean": ("target_failed", "value_failed", "arguments_failed", "encoding_failed", "code_rejected"),
    "EnvironmentCredit.lean": ("known", "unknown", "failed", "callback_credit_failed"),
}

def scan(root):
    failed = False
    for filename, expected in FILES.items():
        path = root / "Solidity/Lowering/Readonly" / filename
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            print(f"{path}: ERROR {exc}")
            failed = True
            continue
        helpers = list(re.finditer(r"^private theorem run_bind\b", text, re.M))
        declarations = list(re.finditer(r"^theorem (\w+)\b", text, re.M))
        users = []
        for i, match in enumerate(declarations):
            end = declarations[i + 1].start() if i + 1 < len(declarations) else len(text)
            if re.search(r"\brun_bind\b", text[match.end():end]):
                users.append(match.group(1))
        ok = len(helpers) == 1 and tuple(users) == expected
        failed |= not ok
        print("{}: helpers={} consumers={} {}".format(
            path.relative_to(root), len(helpers), ",".join(users), "OK" if ok else "DRIFT"))
    return 1 if failed else 0

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    raise SystemExit(scan(parser.parse_args().root))
