#!/usr/bin/env python3
"""Report the frozen readonly run_bind declarations and their consumers."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
FILES = {
    "CapturePhases.lean": ("compose",),
    "CaptureFailures.lean": ("target_failed", "value_failed", "arguments_failed", "encoding_failed", "code_rejected"),
    "EnvironmentCredit.lean": ("known", "unknown", "failed", "callback_credit_failed"),
}
failed = False
for filename, expected in FILES.items():
    path = ROOT / "Solidity/Lowering/Readonly" / filename
    text = path.read_text(encoding="utf-8")
    helpers = list(re.finditer(r"^private theorem run_bind\b", text, re.M))
    declarations = list(re.finditer(r"^theorem (\w+)\b", text, re.M))
    users = []
    for i, match in enumerate(declarations):
        end = declarations[i + 1].start() if i + 1 < len(declarations) else len(text)
        if re.search(r"\brun_bind\b", text[match.end():end]):
            users.append(match.group(1))
    ok = len(helpers) == 1 and tuple(users) == expected
    failed |= not ok
    print("{}: helpers={} consumers={} {}".format(path.relative_to(ROOT), len(helpers), chr(44).join(users), "OK" if ok else "DRIFT"))
sys.exit(1 if failed else 0)
