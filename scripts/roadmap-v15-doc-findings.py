#!/usr/bin/env python3
"""Compare ALL emitted missing/ambiguous findings; do not waive the full gate."""
from collections import Counter
from pathlib import Path
import json
import re
import sys

def findings(text):
    result = Counter(line for line in text.splitlines() if line.startswith(("missing:", "ambiguous:")))
    missing = sum(n for line, n in result.items() if line.startswith("missing:"))
    exits = re.findall(r"^EXIT: ([0-9]+)$", text, re.M)
    if len(exits) != 1:
        raise ValueError("checker log lacks one recorded exit status")
    failures = re.findall(r"^FAIL: ([0-9]+) reference\(s\) name a file that does not exist\.$", text, re.M)
    if missing:
        if failures != [str(missing)] or exits != ["1"]:
            raise ValueError("incomplete/mismatched checker failure footer")
    elif failures or exits != ["0"] or "OK: every backticked *.lean reference resolves." not in text:
        raise ValueError("checker log lacks a completed successful outcome")
    return result

def compare(base, current):
    a, b = findings(base), findings(current)
    return dict(base=dict(a), current=dict(b), added=dict(b-a), removed=dict(a-b))

if __name__ == "__main__":
    result = compare(Path(sys.argv[1]).read_text(), Path(sys.argv[2]).read_text())
    print(json.dumps(result, indent=2))
    sys.exit(bool(result["added"]))
