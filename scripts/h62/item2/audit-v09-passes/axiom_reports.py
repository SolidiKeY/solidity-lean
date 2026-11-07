#!/usr/bin/env python3
"""Inventory the guarded-report regression: a bare #print axioms command is
observed output, not an enforced pin. Source-only accounting at the frozen pin;
no Lean target resolution, actual axiom set, witness or trust result is inferred.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
from census import BASE, census, masked, sha

PRINT = re.compile(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+([^\s;]+)")
GUARD = re.compile(r"#guard_msgs(?:\s*\([^\n]*\))?\s+in\s*\Z")


def reports(source):
    """Keep exact report spans; only a directly enclosing source guard counts.

    Comments and strings cannot create commands. Intervening commands break
    attachment. This recognizes the repository's single-command guard form,
    not every possible Lean command syntax or elaborated declaration identity.
    """
    clean = masked(source)
    result = []
    for match in PRINT.finditer(clean):
        prefix = clean[:match.start()]
        guard = GUARD.search(prefix)
        start = match.start() + len(match[0]) - len(match[0].lstrip())
        result.append({
            "token": source[match.start(1):match.end(1)],
            "line": source.count("\n", 0, start) + 1,
            "character_span": [start, match.end()],
            "source_command": source[start:match.end()],
            "direct_guard": guard is not None,
            "target_resolution": "pending Lean",
            "actual_axioms": None,
        })
    return result


def inventory(root):
    frozen = census(root)
    files = []
    for item in frozen["files"]:
        data = subprocess.check_output(["git", "show", BASE + ":" + item["path"]], cwd=root)
        found = reports(data.decode())
        files.append({"path": item["path"], "source_sha256": sha(data),
                      "census_theorems": item["theorem_count"], "reports": found})
    rows = [row for item in files for row in item["reports"]]
    return {"schema": 1, "base": BASE, "files": files,
            "boundary": "Source command inventory only; no target resolution, theorem coverage, actual axiom set, proof or trust claim.",
            "summary": {"files": len(files), "census_theorems": len(frozen["declarations"]),
                        "print_commands": len(rows), "directly_guarded": sum(r["direct_guard"] for r in rows),
                        "bare_or_unrecognized_guard": sum(not r["direct_guard"] for r in rows),
                        "verified_witnesses": 0}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = inventory(Path(__file__).resolve().parents[4])
    args.output.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()
    (args.output / "axiom-reports.json").write_bytes(data)
    (args.output / "axiom-reports.sha256").write_text(sha(data) + "  axiom-reports.json\n")
    print(json.dumps(result["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
