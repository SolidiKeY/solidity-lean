#!/usr/bin/env python3
"""Guard silent loss/duplication of named law telescope associations.

Source accounting only: actual imported telescope and axiom checks remain Lean
obligations. Anonymous examples are not named theorem census entries.
"""
import argparse
import collections
import json
import re
from pathlib import Path
from census import BASE, git, mask, scan


def check(source_path, frozen, current, witness):
    original = scan(source_path, frozen, {"language"})
    live = scan(source_path, current, {"language"})
    before = {r["name_candidate"]: r for r in original}
    after = {r["name_candidate"]: r for r in live}
    if len(before) != len(original) or len(after) != len(live):
        raise ValueError("duplicate source theorem name")
    if not before or set(before) != set(after):
        raise ValueError("frozen/current named theorem census differs")
    for name in before:
        for key in ("source_signature", "section_variables"):
            if before[name][key] != after[name][key]:
                raise ValueError("frozen header/context differs: " + name)
    pairs = re.findall(r"^#verify_hypotheses (\S+) for (\S+)$", mask(witness), re.M)
    counts = collections.Counter(target for _, target in pairs)
    if set(counts) != set(before) or any(n != 1 for n in counts.values()):
        raise ValueError("missing, unexpected or duplicate target association")
    if len({name for name, _ in pairs}) != len(pairs):
        raise ValueError("duplicate witness association")
    declarations = [r["name_candidate"] for r in scan("witness", witness.encode(), {"language"})]
    for name, _ in pairs:
        hits = [d for d in declarations if d == name or d.endswith("." + name)]
        if len(hits) != 1:
            raise ValueError("missing or ambiguous witness declaration: " + name)
    return {"named_targets": len(before), "associations": len(pairs),
            "source_headers_match_frozen": True, "kernel_checked_by_this_command": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True)
    parser.add_argument("--witness", type=Path, required=True)
    args = parser.parse_args()
    result = check(args.source, git("show", f"{BASE}:{args.source}"),
                   Path(args.source).read_bytes(), args.witness.read_text())
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
