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
    witnesses = []
    for name, _ in pairs:
        hits = [d for d in declarations if d == name or d.endswith("." + name)]
        if len(hits) != 1:
            raise ValueError("missing or ambiguous witness declaration: " + name)
        witnesses.append(hits[0])
    if len(set(witnesses)) != len(witnesses):
        raise ValueError("duplicate resolved witness declaration")
    return {"named_targets": len(before), "associations": len(pairs),
            "source_headers_match_frozen": True, "kernel_checked_by_this_command": False,
            "target_names": sorted(counts), "witness_names": sorted(witnesses)}


def check_families(families):
    reports, targets, witnesses = [], set(), set()
    if not families:
        raise ValueError("no families supplied")
    for path, frozen, current, witness in families:
        report = check(path, frozen, current, witness)
        if targets.intersection(report["target_names"]):
            raise ValueError("target counted in more than one family")
        if witnesses.intersection(report["witness_names"]):
            raise ValueError("witness declaration counted in more than one family")
        targets.update(report["target_names"])
        witnesses.update(report["witness_names"])
        reports.append({"source": path, **report})
    return {"families": reports, "family_count": len(reports),
            "unique_targets": len(targets), "unique_witnesses": len(witnesses),
            "kernel_checked_by_this_command": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source")
    parser.add_argument("--witness", type=Path)
    parser.add_argument("--family", nargs=2, action="append", metavar=("SOURCE", "WITNESS"))
    args = parser.parse_args()
    if args.family:
        if args.source or args.witness:
            parser.error("use --family or --source/--witness, not both")
        families = [(path, git("show", f"{BASE}:{path}"), Path(path).read_bytes(),
                     Path(witness).read_text()) for path, witness in args.family]
        result = check_families(families)
    else:
        if not args.source or not args.witness:
            parser.error("supply --source and --witness, or at least one --family")
        result = check(args.source, git("show", f"{BASE}:{args.source}"),
                       Path(args.source).read_bytes(), args.witness.read_text())
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
