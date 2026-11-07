#!/usr/bin/env python3
"""Compare successful fresh-output probe receipts; refuse failed/mixed inputs.
This reports a timing threshold only, never kernel correspondence acceptance.
"""
import argparse
import json
from pathlib import Path
from propose import TARGETS


def compare(before, after):
    receipts = [json.loads((p/"receipt.json").read_text()) for p in (before, after)]
    a, b = receipts
    if before.resolve() == after.resolve() or a.get("command") == b.get("command"):
        raise ValueError("before/after must be distinct executions")
    required = {"Solidity.Backend.StructuredFlow."+name for name in TARGETS}
    for r in receipts:
        if not required <= set(r["requested"]) or not required <= set(r["closure"]):
            raise ValueError("all six affected family modules must be measured")
    for r in receipts:
        if r["exit"] != 0 or r["guard"]:
            raise ValueError("failed/resource-stopped gate cannot supply acceptance timings")
        if r.get("source_sha256_before") != r["source_sha256"] or r.get("git_status_before") != r.get("git_status_after"):
            raise ValueError("source or git status changed during gate")
        if r.get("conditions", {}).get("cache") != "fresh-private-output":
            raise ValueError("missing fresh-output condition evidence")
    if a["conditions"] != b["conditions"] or a["archive_sha256"] != b["archive_sha256"] or a["requested"] != b["requested"]:
        raise ValueError("mixed toolchain/resources/cache/target conditions")
    if a["head"] != b["head"]:
        raise ValueError("different frozen trees: paired overlays must share a committed base")
    allowed = {"Solidity.Backend.StructuredFlow."+name for name in TARGETS}
    helpers = {"tests.h62.item4.generic-structuredflow.GenericMapped", "Solidity.Backend.StructuredFlow.GenericMapped"}
    keys = set(a["source_sha256"]) | set(b["source_sha256"])
    if any(a["source_sha256"].get(k) != b["source_sha256"].get(k) for k in keys-allowed-helpers):
        raise ValueError("unrelated dependency source drift")
    for path, receipt in zip((before, after), receipts):
        rows = [line.split() for line in (path/"modules.tsv").read_text().splitlines()]
        if [row[0] for row in rows] != receipt["closure"] or any(row[1] != "0" for row in rows):
            raise ValueError("incomplete/failing module inventory")
    durations = [sum(int(line.split()[2]) for line in (p/"modules.tsv").read_text().splitlines()) for p in (before, after)]
    seconds = [n/1e9 for n in durations]
    if min(seconds) <= 0:
        raise ValueError("invalid timing duration")
    delta = (seconds[1]/seconds[0]-1)*100
    return dict(before_seconds=seconds[0], after_seconds=seconds[1], delta_percent=delta,
                decision="STOP_SLOWDOWN" if durations[1]*100 > durations[0]*110 else "WITHIN_TIMING_LIMIT",
                semantic_acceptance=False, conditions=a["conditions"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    args = parser.parse_args()
    try:
        result = compare(args.before, args.after)
    except (ValueError, KeyError, OSError) as error:
        raise SystemExit("REFUSED: " + str(error))
    print(json.dumps(result, indent=2, sort_keys=True))
    raise SystemExit(result["decision"] == "STOP_SLOWDOWN")


if __name__ == "__main__":
    main()
