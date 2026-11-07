#!/usr/bin/env python3
"""Validate timing receipt structure and compare paired declared groups.

This is an offline receipt checker, not a build runner or proof verifier. It
checks recorded metadata and log hashes; it cannot establish that a log or its
resource/cache description is truthful. No delta is computed until its declared
prerequisites and both declared groups pass the structural checks below.
"""
import argparse
import hashlib
import json
import pathlib
import sys

PIN = "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d"
REQUIRED = {"toolchain", "keysort", "dependency", "helper", "equivalence", "axioms"}
META = {"base", "toolchain_sha256", "lean_version", "lake_version", "threads", "lean_args",
        "memory_max_bytes", "reserve_bytes", "swap_bytes", "cache_preparation", "resources"}


def verify_receipt(item):
    if not isinstance(item, dict):
        raise ValueError("receipt must be an object")
    if item.get("status") != "pass" or type(item.get("exit_code")) is not int or item.get("exit_code") != 0:
        raise ValueError("required receipt did not pass")
    path = pathlib.Path(item.get("log", ""))
    if not path.is_absolute() or not path.is_file():
        raise ValueError("required receipt log is absent or not absolute")
    content = path.read_bytes()
    if not content:
        raise ValueError("required receipt log is empty")
    if hashlib.sha256(content).hexdigest() != item.get("sha256"):
        raise ValueError("receipt log SHA-256 mismatch")


def evaluate(data):
    if not isinstance(data, dict) or type(data.get("schema_version")) is not int or data.get("schema_version") != 1:
        raise ValueError("unsupported schema")
    prereqs = data.get("prerequisites", {})
    if not isinstance(prereqs, dict) or set(prereqs) != REQUIRED:
        raise ValueError("required proof and toolchain prerequisites missing or extra")
    for receipt in prereqs.values():
        verify_receipt(receipt)
    before, after = data["before"], data["after"]
    bm, am = before["metadata"], after["metadata"]
    if not isinstance(bm, dict) or not isinstance(am, dict) or set(bm) != META or bm != am:
        raise ValueError("timing metadata missing, extra, or not identical")
    if (bm["toolchain_sha256"] != PIN or type(bm["threads"]) is not int or bm["threads"] != 1 or
            not isinstance(bm["lean_args"], list) or "-j1" not in bm["lean_args"] or
            not isinstance(bm["lean_version"], str) or not isinstance(bm["lake_version"], str) or
            "4.35.0" not in bm["lean_version"] or "4.35.0" not in bm["lake_version"]):
        raise ValueError("toolchain or serial Lean settings do not match the assignment")
    if (type(bm["swap_bytes"]) is not int or bm["swap_bytes"] != 0 or
            type(bm["reserve_bytes"]) is not int or bm["reserve_bytes"] < 4 * 1024**3):
        raise ValueError("swap or available-memory reserve is invalid")
    if type(bm["memory_max_bytes"]) is not int or bm["memory_max_bytes"] <= bm["reserve_bytes"]:
        raise ValueError("invalid memory cap")
    if any(not bm[k] for k in ("base", "lean_version", "lake_version", "cache_preparation", "resources")):
        raise ValueError("empty required timing metadata")
    names = data.get("original_components")
    if (not isinstance(names, list) or not names or any(not isinstance(n, str) or not n.strip() for n in names) or
            len(set(names)) != len(names) or "extracted_helper" in names):
        raise ValueError("invalid original component list")
    a, b = before["samples"], after["samples"]
    if not isinstance(a, list) or not isinstance(b, list) or not a or len(a) != len(b):
        raise ValueError("nonempty equal numbers of before/after samples required")
    totals = []
    for old, new in zip(a, b):
        for row, expected in ((old, set(names)), (new, set(names) | {"extracted_helper"})):
            verify_receipt(row)
            components = row.get("components_ns", {})
            if not isinstance(components, dict) or set(components) != expected or any(type(n) is not int or n <= 0 or n > 2**63-1 for n in components.values()):
                raise ValueError("missing, extra, or invalid timing component")
            commands = row.get("commands", {})
            if not isinstance(commands, dict) or set(commands) != expected or any(not isinstance(c, str) or not c.strip() for c in commands.values()):
                raise ValueError("missing, extra, or invalid component command")
        if any(old["commands"][name] != new["commands"][name] for name in names):
            raise ValueError("before and after component commands differ")
        totals.append((sum(old["components_ns"].values()), sum(new["components_ns"].values())))
    comparisons = [{"before_ns": x, "after_ns": y, "change_percent": (y-x)*100/x,
                    "over_10_percent": y*10 > x*11} for x, y in totals]
    return {"status": "stop_slowdown" if any(r["over_10_percent"] for r in comparisons) else "declared_receipts_within_limit",
            "pairs": comparisons,
            "boundary": "caller-declared receipts and arithmetic only; workload completeness, actual commands, logs, cache/resource state and proof validity are not independently verified"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=pathlib.Path)
    args = parser.parse_args()
    try:
        result = evaluate(json.loads(args.manifest.read_text()))
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "invalid", "error": str(error), "delta_computed": False}))
        return 2
    print(json.dumps(result, indent=2))
    return 1 if result["status"] == "stop_slowdown" else 0

if __name__ == "__main__":
    sys.exit(main())
