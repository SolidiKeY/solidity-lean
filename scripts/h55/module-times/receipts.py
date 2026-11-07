#!/usr/bin/env python3
"""Validate a complete, fresh per-file timing receipt; never runs Lean.

Inventory is an explicit JSON array of unique relative .lean paths. Receipts are
JSON objects with a matching path, status, elapsed_seconds, and fresh boolean.
This standalone consumer does not authenticate its input or select the scope.
"""
import argparse
from decimal import Decimal
import json
import math
import pathlib
import sys


def validate(inventory, receipts):
    errors = []
    if not isinstance(inventory, list) or not inventory:
        return ["inventory must be a nonempty list"]
    def valid_path(p):
        return (isinstance(p, str) and p.endswith(".lean") and p != ".lean"
                and not p.startswith("/") and "\\" not in p
                and all(x not in ("", ".", "..") for x in p.split("/")))
    if any(not valid_path(p) for p in inventory) or len(set(inventory)) != len(inventory):
        return ["invalid or duplicate inventory path"]
    if not isinstance(receipts, list):
        return ["receipts must be a list"]
    expected = set(inventory)
    seen = set()
    for row in receipts:
        if not isinstance(row, dict) or not valid_path(row.get("path")):
            errors.append("invalid receipt path")
            continue
        path = row["path"]
        if path in seen:
            errors.append(f"duplicate: {path}")
        seen.add(path)
        if path not in expected:
            errors.append(f"unexpected: {path}")
        if row.get("status") != "ok" or row.get("fresh") is not True:
            errors.append(f"failed, timed out or not fresh: {path}")
        value = row.get("elapsed_seconds")
        finite = (type(value) is int or (type(value) is float and math.isfinite(value))
                  or (type(value) is Decimal and value.is_finite()))
        if not finite or value <= 0:
            errors.append(f"invalid elapsed time: {path}")
        elif value > 300:
            errors.append(f"over 300 seconds: {path}")
    errors.extend(f"missing: {p}" for p in sorted(expected - seen))
    return errors


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("inventory", type=pathlib.Path)
    parser.add_argument("receipts", type=pathlib.Path)
    args = parser.parse_args()
    try:
        def reject_constant(value):
            raise ValueError(f"invalid JSON constant: {value}")
        receipt_data = json.loads(args.receipts.read_text(), parse_float=Decimal, parse_constant=reject_constant)
        errors = validate(json.loads(args.inventory.read_text()), receipt_data)
    except (OSError, ValueError, TypeError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 1
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("receipt structure and coverage pass; measurement provenance is not authenticated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
