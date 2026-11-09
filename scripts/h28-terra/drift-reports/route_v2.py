#!/usr/bin/env python3
"""Guard lost earlier owner rows when lexical routing IDs have conflicting records.

Version 2 is opt-in; route.py remains the frozen version 1. Matching is lexical,
including paths, comments and strings, and never establishes actual ownership.
"""
import json
import re
import sys


class _JsonNumber(str):
    """Retain valid JSON number tokens without binary-float rounding or overflow."""


def _dump(value, *, sort_keys=False):
    if isinstance(value, _JsonNumber):
        return str(value)
    if isinstance(value, dict):
        keys = sorted(value) if sort_keys else value
        return "{" + ", ".join(json.dumps(key) + ": " + _dump(value[key], sort_keys=sort_keys)
                                for key in keys) + "}"
    if isinstance(value, list):
        return "[" + ", ".join(_dump(item, sort_keys=sort_keys) for item in value) + "]"
    return json.dumps(value, allow_nan=False)


def _invalid_constant(value):
    raise ValueError("Non-JSON numeric constant: " + value)


def route(data):
    owners = {}
    for row in data["ownership"]:
        if type(row["id"]) is not str:
            raise ValueError("Ownership IDs must be JSON strings")
        owners.setdefault(row["id"], []).append(row)
    output = []
    for file in data["files"]:
        if type(file["path"]) is not str or type(file["text"]) is not str:
            raise ValueError("File paths and text must be JSON strings")
    for file in sorted(data["files"], key=lambda row: row["path"]):
        if not file["path"].endswith(".lean"):
            continue
        text = file["path"] + "\n" + file["text"]
        ids = sorted(key for key in owners if re.search(
            r"(?<![\w.-])" + re.escape(key) + r"(?![\w.-])", text))
        conflicts = [key for key in ids if any(
            _dump(row, sort_keys=True) != _dump(owners[key][0], sort_keys=True)
            for row in owners[key][1:])]
        row = {"path": file["path"],
               "ownerHints": [owner for key in ids for owner in owners[key]],
               "verdict": ("lexical-conflict-owner-review-required" if conflicts else
                           "lexical-hint-owner-review-required" if ids else
                           "unassigned-owner-review-required")}
        if conflicts:
            row["conflictingIds"] = conflicts
        output.append(row)
    return output


if __name__ == "__main__":
    data = json.load(sys.stdin, parse_int=_JsonNumber, parse_float=_JsonNumber,
                     parse_constant=_invalid_constant)
    print(_dump(route(data)))
