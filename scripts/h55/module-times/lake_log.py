#!/usr/bin/env python3
"""Parse completed Lake timing rows without treating logs as proof of freshness."""
from fractions import Fraction
import json
import math
import re
import sys

# Lake prints a status glyph, job count, action, module and duration. Reject
# unknown duration syntax completely instead of accidentally interpreting zero.
ROW = re.compile(r"^\s*[✔✖⚠ℹ]?\s*\[\d+/\d+\]\s+(Built|Replayed)\s+([^\s]+)\s+\(([^()]*)\)\s*$")
PART = re.compile(r"(\d+(?:\.\d+)?|\.\d+)\s*(ms|s|m|h)")
ORDER = {"h": 0, "m": 1, "s": 2, "ms": 3}
FACTOR = {"h": Fraction(3600), "m": Fraction(60), "s": Fraction(1), "ms": Fraction(1, 1000)}


def seconds_exact(text):
    if not isinstance(text, str):
        raise ValueError("invalid duration")
    pos = 0
    total = Fraction(0)
    last = -1
    found = False
    while pos < len(text):
        while pos < len(text) and text[pos].isspace():
            pos += 1
        if pos == len(text):
            break
        match = PART.match(text, pos)
        if not match or ORDER[match[2]] <= last:
            raise ValueError("malformed duration")
        last = ORDER[match[2]]
        total += Fraction(match[1]) * FACTOR[match[2]]
        pos = match.end()
        found = True
    if not found:
        raise ValueError("empty duration")
    return total


def seconds(text):
    value = float(seconds_exact(text))
    if not math.isfinite(value) or value <= 0:
        raise ValueError("nonpositive or nonfinite duration")
    return value


def parse(log):
    rows, errors = [], []
    for number, line in enumerate(log.splitlines(), 1):
        match = ROW.fullmatch(line)
        if match:
            if line.lstrip().startswith("✖"):
                errors.append(f"line {number}: failed build row")
                continue
            try:
                duration = seconds(match[3])
            except (ValueError, OverflowError):
                errors.append(f"line {number}: malformed duration")
                continue
            rows.append({"line": number, "action": match[1], "module": match[2], "seconds": duration, "duration": match[3]})
        elif re.search(r"\b(?:Built|Replayed)\b", line):
            errors.append(f"line {number}: unrecognized timing row")
    return {"rows": rows, "errors": errors}



def coverage(inventory, parsed, exit_code):
    # Check completed-log coverage; provenance remains unauthenticated.
    if type(exit_code) is not int or exit_code != 0:
        return ["build did not exit successfully"]
    if not isinstance(inventory, list) or not inventory:
        return ["empty or invalid module inventory"]
    if any(not isinstance(row, dict) or not isinstance(row.get("module"), str)
           or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9\x27]*(?:\.[A-Za-z_][A-Za-z_0-9\x27]*)*", row["module"])
           or not isinstance(row.get("path"), str) or not row["path"].endswith(".lean")
           or row["path"].startswith("/") or "\\" in row["path"]
           or any(part in ("", ".", "..") for part in row["path"].split("/")) for row in inventory):
        return ["invalid module mapping"]
    modules = [row["module"] for row in inventory]
    paths = [row["path"] for row in inventory]
    if len(set(modules)) != len(modules) or len(set(paths)) != len(paths):
        return ["duplicate module or path mapping"]
    errors = list(parsed["errors"])
    seen = set()
    expected = set(modules)
    for row in parsed["rows"]:
        name = row["module"]
        if name in seen:
            errors.append(f"duplicate module: {name}")
        seen.add(name)
        if name not in expected:
            errors.append(f"unexpected module: {name}")
        if row["action"] != "Built":
            errors.append(f"replayed module: {name}")
        try:
            exact = seconds_exact(row.get("duration"))
            shown = row.get("seconds")
            if (type(shown) not in (int, float) or not math.isfinite(shown)
                    or shown <= 0 or shown != float(exact)):
                errors.append(f"inconsistent displayed duration: {name}")
            if not 0 < exact <= 300:
                errors.append(f"invalid or over 300 seconds: {name}")
        except (ValueError, OverflowError):
            errors.append(f"invalid duration: {name}")
    errors.extend(f"missing module: {name}" for name in sorted(expected - seen))
    return errors

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--inventory", required=True, help="JSON list of module/path mappings")
    parser.add_argument("--exit-code", required=True, type=int, help="actual Lake process exit status")
    args = parser.parse_args()
    try:
        with open(args.inventory, encoding="utf-8") as file:
            inventory = json.load(file)
        result = parse(sys.stdin.read())
        result["coverage_errors"] = coverage(inventory, result, args.exit_code)
    except (OSError, ValueError, TypeError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return bool(result["coverage_errors"])


if __name__ == "__main__":
    sys.exit(main())
