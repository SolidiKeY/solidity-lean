#!/usr/bin/env python3
"""Compare supplied before/after timings; does not authenticate measurements."""
import json
import pathlib
import re
import sys

SHA = re.compile(r"[0-9a-f]{64}\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")
GIB = 1024 ** 3
COMMON = ("vm_identity", "cpu", "lean_version", "lake_version", "tool_sha256",
          "cache_sha256", "image_sha256", "unchanged_inputs_sha256", "memory_max", "swap_max", "threads", "jobs")


def digest(value, pattern):
    return isinstance(value, str) and pattern.fullmatch(value) is not None


def valid_environment(env):
    if not isinstance(env, dict):
        return False
    if any(not isinstance(env.get(k), str) or not env[k] for k in ("vm_identity", "cpu", "lean_version", "lake_version")):
        return False
    if any(not digest(env.get(k), SHA) for k in ("tool_sha256", "cache_sha256", "image_sha256", "unchanged_inputs_sha256")):
        return False
    return (type(env.get("memory_max")) is int and 0 < env["memory_max"] <= 12 * GIB
            and type(env.get("swap_max")) is int and env["swap_max"] == 0
            and type(env.get("threads")) is int and env["threads"] == 1
            and type(env.get("jobs")) is int and env["jobs"] == 1)


def compare(before, after):
    errors = []
    if not isinstance(before, dict) or not isinstance(after, dict):
        return {"verdict": "invalid", "errors": ["invalid records"]}
    for side, row in (("before", before), ("after", after)):
        path = row.get("path")
        if (not isinstance(path, str) or not path.endswith(".lean") or path.startswith("/") or "\\" in path
                or any(part in ("", ".", "..") for part in path.split("/"))):
            errors.append(f"{side}: invalid path")
        if (not valid_environment(row.get("environment")) or not digest(row.get("head"), COMMIT)
                or not digest(row.get("source_sha256"), SHA)):
            errors.append(f"{side}: invalid provenance")
        if row.get("status") != "ok" or type(row.get("exit_code")) is not int or row["exit_code"] != 0 or row.get("fresh") is not True:
            errors.append(f"{side}: measurement failed or not fresh")
        if type(row.get("wall_ns")) is not int or not 0 < row["wall_ns"] <= 300_000_000_000:
            errors.append(f"{side}: invalid wall time")
        if type(row.get("peak_rss_kib")) is not int or row["peak_rss_kib"] <= 0:
            errors.append(f"{side}: invalid RSS")
        if type(row.get("minimum_available")) is not int or row["minimum_available"] < 4 * GIB:
            errors.append(f"{side}: insufficient headroom")
    if before.get("path") != after.get("path"):
        errors.append("paths differ")
    if valid_environment(before.get("environment")) and valid_environment(after.get("environment")):
        if any(before["environment"][key] != after["environment"][key] for key in COMMON):
            errors.append("environment or unchanged-input identity differs")
    if errors:
        return {"verdict": "invalid", "errors": errors}
    # Integer arithmetic avoids rounding a result at the exact 10% boundary.
    if after["wall_ns"] * 10 > before["wall_ns"] * 11:
        return {"verdict": "stop-slowdown", "errors": []}
    return {"verdict": "within-bound", "errors": []}



def compare_all(expected_paths, before, after):
    """Check every supplied expected path; inputs remain unauthenticated."""
    if (not isinstance(expected_paths, list) or not expected_paths or
            any(not isinstance(path, str) or not path.endswith(".lean") or path.startswith("/")
                or "\\" in path or any(part in ("", ".", "..") for part in path.split("/"))
                for path in expected_paths) or len(set(expected_paths)) != len(expected_paths) or
            not isinstance(before, list) or not isinstance(after, list)):
        return {"verdict": "invalid", "errors": ["invalid expected paths or records"], "slowdowns": []}
    expected = set(expected_paths)
    errors = []
    indexed = []
    for label, records in (("before", before), ("after", after)):
        found = {}
        for row in records:
            if not isinstance(row, dict) or not isinstance(row.get("path"), str):
                errors.append(f"{label}: malformed row")
                continue
            path = row["path"]
            if path in found:
                errors.append(f"{label}: duplicate {path}")
            found.setdefault(path, []).append(row)
            if path not in expected:
                errors.append(f"{label}: unexpected {path}")
        errors.extend(f"{label}: missing {path}" for path in sorted(expected - found.keys()))
        indexed.append(found)
    slowdowns = []
    for path in sorted(expected & indexed[0].keys() & indexed[1].keys()):
        # Do not hide a valid slowdown behind a duplicated faster row.
        stop = False
        for first in indexed[0][path]:
            for second in indexed[1][path]:
                result = compare(first, second)
                if result["verdict"] == "stop-slowdown":
                    stop = True
                elif result["verdict"] != "within-bound":
                    errors.extend(f"{path}: {error}" for error in result["errors"])
        if stop:
            slowdowns.append(path)
    verdict = "stop-slowdown" if slowdowns else "invalid" if errors else "within-bound"
    return {"verdict": verdict, "errors": errors, "slowdowns": slowdowns}

def main():
    if len(sys.argv) != 2:
        print("usage: slowdown_compare.py INPUT.json", file=sys.stderr)
        return 2
    try:
        data = json.loads(pathlib.Path(sys.argv[1]).read_text())
        if "expected_paths" in data:
            result = compare_all(data["expected_paths"], data["before"], data["after"])
        else:
            result = compare(data["before"], data["after"])
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 1
    print(json.dumps({**result, "authentication": "not established"}))
    return 0 if result["verdict"] == "within-bound" else 1


if __name__ == "__main__":
    sys.exit(main())
