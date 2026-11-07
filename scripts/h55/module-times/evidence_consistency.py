#!/usr/bin/env python3
"""Check supplied timing data for consistency; inputs are not authenticated."""
import json
import math
import pathlib
import re
import sys

SHA = re.compile(r"[0-9a-f]{64}\Z")
HEAD = re.compile(r"[0-9a-f]{40}\Z")
GIB = 1024 ** 3


def valid_digest(value, pattern):
    return isinstance(value, str) and pattern.fullmatch(value) is not None



def valid_path(path):
    return (isinstance(path, str) and path.endswith(".lean") and not path.startswith("/")
            and "\\" not in path and all(part not in ("", ".", "..") for part in path.split("/")))

def validate(inventory, binding, records):
    if not isinstance(inventory, list) or not inventory or not isinstance(binding, dict) or not isinstance(records, list):
        return ["invalid inventory, binding or records"]
    if (not valid_digest(binding.get("head"), HEAD) or
            any(not valid_digest(binding.get(k), SHA) for k in ("tool_sha256", "cache_sha256", "image_sha256")) or
            any(not isinstance(binding.get(k), str) or not binding[k] for k in ("vm_identity", "lean_version", "lake_version"))):
        return ["invalid provenance binding"]
    expected = {}
    for row in inventory:
        if (not isinstance(row, dict) or not valid_path(row.get("path")) or
                not valid_digest(row.get("sha256"), SHA) or row["path"] in expected):
            return ["invalid or duplicate inventory"]
        expected[row["path"]] = row["sha256"]
    errors, seen, mono_intervals, boot_intervals = [], set(), [], []
    for record in records:
        if not isinstance(record, dict) or not isinstance(record.get("path"), str):
            errors.append("invalid record path")
            continue
        path = record["path"]
        if path in seen:
            errors.append(f"duplicate: {path}")
        seen.add(path)
        if path not in expected or record.get("source_sha256") != expected.get(path):
            errors.append(f"unexpected path or source mismatch: {path}")
        if any(record.get(k) != binding[k] for k in binding):
            errors.append(f"provenance mismatch: {path}")
        if record.get("cache_after_sha256") != binding["cache_sha256"]:
            errors.append(f"cache changed: {path}")
        if record.get("status") != "ok" or type(record.get("exit_code")) is not int or record["exit_code"] != 0 or record.get("fresh") is not True:
            errors.append(f"failed or nonfresh: {path}")
        if type(record.get("lean_jobs")) is not int or record["lean_jobs"] != 1 or type(record.get("lean_threads")) is not int or record["lean_threads"] != 1:
            errors.append(f"nonserial: {path}")
        resource = record.get("resources")
        if (not isinstance(resource, dict) or type(resource.get("memory_max")) is not int or
                not 0 < resource["memory_max"] <= 12 * GIB or resource.get("swap_max") != 0 or
                type(resource.get("swap_max")) is not int or type(resource.get("minimum_available")) is not int or
                resource["minimum_available"] < 4 * GIB):
            errors.append(f"invalid resource evidence: {path}")
        rss = record.get("peak_rss_kib")
        if type(rss) is not int or rss <= 0:
            errors.append(f"invalid RSS: {path}")
        starts = [record.get(k) for k in ("mono_start_ns", "mono_end_ns", "boot_start_ns", "boot_end_ns")]
        if any(type(v) is not int or v < 0 for v in starts):
            errors.append(f"invalid clock values: {path}")
            continue
        mono_ns = starts[1] - starts[0]
        boot_ns = starts[3] - starts[2]
        if not 0 < mono_ns <= 300_000_000_000 or not 0 < boot_ns <= 300_000_000_000:
            errors.append(f"invalid or inconsistent timing: {path}")
            continue
        mono_intervals.append((starts[0], starts[1], path))
        boot_intervals.append((starts[2], starts[3], path))
        mono = mono_ns / 1e9
        boot = boot_ns / 1e9
        wall = record.get("wall_seconds")
        if (type(wall) not in (int, float) or not math.isfinite(wall) or not 0 < wall <= 300 or
                not 0 < mono <= 300 or not 0 < boot <= 300 or
                abs(mono - boot) > max(.05, boot * .01) or abs(wall - mono) > .05):
            errors.append(f"invalid or inconsistent timing: {path}")
    for label, intervals in (("monotonic", mono_intervals), ("boottime", boot_intervals)):
        intervals.sort()
        for previous, current in zip(intervals, intervals[1:]):
            if current[0] < previous[1]:
                errors.append(f"overlapping {label} intervals: {previous[2]} and {current[2]}")
    errors.extend(f"missing: {path}" for path in sorted(expected.keys() - seen))
    return errors


def main():
    if len(sys.argv) != 2:
        print("usage: evidence_consistency.py INPUT.json", file=sys.stderr)
        return 2
    try:
        data = json.loads(pathlib.Path(sys.argv[1]).read_text())
        errors = validate(data["inventory"], data["binding"], data["records"])
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"invalid input: {exc}", file=sys.stderr)
        return 1
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("consistency only: input provenance, measurements and inventory remain unauthenticated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
