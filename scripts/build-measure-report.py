#!/usr/bin/env python3
"""Summarise a `scripts/build-measure.py` output directory as Markdown.

Usage: scripts/build-measure-report.py DIR [--log LOG] [--top N]

Prints the run summary, the N slowest and the N most memory-hungry `lean`
processes, and the lean-RSS/MemAvailable extremes per concurrency level.
With `--log` (the command's captured output), the elapsed time of a module is
the one Lake prints (`Built Mod (2.5s)`), which is exact; the watcher's
sampled lifetime is the fallback. Failed jobs (`✖`) are listed.
Only the standard library is used.
"""
import argparse
import csv
import json
import os
import re

LAKE_LINE = re.compile(r"(?:✔|⚠) \[\d+/\d+\] Built (\S+)(?::\S+)? \((\d+(?:\.\d+)?)(ms|s|m)\)")
FAIL_LINE = re.compile(r"✖ \[\d+/\d+\] (.*)")


def module_name(path):
    path = path[:-5] if path.endswith(".lean") else path
    for prefix in ("Bridge/vendor/", "Bridge/", "vendor/LeanTeX/"):
        if path.startswith(prefix):
            path = path[len(prefix):]
            break
    return path.replace("/", ".")


def lake_times(log):
    times, failed = {}, []
    with open(log, errors="replace") as f:
        for line in f:
            m = LAKE_LINE.search(line)
            if m:
                v = float(m.group(2)) * {"ms": 0.001, "s": 1, "m": 60}[m.group(3)]
                times[m.group(1)] = max(times.get(m.group(1), 0), v)
                continue
            m = FAIL_LINE.search(line)
            if m:
                failed.append(m.group(1).strip())
    return times, failed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--log")
    ap.add_argument("--top", type=int, default=20)
    ns = ap.parse_args()
    with open(os.path.join(ns.dir, "summary.json")) as f:
        summary = json.load(f)
    with open(os.path.join(ns.dir, "modules.csv")) as f:
        rows = [r for r in csv.DictReader(f) if r["kind"] == "lean"]
    with open(os.path.join(ns.dir, "samples.csv")) as f:
        samples = list(csv.DictReader(f))
    failed = []
    if ns.log:
        times, failed = lake_times(ns.log)
        for r in rows:
            name = module_name(r["module"])
            r["module"] = name
            if name in times:
                r["elapsed_s"] = f"{times[name]:.1f}"
    else:
        for r in rows:
            r["module"] = module_name(r["module"])

    print("## Summary\n")
    for k, v in summary.items():
        if k == "kernel_oom":
            v = len(v)
        print(f"- `{k}`: {v}")
    total = sum(float(r["elapsed_s"]) for r in rows)
    print(f"- summed lean process time: {total:.0f} s over {len(rows)} processes")
    for line in failed:
        print(f"- failed: `{line}`")

    def table(title, key):
        print(f"\n## {title}\n")
        print("| # | Module | Elapsed (s) | Peak RSS (MiB) | Start (s) |")
        print("|---:|---|---:|---:|---:|")
        for i, r in enumerate(sorted(rows, key=key, reverse=True)[: ns.top], 1):
            print(f"| {i} | `{r['module']}` | {r['elapsed_s']} | {r['peak_rss_mib']} | {r['start_s']} |")

    table(f"{ns.top} slowest", lambda r: float(r["elapsed_s"]))
    table(f"{ns.top} by peak RSS", lambda r: int(r["peak_rss_mib"]))

    print("\n## By concurrent lean workers\n")
    print("| Workers | Samples | Max lean RSS (MiB) | Min MemAvailable (MiB) |")
    print("|---:|---:|---:|---:|")
    by = {}
    for s in samples:
        w = int(s["lean_workers"])
        rss, avail, n = by.get(w, (0, 1 << 62, 0))
        by[w] = (max(rss, int(s["lean_rss_kib"])), min(avail, int(s["mem_available_kib"])), n + 1)
    for w in sorted(by):
        rss, avail, n = by[w]
        print(f"| {w} | {n} | {rss // 1024} | {avail // 1024} |")


if __name__ == "__main__":
    main()
