#!/usr/bin/env python3
"""Summarise a `scripts/build-measure.py` output directory as Markdown.

Usage: scripts/build-measure-report.py DIR [--log LOG] [--top N]
       scripts/build-measure-report.py DIR --log LOG --deps MODULE...

Prints the run summary, the N slowest and the N most memory-hungry `lean`
processes, and the lean-RSS/MemAvailable extremes per concurrency level.
With `--log` (the command's captured output), the elapsed time of a module is
the one Lake prints (`Built Mod (2.5s)`), which is exact; the watcher's
sampled lifetime is the fallback, and a module Lake built faster than one
sample appears with Lake's time and no RSS. Failed jobs (`✖`) are listed.
With `--deps`, prints for each MODULE the number of its transitive
dependents among the modules the run built (from the `import` lines of the
sources under the working directory) and their summed Lake time; a module
that failed (no `Built` line) is counted with the time Lake printed when it
failed. Only the standard library is used.
"""
import argparse
import csv
import json
import os
import re

# Lake 4.24 marks a job ✔, ⚠ or ℹ by its worst log level; times are `Nms`,
# `N.Ns` or `Ns`, never minutes.
LAKE_LINE = re.compile(r"[✔⚠ℹ] \[\d+/\d+\] (?:\(Optional\) )?Built (\S+) \((\d+(?:\.\d+)?)(ms|s)\)")
FAIL_LINE = re.compile(r"✖ \[\d+/\d+\] (.*)")
FAIL_TIME = re.compile(r"Building (\S+) \((\d+(?:\.\d+)?)(ms|s)\)")


def module_name(path):
    path = path[:-5] if path.endswith(".lean") else path
    m = re.match(r"(?:Bridge/)?\.lake/packages/[^/]+/(.*)", path)
    if m:
        path = m.group(1)
    else:
        for prefix in ("Bridge/vendor/", "Bridge/", "vendor/LeanTeX/"):
            if path.startswith(prefix):
                path = path[len(prefix):]
                break
    return path.replace("/", ".")


def seconds(value, unit):
    return float(value) * (0.001 if unit == "ms" else 1)


def lake_times(log):
    times, failed = {}, []
    with open(log, errors="replace") as f:
        for line in f:
            m = LAKE_LINE.search(line)
            if m:
                if ":" not in m.group(1):  # skip the `:c.o`/`:exe` facets
                    times[m.group(1)] = seconds(m.group(2), m.group(3))
                continue
            m = FAIL_LINE.search(line)
            if m:
                failed.append(m.group(1).strip())
                t = FAIL_TIME.search(m.group(1))
                if t and t.group(1) not in times:
                    times[t.group(1)] = seconds(t.group(2), t.group(3))
    return times, failed


def print_deps(modules, times):
    imports = {}
    for dirpath, dirnames, filenames in os.walk("."):
        dirnames[:] = [d for d in dirnames if d not in (".git", ".lake", "node_modules")]
        for fn in filenames:
            if fn.endswith(".lean"):
                path = os.path.relpath(os.path.join(dirpath, fn))
                with open(path, errors="replace") as f:
                    names = [w for line in f if line.startswith("import ")
                             for w in line.split()[1:]]
                imports[module_name(path)] = names
    users = {}
    for name, names in imports.items():
        if name in times:
            for dep in names:
                users.setdefault(dep, set()).add(name)
    print("| Module | Dependents built | Their summed time (s) | Own time (s) |")
    print("|---|---:|---:|---:|")
    for m in modules:
        found, todo = set(), [m]
        while todo:
            for u in users.get(todo.pop(), ()):
                if u not in found:
                    found.add(u)
                    todo.append(u)
        print(f"| `{m}` | {len(found)} | {sum(times[u] for u in found):.0f} | {times.get(m, 0):.1f} |")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("dir")
    ap.add_argument("--log")
    ap.add_argument("--top", type=int, default=20)
    ap.add_argument("--deps", nargs="+")
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
        if ns.deps:
            print_deps(ns.deps, times)
            return
        seen = set()
        for r in rows:
            name = module_name(r["module"])
            r["module"] = name
            seen.add(name)
            if name in times:
                r["elapsed_s"] = f"{times[name]:.1f}"
        for name, t in times.items():
            if name not in seen:
                rows.append({"module": name, "kind": "lean", "start_s": "", "end_s": "",
                             "elapsed_s": f"{t:.1f}", "peak_rss_mib": "0"})
    else:
        for r in rows:
            r["module"] = module_name(r["module"])

    print("## Summary\n")
    for k, v in summary.items():
        if k == "kernel_oom":
            v = len(v)
        print(f"- `{k}`: {v}")
    total = sum(float(r["elapsed_s"]) for r in rows)
    print(f"- summed lean time: {total:.0f} s over {len(rows)} modules")
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
