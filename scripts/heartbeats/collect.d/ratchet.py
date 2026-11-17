#!/usr/bin/env python3
"""Heartbeat ratchet over collect.sh output (scripts/heartbeats/README.md).

write BASELINE RUN: record each collected module's total and its commands of at
least --min units (default 10), keeping the other modules already in BASELINE.
check BASELINE RUN: fail when a module or recorded command exceeds its baseline
by more than --tolerance percent (default 1) and by more than 1 unit; a
decrease, a new or a removed entry only prints.
"""
import argparse, json, sys

FLOOR = 1.0  # units; below this a growth is noise (H1076: 1k raw out of 973M)


def entries(row, min_units):
    """Commands keyed by declared name, else `kind#n` (n-th unnamed of that kind)."""
    out, seen = {}, {}
    for c in row["commands"]:
        key = c["name"]
        if key is None:
            seen[c["kind"]] = seen.get(c["kind"], 0) + 1
            key = f'{c["kind"]}#{seen[c["kind"]]}'
        while key in out:
            key += "'"
        if c["heartbeats"] >= min_units:
            out[key] = {"heartbeats": c["heartbeats"], "line": c["line"]}
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=["write", "check"])
    p.add_argument("baseline")
    p.add_argument("run")
    p.add_argument("--tolerance", type=float, default=1.0)
    p.add_argument("--min", type=float, default=None)
    a = p.parse_args()
    rows = [json.loads(l) for l in open(a.run) if l.strip()]
    try:
        base = json.load(open(a.baseline))
    except FileNotFoundError:
        if a.mode == "check":
            sys.exit(f"ratchet: no baseline {a.baseline}; create it with --write")
        base = {"min_units": 10, "modules": {}}
    min_units = base.get("min_units", 10) if a.min is None else a.min
    bad = [r["module"] for r in rows if r["errors"]]
    if bad:
        print(f"ratchet: elaboration errors in {', '.join(bad)}; not compared", file=sys.stderr)
    rows = [r for r in rows if not r["errors"]]
    if a.mode == "write":
        if bad:
            return 1
        for r in rows:
            base["modules"][r["module"]] = {"heartbeats": r["heartbeats"], "commands": entries(r, min_units)}
        base["modules"] = dict(sorted(base["modules"].items()))
        with open(a.baseline, "w") as f:
            json.dump(base, f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"ratchet: wrote {len(rows)} module(s) to {a.baseline}", file=sys.stderr)
        return 0
    fails = 0

    def compare(label, old, new):
        nonlocal fails
        limit = old * (1 + a.tolerance / 100)
        if new > limit and new - old > FLOOR:
            fails += 1
            print(f"FAIL {label}: {new:.3f} > {old:.3f} (+{100 * (new - old) / max(old, 1e-9):.2f}%, tolerance {a.tolerance}%)")
        elif new < old - FLOOR:
            print(f"decrease {label}: {new:.3f} < {old:.3f}")

    for r in rows:
        m = r["module"]
        old = base["modules"].get(m)
        if old is None:
            print(f"new module {m}: {r['heartbeats']:.3f}")
            continue
        compare(m, old["heartbeats"], r["heartbeats"])
        cur = entries(r, 0)
        for k, o in old["commands"].items():
            if k in cur:
                compare(f"{m} {k} (line {cur[k]['line']})", o["heartbeats"], cur[k]["heartbeats"])
            else:
                print(f"removed {m} {k}")
        for k, c in entries(r, min_units).items():
            if k not in old["commands"]:
                print(f"new {m} {k} (line {c['line']}): {c['heartbeats']:.3f}")
    print(f"ratchet: {len(rows)} module(s), {fails} over baseline", file=sys.stderr)
    return 1 if fails or bad else 0


if __name__ == "__main__":
    sys.exit(main())
