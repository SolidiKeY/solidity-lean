#!/usr/bin/env python3
"""Produce annotation-only, owner-reviewable proposals without editing inputs.

These patches identify the existing reproduction helper. They do not change the
Lean declarations and do not implement a table migration or grant a file lease.
"""
import argparse
import difflib
import json
from pathlib import Path
import fixture_controls as fixture
import word_table as word

MARKERS = {
    "word": b"-- H55 reproduction: scripts/h55/vectors-tables/word_table.py (proof text remains authoritative).\n",
    "fixture": b"-- H55 reproduction: scripts/h55/vectors-tables/fixture_controls.py (fixture data remains authoritative).\n",
}

def inputs(kind):
    if kind == "word":
        records = word.collect(word.ROOT)
        if word.manifest(records) != json.loads(word.MANIFEST.read_text()): raise ValueError("WordTable inputs differ from pinned base")
        return [(word.AREA / name, (word.ROOT / word.AREA / name).read_bytes()) for name in word.NAMES]
    if kind == "fixture":
        if fixture.inventory(fixture.ROOT) != json.loads(fixture.MANIFEST.read_text()): raise ValueError("fixture inputs differ from pinned base")
        return [(fixture.CONTROL / name, (fixture.ROOT / fixture.CONTROL / name).read_bytes()) for name in fixture.names()]
    raise ValueError("unknown table")

def annotated(data, kind):
    if type(data) is not bytes or kind not in MARKERS or MARKERS[kind] in data: raise ValueError("input schema or marker already present")
    first, sep, rest = data.partition(b"\n")
    if not sep or not first.startswith(b"import "): raise ValueError("expected initial import")
    return first + b"\n" + MARKERS[kind] + rest

def proposal(kind):
    result = []
    for path, source in inputs(kind):
        target = annotated(source, kind)
        before = source.decode("utf-8").splitlines(keepends=True)
        after = target.decode("utf-8").splitlines(keepends=True)
        result.extend(difflib.unified_diff(before, after, fromfile="a/" + str(path), tofile="b/" + str(path), n=3))
    return "".join(result).encode("utf-8")

def main():
    p = argparse.ArgumentParser(); p.add_argument("kind", choices=("word", "fixture")); p.add_argument("output", type=Path); args = p.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(word.ROOT) or output.exists(): raise ValueError("output must be a new external file")
    patch = proposal(args.kind)
    output.write_bytes(patch)
    print(f"PASS: {args.kind} annotation proposal for {len(inputs(args.kind))} frozen files written to {output}")

if __name__ == "__main__": main()
