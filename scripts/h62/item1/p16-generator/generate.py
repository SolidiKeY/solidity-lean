#!/usr/bin/env python3
"""Render the P16 import boundary without editing the owner-controlled file."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
TARGET = ROOT / "Solidity/Yul/Interfaces/P16.lean"
NAME = "Solidity/Yul/Interfaces/P16.lean"
MODULE = re.compile(r"Solidity(?:\.[A-Za-z_][A-Za-z_0-9]*)+")


def registered_fragments():
    """Validate the frozen baseline and independently registered extensions."""
    inventory = json.loads((HERE / "baseline-inventory.json").read_bytes().decode("utf-8"))
    if set(inventory) != {"imports", "body"}:
        raise ValueError("invalid baseline inventory keys")
    expected = {}
    for kind in ("imports", "body"):
        entries = inventory[kind]
        if not isinstance(entries, dict) or not entries:
            raise ValueError("invalid baseline " + kind + " inventory")
        for name, digest in entries.items():
            if not re.fullmatch(r"[0-9]{3}(?:-[A-Za-z_][A-Za-z_0-9]*)?\.txt", name) or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
                raise ValueError("invalid baseline " + kind + " entry")
            path = HERE / kind / name
            if not path.is_file() or path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                raise ValueError("missing or changed baseline " + kind + " fragment " + name)
        expected[kind] = set(entries)
    ids = set()
    directory = HERE / "registrations"
    files = sorted(directory.iterdir())
    for registration in files:
        if registration.name == "README.md" and registration.is_file() and not registration.is_symlink():
            continue
        if not registration.is_file() or registration.is_symlink() or registration.suffix != ".json":
            raise ValueError("unexpected registration entry " + registration.name)
        ident = registration.stem
        if not re.fullmatch(r"(?:VY1|VY3)-[A-Za-z_][A-Za-z_0-9]*", ident):
            raise ValueError("invalid extension registration " + registration.name)
        if ident in ids:
            raise ValueError("duplicate extension registration " + ident)
        ids.add(ident)
        entry = json.loads(registration.read_bytes().decode("utf-8"))
        if not isinstance(entry, dict) or set(entry) != {"module", "documentation"}:
            raise ValueError("invalid registration fields " + ident)
        module, doc = entry["module"], entry["documentation"]
        if not isinstance(doc, bool) or (module is not None and (not isinstance(module, str) or not MODULE.fullmatch(module))):
            raise ValueError("invalid registration values " + ident)
        if module is None and not doc:
            raise ValueError("empty registration " + ident)
        filename = "ext-" + ident + ".txt"
        if module is not None:
            expected["imports"].add(filename)
            path = HERE / "imports" / filename
            if path.is_file() and path.read_bytes() != (module + "\n").encode("utf-8"):
                raise ValueError("registration module mismatch " + ident)
        if doc:
            expected["body"].add(filename)
    for kind in ("imports", "body"):
        entries = list((HERE / kind).iterdir())
        if any(not p.is_file() or p.is_symlink() or p.suffix != ".txt" for p in entries):
            raise ValueError("unexpected " + kind + " entry")
        actual = {p.name for p in entries}
        missing, extra = expected[kind] - actual, actual - expected[kind]
        if missing or extra:
            raise ValueError(f"{kind} fragment mismatch: missing={sorted(missing)} extra={sorted(extra)}")
    return expected


def validate_doc(path, content):
    """Accept one nonempty, balanced Lean documentation comment only."""
    if "\r" in content or not content.startswith("/-!") or not content.endswith("-/\n") or not content[3:-3].strip():
        raise ValueError("invalid documentation fragment " + path.name)
    depth, index = 1, 3
    while index < len(content):
        pair = content[index:index + 2]
        if pair == "/-":
            depth += 1
            index += 2
        elif pair == "-/":
            depth -= 1
            index += 2
            if depth == 0:
                if content[index:] != "\n":
                    raise ValueError("trailing content in documentation fragment " + path.name)
                return
        else:
            index += 1
    raise ValueError("unbalanced documentation fragment " + path.name)


def render(require_sources=True):
    expected = registered_fragments()
    contents = [(HERE / "imports" / name).read_bytes().decode("utf-8") for name in sorted(expected["imports"])]
    if any(not x.endswith("\n") or x.count("\n") != 1 or "\r" in x for x in contents):
        raise ValueError("invalid import fragment formatting")
    nodes = [x[:-1] for x in contents]
    if not nodes or any(not MODULE.fullmatch(x) for x in nodes):
        raise ValueError("invalid or empty import manifest")
    if len(nodes) != len(set(nodes)):
        raise ValueError("duplicate manifest node")
    for node in nodes:
        if require_sources and not (ROOT / (node.replace(".", "/") + ".lean")).is_file():
            raise ValueError("missing source node " + node)
    body_files = [HERE / "body" / name for name in sorted(expected["body"])]
    body_parts = [p.read_bytes().decode("utf-8") for p in body_files]
    for path, part in zip(body_files, body_parts):
        validate_doc(path, part)
    body = "\n".join(body_parts)
    return nodes, "".join("import " + node + "\n" for node in nodes) + "\n" + body


def main():
    ap = argparse.ArgumentParser()
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true")
    group.add_argument("--render", action="store_true")
    group.add_argument("--patch", action="store_true")
    ap.add_argument("--migration", action="store_true", help="include the generated marker used by the adopted file")
    args = ap.parse_args()
    nodes, expected = render()
    if args.migration:
        expected = "-- Generated by scripts/h62/item1/p16-generator/generate.py; edit fragments, not this file.\n" + expected
    if args.render:
        sys.stdout.write(expected)
        return 0
    actual = TARGET.read_bytes().decode("utf-8")
    if args.patch:
        sys.stdout.writelines(difflib.unified_diff(actual.splitlines(keepends=True), expected.splitlines(keepends=True), fromfile="a/" + NAME, tofile="b/" + NAME))
        return 0
    if actual == expected:
        print(f"P16: reproduced exactly ({len(nodes)} import nodes)")
        return 0
    observed = re.findall(r"^import ([^\s]+)\s*$", actual, re.MULTILINE)
    for node in sorted(set(nodes) - set(observed)):
        print("P16: missing import " + node)
    for node in sorted(set(observed) - set(nodes)):
        print("P16: extra import " + node)
    if set(nodes) == set(observed):
        print("P16: non-generated order, duplicate, or body")
    return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, TypeError) as exc:
        print("P16 generator: " + str(exc), file=sys.stderr)
        sys.exit(2)
