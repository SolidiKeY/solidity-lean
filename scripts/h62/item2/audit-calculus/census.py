#!/usr/bin/env python3
"""Frozen source census, deliberately NOT an elaborated-hypothesis certificate.

Bulk JSON belongs outside git. Preserve all declarations (including private and
hypothesis-free ones) until an independent kernel census can discharge coverage.
No heuristic classification is allowed to mark a witness proved.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
AREAS = ("calculus", "try-evidence")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def expand(path):
    match = re.search(r"\{([^{}]*)\}", path)
    if not match:
        return [path]
    return list(itertools.chain.from_iterable(
        expand(path[:match.start()] + choice + path[match.end():])
        for choice in match[1].split(",")))


def mask(source):
    """Blank comments and string literals, preserving offsets and newlines."""
    result = list(source)
    i, depth = 0, 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                result[i:i+2] = "  "; depth += 1; i += 2
            elif source.startswith("-/", i):
                result[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if source[i] != "\n": result[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                result[i] = " "; i += 1
                if i < len(source):
                    if source[i] != "\n": result[i] = " "
                    i += 1
            elif source[i] == '"':
                result[i] = " "; string = False; i += 1
            else:
                if source[i] != "\n": result[i] = " "
                i += 1
        elif source.startswith("/-", i):
            result[i:i+2] = "  "; depth = 1; i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result[i:end] = " " * (end-i); i = end
        elif source[i] == '"':
            result[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("unclosed comment/string")
    return "".join(result)


COMMAND = re.compile(
    r"^[ \t]*(?:(?:@\[[^\n]*?\]|private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>namespace|section|mutual|end|variable|include|omit|theorem|lemma)\b(?P<tail>[^\n]*)", re.M)
DECL = re.compile(r"\s+([^\s({:]+)")


def signature_end(clean, start):
    stack = []
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    i = start
    pending_lets = 0
    while i < len(clean):
        char = clean[i]
        if char in pairs: stack.append(pairs[char])
        elif stack and char == stack[-1]: stack.pop()
        elif not stack and re.match(r"(?:let|letI|have)\b", clean[i:]) and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] == "_")):
            pending_lets += 1
        elif not stack and clean.startswith(":=", i):
            if pending_lets: pending_lets -= 1
            else: return i
        elif not stack and char == "\n" and re.match(r"[ \t]*\|", clean[i+1:]): return i
        elif not stack and re.match(r"where\b", clean[i:]) and (i == 0 or clean[i-1].isspace()):
            return i
        i += 1
    raise ValueError("declaration body delimiter not found")


def declarations(source, path):
    clean = mask(source)
    commands = list(COMMAND.finditer(clean))
    stack, rows = [], []
    for index, command in enumerate(commands):
        kind, tail = command["kind"], command["tail"].strip()
        if kind in ("namespace", "section", "mutual"):
            stack.append({"kind": kind, "name": tail.split()[0] if tail else "", "variables": []})
        elif kind == "end":
            if stack: stack.pop()
        elif kind in ("variable", "include", "omit"):
            # Preserve every continuation line, including semantic assumptions.
            end = command.end()
            indent = len(command[0]) - len(command[0].lstrip(" \t"))
            for line in clean[end:].splitlines(keepends=True):
                if not line.strip():
                    end += len(line)
                    continue
                width = len(line) - len(line.lstrip(" \t"))
                if width <= indent: break
                end += len(line)
            if not stack: stack.append({"kind": "section", "name": "", "variables": []})
            stack[-1]["variables"].append(source[command.start():end].strip())
        else:
            name_match = DECL.match(command["tail"])
            if not name_match: raise ValueError(f"unparsed declaration in {path}: {tail}")
            name = name_match[1]
            stop = signature_end(clean, command.start())
            signature = source[command.start():stop].strip()
            prefix = ".".join(x["name"] for x in stack if x["kind"] == "namespace")
            fq = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(filter(None, (prefix, name)))
            rows.append({"source_name": fq, "name_status": "source-inferred; kernel confirmation pending",
                         "file": path, "line": source.count("\n", 0, command.start())+1,
                         "kind": kind, "private": bool(re.search(r"\bprivate\b", clean[command.start():command.start()+command[0].find(kind)])),
                         "signature": signature, "signature_sha256": digest(signature.encode()),
                         "signature_status": "lexical candidate; parser/kernel confirmation required",
                         "raw_source_tail": source[command.start():commands[index+1].start() if index+1 < len(commands) else len(source)],
                         "section_directive_history": [v for x in stack for v in x["variables"]],
                         "hypotheses": "unclassified pending elaborated telescope",
                         "joint_witness": "pending", "owner": "unresolved area producer; coordinator resolution required"})
    return rows


def mapped_files(root):
    files, missing = {}, []
    for area in AREAS:
        data = (root / f"docs/module-map/{area}.md").read_text()
        # Include all explicitly named module paths, even prose references.
        # This is conservative accounting; none may be silently excluded.
        for spelling in re.findall(r"`([^`]+\.lean)`", data):
            for relative in expand(spelling):
                path = relative if relative.startswith("Solidity/") else "Solidity/" + relative
                if not (root/path).is_file():
                    missing.append({"area": area, "path": path})
                else:
                    files.setdefault(path, set()).add(area)
    return files, missing


def generate(root):
    files, missing = mapped_files(root)
    rows, generators, sources = [], [], []
    for path, areas in sorted(files.items()):
        source = (root/path).read_text()
        sources.append({"path": path, "areas": sorted(areas), "sha256": digest((root/path).read_bytes())})
        for row in declarations(source, path):
            row["areas"] = sorted(areas)
            row["id"] = f"{path}:{row['line']}:{row['source_name']}"
            rows.append(row)
        for match in re.finditer(r"^[ \t]*#(?:replay|derive)[^\n]*", mask(source), re.M):
            generators.append({"file": path, "line": source.count("\n",0,match.start())+1,
                               "command": source[match.start():match.end()].strip(),
                               "status": "generated declarations require kernel enumeration"})
    ids = [r["id"] for r in rows]
    if len(ids) != len(set(ids)): raise ValueError("duplicate source declaration ID")
    return {"schema": 1, "base": BASE,
            "coverage_status": "SOURCE CANDIDATES ONLY; elaborated census, owners and witnesses pending",
            "sources": sources, "missing_module_paths": missing,
            "declarations": rows, "generator_commands": generators,
            "counts": {"files": len(sources), "declarations": len(rows),
                       "private": sum(r["private"] for r in rows), "joint_witnesses_verified": 0,
                       "uncovered_source_candidates": len(rows), "generator_commands": len(generators)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    if args.out.resolve().is_relative_to(root):
        parser.error("H44: write bulk evidence outside the repository")
    tracked = subprocess.check_output(["git", "diff", BASE, "--", "Solidity", "docs/module-map"], cwd=root)
    if tracked: raise SystemExit("frozen source or module map differs from base")
    result = generate(root)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(result, indent=2, ensure_ascii=False)+"\n").encode()
    args.out.write_bytes(data)
    args.out.with_suffix(args.out.suffix+".sha256").write_text(digest(data)+"  "+args.out.name+"\n")
    print(json.dumps({"output": str(args.out.resolve()), "sha256": digest(data), **result["counts"]}, sort_keys=True))


if __name__ == "__main__":
    main()
