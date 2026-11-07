#!/usr/bin/env python3
"""Source census, not a Lean elaborator or a proof of premise feasibility.

Keep every named theorem/lemma in module-map files. Exact source signatures,
full source hashes, and preceding context are retained for elaborated review.
No hypothesis heuristic filters declarations out. Bulk JSON belongs off Git.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MAP = "docs/module-map/bytecode-selection.md"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def mask(text):
    """Blank nested comments and strings, preserving positions and newlines."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            width = 1
            if text.startswith("/-", i):
                depth += 1
                width = 2
            elif text.startswith("-/", i):
                depth -= 1
                width = 2
        elif string:
            width = 2 if text[i] == "\\" and i + 1 < len(text) else 1
            if text[i] == '"':
                string = False
        elif text.startswith("/-", i):
            depth = 1
            width = 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
            continue
        elif text[i] == '"':
            string = True
            width = 1
        else:
            i += 1
            continue
        for j in range(i, min(i + width, len(text))):
            if text[j] != "\n":
                out[j] = " "
        i += width
    if depth or string:
        raise ValueError("unclosed comment or string")
    return "".join(out)


EVENT = re.compile(
    r"(?m)^[ \t]*(?:(?:@\[[^\n]*?\]|private|protected|noncomputable)\s+)*"
    r"(?P<kind>namespace|section|end|theorem|lemma)\b[ \t]*(?P<name>[^\s({:]*)(?=[\s({:]|$)"
)


def declarations(text):
    clean = mask(text)
    stack = []
    rows = []
    for event in EVENT.finditer(clean):
        kind, name = event.group("kind", "name")
        if kind in ("namespace", "section"):
            stack.append((kind, name))
            continue
        if kind == "end":
            if stack:
                stack.pop()
            continue
        if not name:
            raise ValueError("unnamed theorem")
        depth = 0
        i = event.end()
        while i < len(clean):
            if depth == 0 and clean.startswith(":=", i):
                break
            if clean[i] in "({[⦃":
                depth += 1
            elif clean[i] in ")}]⦄":
                depth -= 1
                if depth < 0:
                    raise ValueError("unbalanced signature: " + name)
            i += 1
        else:
            raise ValueError("no proof delimiter: " + name)
        start = event.start()
        signature = text[start:i]
        namespace = ".".join(n for k, n in stack if k == "namespace")
        # Source-level names are candidates: private name mangling, open names,
        # section generalization and macro declarations require elaboration.
        rows.append({
            "name_candidate": (namespace + "." if namespace else "") + name,
            "kind": kind,
            "name_line": text.count("\n", 0, event.start("name")) + 1,
            "name_column": event.start("name") - (text.rfind("\n", 0, event.start("name")) + 1),
            "line": text.count("\n", 0, start) + 1,
            "byte_start": len(text[:start].encode()),
            "byte_end": len(text[:i].encode()),
            "signature": signature,
            "signature_sha256": sha(signature.encode()),
            "preceding_context_sha256": sha(text[:start].encode()),
            "owner": "UNRESOLVED: area producer/coordinator ownership mapping required",
            "hypotheses": "UNCLASSIFIED: retain parameters, section variables and implications",
            "simultaneous_witness": None,
            "status": "uncovered",
        })
    return rows


def mapped_references(text):
    """Normalize the frozen roster without treating imported dependencies as scope."""
    refs = re.findall(r"`([^`]+\.lean)`", text)
    paths = [ref if ref.startswith(("Solidity/", "Bridge/")) else "Solidity/" + ref for ref in refs]
    return sorted(set(paths)), len(refs)


def mapped_paths(repo):
    data = (repo / MAP).read_bytes()
    original = subprocess.check_output(["git", "show", BASE + ":" + MAP], cwd=repo)
    if data != original:
        raise ValueError("frozen module map differs from base")
    paths, count = mapped_references(data.decode())
    for path in paths:
        if not (repo / path).is_file():
            raise ValueError("missing mapped file: " + path)
    return paths, count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = args.repo.resolve()
    paths, reference_count = mapped_paths(repo)
    files, rows = [], []
    for path in paths:
        data = (repo / path).read_bytes()
        text = data.decode()
        # Frozen interface fidelity is checked against Git, not a mutable digest.
        original = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo)
        if data != original:
            raise ValueError("frozen source differs from base: " + path)
        files.append({"path": path, "sha256": sha(data)})
        for row in declarations(text):
            row["path"] = path
            row["id"] = path + ":" + str(row["byte_start"])
            rows.append(row)
    assert len({r["id"] for r in rows}) == len(rows)
    result = {
        "schema": 1, "base": BASE,
        "boundary": "Source candidates only; not an elaborated hypothesis or field census",
        "module_map_sha256": sha((repo / MAP).read_bytes()),
        "module_map_references": reference_count,
        "files": files, "declarations": rows,
        "summary": {"files": len(files), "named_theorem_candidates": len(rows),
                    "witnesses_verified": 0, "uncovered_candidates": len(rows)},
    }
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
