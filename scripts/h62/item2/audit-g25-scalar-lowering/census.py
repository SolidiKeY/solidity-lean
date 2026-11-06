#!/usr/bin/env python3
"""Frozen source census, not a Lean elaborator or a satisfiability proof.

Bulk signatures stay off git. Fail closed on unsupported declaration layout;
include all named theorems, even those without propositional premises. A later
kernel census must resolve auto-implicit/section parameters and proposition types.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MAP = "docs/module-map/g25-scalar-lowering.md"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def mask(source):
    # Preserve offsets and newlines while hiding strings and nested comments.
    out = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif source.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if source[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                out[i] = " "
                if i+1 < len(source): out[i+1] = " "
                i += 2
            else:
                if source[i] == '"': string = False
                if source[i] != "\n": out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end == -1: end = len(source)
            out[i:end] = " " * (end-i); i = end
        elif source[i] == '"':
            out[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string: raise ValueError("unterminated comment/string")
    return "".join(out)


def assignment_end(clean, start):
    nesting = []
    pairs = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    i = start
    pending_let_assignments = 0
    while i < len(clean):
        c = clean[i]
        if not nesting and (i == 0 or clean[i-1] == "\n"):
            if re.match(r"(?:private +)?(?:theorem|lemma|def|namespace|end)\b", clean[i:]):
                raise ValueError("missing assignment before next declaration")
        if not nesting and re.match(r"let\b", clean[i:]) and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] == "_")):
            pending_let_assignments += 1
        if not nesting and clean.startswith(":=", i):
            if pending_let_assignments:
                pending_let_assignments -= 1
                i += 2
                continue
            return i
        if c in pairs: nesting.append(pairs[c])
        elif c in pairs.values():
            if not nesting or nesting.pop() != c: raise ValueError("unbalanced signature")
        i += 1
    raise ValueError("missing theorem assignment")


def declarations(source, path):
    clean = mask(source)
    namespaces = list(re.finditer(r"(?m)^namespace ([\w.]+)\s*$", clean))
    if len(namespaces) != 1: raise ValueError(f"{path}: expected one namespace")
    namespace = namespaces[0].group(1)
    endings = list(re.finditer(r"(?m)^end ([\w.]+)\s*$", clean))
    if len(endings) != 1 or endings[0].group(1) != namespace:
        raise ValueError("unsupported namespace extent")
    # These files have no nested sections; reject changes to that assumption.
    if re.search(r"(?m)^section(?: |$)", clean): raise ValueError("section requires elaborator census")
    variables = list(re.finditer(r"(?m)^variable[^\n]*", clean))
    for v in variables:
        if not v.group().removeprefix("variable").strip():
            raise ValueError("multiline variable requires elaborator census")
        next_line = clean[v.end()+1:].split("\n", 1)[0].lstrip()
        if next_line.startswith(("{", "(", "[", "⦃")):
            raise ValueError("multiline variable requires elaborator census")
    pattern = r"(?m)^(?P<private>private +)?(?P<kind>theorem|lemma) +(?P<name>[\w.\']+)"
    result = []
    for match in re.finditer(pattern, clean):
        if not namespaces[0].end() <= match.start() < endings[0].start():
            raise ValueError("theorem outside supported namespace")
        if clean[match.end():match.end()+1] not in " \t\n({[:":
            raise ValueError("unsupported theorem identifier")
        end = assignment_end(clean, match.end())
        raw = source[match.start():end]
        result.append({
            "name": namespace + "." + match.group("name"),
            "visibility": "private" if match.group("private") else "public",
            "path": path,
            "line": source.count("\n", 0, match.start()) + 1,
            "signature": raw,
            "signature_sha256": digest(raw.encode()),
            "section_variables": [source[v.start():v.end()] for v in variables if v.end() < match.start()],
        })
    # Reject theorem spellings this limited scanner does not understand.
    tokens = list(re.finditer(r"\b(?:theorem|lemma)\b", clean))
    if len(tokens) != len(result): raise ValueError(f"{path}: unsupported theorem layout")
    names = [r["name"] for r in result]
    if len(set(names)) != len(names): raise ValueError(f"{path}: repeated source names")
    return result


SCHEDULING_PATH = "Solidity/Backend/Scalar/PowerBounds.lean"
SCHEDULING_EDIT = (b"-- Keep the 32 kernel-checked rows from retaining concurrent proof tasks.\n"
                   b"set_option Elab.async false\n\n")


def scheduling_only_change(path, frozen, actual):
    """Accept only the published pre-namespace scheduling insertion, not proof edits."""
    marker = b"-/\nnamespace Solidity.Backend.Scalar\n"
    return (path == SCHEDULING_PATH and marker in frozen and
            actual == frozen.replace(marker, b"-/\n" + SCHEDULING_EDIT +
                                      b"namespace Solidity.Backend.Scalar\n", 1))


def frozen_bytes(repo, path):
    frozen = subprocess.run(["git", "show", BASE+":"+path], cwd=repo,
                            check=True, stdout=subprocess.PIPE).stdout
    actual = (repo/path).read_bytes()
    if actual != frozen and not scheduling_only_change(path, frozen, actual):
        raise ValueError("frozen file mismatch: " + path)
    return actual


def census(repo, ownership):
    map_bytes = frozen_bytes(repo, MAP)
    modules = re.findall(r"`(Backend/[^`]+\.lean)`", map_bytes.decode())
    if len(set(modules)) != len(modules): raise ValueError("duplicate module rows")
    if not modules: raise ValueError("empty module map")
    items = {i["id"]: i for i in ownership["items"]}
    files = []
    records = []
    for module in modules:
        path = "Solidity/" + module
        content = frozen_bytes(repo, path)
        area = "G25" if module.startswith("Backend/Scalar/") else "G31"
        owner = items[area]
        rows = declarations(content.decode(), path)
        for row in rows:
            row.update(area=area, owner=owner["owner"], owner_key=owner["ownerKey"])
        records.extend(rows)
        files.append({"path":path, "sha256":digest(content), "area":area,
                      "owner_key":owner["ownerKey"], "named_theorems":len(rows),
                      "base_sha256":digest(subprocess.run(["git", "show", BASE+":"+path],
                        cwd=repo, check=True, stdout=subprocess.PIPE).stdout),
                      "published_scheduling_only_change": path == SCHEDULING_PATH and
                        content != subprocess.run(["git", "show", BASE+":"+path],
                        cwd=repo, check=True, stdout=subprocess.PIPE).stdout})
    public = [r for r in records if r["visibility"] == "public"]
    if len({r["name"] for r in public}) != len(public): raise ValueError("duplicate public theorem")
    return {"base":BASE, "module_map":MAP, "module_map_sha256":digest(map_bytes),
            "boundary":"Source signatures only; no satisfiability or kernel census claim.",
            "modules":files, "theorems":records,
            "summary":{"modules":len(files), "named_theorems":len(records),
                       "public_theorems":len(public), "private_theorems":len(records)-len(public),
                       "proof_credit_from_source_scan":0}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--ownership", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = census(args.repo, json.loads(args.ownership.read_text()))
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps(report["summary"],sort_keys=True))
    print("census_sha256="+digest(args.output.read_bytes()))

if __name__ == "__main__": main()
