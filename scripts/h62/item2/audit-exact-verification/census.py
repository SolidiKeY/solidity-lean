#!/usr/bin/env python3
"""Deterministic source-candidate census, NOT an elaborated statement census.

Frozen table module cells define membership. Each physical file and each source
occurrence is emitted once, preserving all area memberships. Comments/strings
are masked without shifting offsets. Full source signatures, lexical namespace
and section-variable context are retained for subsequent Lean verification.
No candidate is marked witnessed, owner-confirmed, or premise-classified here.
"""
import argparse
import glob
import hashlib
import json
import re
import subprocess
from pathlib import Path

AREAS = ("exact-verification", "corpus", "examples")
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def mask(text):
    """Mask nested Lean comments and escaped strings, preserving newlines."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\" and i+1 < len(text):
                out[i:i+2] = ["\n" if c == "\n" else " " for c in text[i:i+2]]; i += 2
            elif text[i] == '"':
                out[i] = " "; string = False; i += 1
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0: end = len(text)
            out[i:end] = " " * (end-i); i = end
        elif text.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif text[i] == '"':
            out[i] = " "; string = True; i += 1
        else:
            i += 1
    if depth or string: raise ValueError("unterminated comment/string")
    return "".join(out)


def signature_end(clean, start):
    stack = []
    pairs = {")": "(", "]": "[", "}": "{"}
    for i in range(start, len(clean)):
        ch = clean[i]
        if ch in "([{": stack.append(ch)
        elif ch in pairs:
            if stack and stack[-1] == pairs[ch]: stack.pop()
        elif not stack and clean.startswith(":=", i): return i
        elif not stack and ch == "|" and not clean[clean.rfind("\n", 0, i)+1:i].strip(): return i
    raise ValueError("no top-level proof separator")


def declarations(path, areas, root):
    source = path.read_text()
    clean = mask(source)
    scopes = []
    result = []
    # Source command candidates; generated/quoted commands need compiler cross-check.
    pattern = re.compile(r"^[ \t]*(?:@\[[^\n]*?\][ \t]*)*(?:(?:private|protected|noncomputable) +)*(namespace|section|end|variable|theorem|lemma|example)\b([^\n]*)", re.M)
    for m in pattern.finditer(clean):
        kind, tail = m.group(1), m.group(2).strip()
        if kind in ("namespace", "section"):
            scopes.append({"kind": kind, "name": tail.split()[0] if tail else "", "variables": []})
        elif kind == "end":
            if scopes: scopes.pop()
        elif kind == "variable":
            line_end = source.find("\n", m.start())
            if line_end < 0: line_end = len(source)
            # Retain multiline variable commands up to next command/unindented line.
            while line_end < len(source) and re.match(r"[ \t]+\S", clean[line_end+1:]):
                nxt = source.find("\n", line_end+1)
                if nxt < 0: line_end = len(source); break
                line_end = nxt
            if not scopes: scopes.append({"kind": "section", "name": "", "variables": []})
            scopes[-1]["variables"].append(source[m.start():line_end])
        else:
            line = source.count("\n", 0, m.start())+1
            end = signature_end(clean, m.end(1))
            sig = source[m.start():end].rstrip()
            local_name = tail.split()[0] if kind != "example" else None
            ns = ".".join(s["name"] for s in scopes if s["kind"] == "namespace")
            candidate = (ns+"." if ns else "") + local_name if local_name else None
            if local_name and local_name.startswith("_root_."): candidate = local_name[7:]
            rel = path.relative_to(root).as_posix()
            result.append(dict(id=f"{rel}:{line}", file=rel, line=line, areas=areas,
                kind=kind, name_candidate=candidate, source_signature=sig,
                source_signature_sha256=sha(sig.encode()),
                lexical_variables=[v for s in scopes for v in s["variables"]],
                owner="UNRESOLVED_AREA_PRODUCER", premise_classification="pending_elaboration",
                hypothesis_status="pending_elaboration", witness_status="uncovered",
                statement_fidelity="source_only_unverified", private="private" in m.group(0).split(kind)[0]))
    return result


def generate(root):
    files = {}
    maps = {}
    unresolved = []
    for area in AREAS:
        map_path = root / f"docs/module-map/{area}.md"
        raw = map_path.read_bytes()
        frozen_map = subprocess.check_output(["git", "show", f"{BASE}:docs/module-map/{area}.md"], cwd=root)
        if raw != frozen_map: raise ValueError(f"frozen module-map drift: {area}")
        maps[area] = sha(raw)
        for line in raw.decode().splitlines():
            if not line.startswith("| "): continue
            cell = line.split("|")[1]
            sibling = None
            for ref in re.findall(r"`([^`]+\.lean)`", cell):
                direct = root/ref
                pattern = direct if direct.exists() else root/"Solidity"/ref
                if not pattern.exists() and "/" not in ref and sibling is not None:
                    candidate = sibling/ref
                    if candidate.is_file(): pattern = candidate
                matches = sorted(glob.glob(str(pattern)))
                if matches: sibling = Path(matches[0]).parent
                if not matches: unresolved.append(dict(area=area, reference=ref)); continue
                for item in matches:
                    path = Path(item)
                    files.setdefault(path, set()).add(area)
    records = []
    modules = []
    for path, areas in sorted(files.items()):
        rel = path.relative_to(root).as_posix()
        frozen = subprocess.check_output(["git", "show", f"{BASE}:{rel}"], cwd=root)
        if frozen != path.read_bytes(): raise ValueError(f"frozen source drift: {rel}")
        records.extend(declarations(path, sorted(areas), root))
        modules.append(dict(file=path.relative_to(root).as_posix(), areas=sorted(areas), sha256=sha(path.read_bytes())))
    assert len({r["id"] for r in records}) == len(records)
    return dict(schema=1, base=BASE, maps=maps, modules=modules, unresolved_module_rows=unresolved,
        limitations=["Source-only candidates; no compiler/export/generated-command completeness claim.",
            "Namespace resolution and implicit/section hypotheses require elaboration.",
            "All area-producer owners unresolved; ownership snapshot has no file mapping.",
            "Anonymous examples included as candidates; interface classification pending."],
        counts=dict(modules=len(modules), candidates=len(records), named=sum(r["kind"]!="example" for r in records),
                    anonymous=sum(r["kind"]=="example" for r in records), witnessed=0), declarations=records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=root, check=True)
    data = generate(root)
    args.output.write_text(json.dumps(data, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps(dict(counts=data["counts"], unresolved_module_rows=data["unresolved_module_rows"], sha256=sha(args.output.read_bytes()))))


if __name__ == "__main__": main()
