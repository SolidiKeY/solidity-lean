#!/usr/bin/env python3
"""Conservative lexical inventory; source hashes are authoritative, not semantic tags.
No Lean invocation. Comments/strings are blanked without changing offsets.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
FAMILY = "Solidity/Backend/InternalFlow"
DECL = re.compile(r"(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|opaque|example|structure|inductive|class|instance)\b")


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def mask(text):
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("unterminated string")
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if text[j] != "\n":
                out[j] = " "
    return "".join(out)


def header_end(clean, start, end):
    # Assignment in a default binder or let expression is nested and skipped.
    stack = []
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    lets = 0
    for i in range(start, end):
        c = clean[i]
        if c in "([{⟨":
            stack.append(c)
        elif c in pairs:
            if stack and stack[-1] == pairs[c]:
                stack.pop()
        elif not stack and re.match(r"\blet(?:I)?\b", clean[i:end]) and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] == "_")):
            lets += 1
        elif not stack and clean.startswith(":=", i):
            if lets:
                lets -= 1
            else:
                return i
        elif not stack and c == "|" and (i == 0 or clean[i-1] == "\n" or clean[clean.rfind("\n", 0, i)+1:i].isspace()):
            return i
        elif not stack and re.match(r"where\b", clean[i:end]):
            return i
    return end


def inventory(path, source):
    clean = mask(source)
    matches = list(DECL.finditer(clean))
    rows = []
    for index, m in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        stop = header_end(clean, m.end(), end)
        after = clean[m.end():stop].strip()
        name = "<anonymous>" if m[1] == "example" else (after.split()[0] if after else "<anonymous>")
        header = source[m.start():stop].strip()
        rows.append({"line": source.count("\n", 0, m.start()) + 1,
                     "kind": m[1], "name": name, "header": header,
                     "header_sha256": digest(header),
                     "slice_sha256": digest(source[m.start():end]),
                     "negative_candidate": bool(re.search(r"negative|refus|wrong|bad_|insufficient|not_revert|shallow|exhaust|missing|reject|no_allocator", name, re.I))})
    # Retain guard/axiom commands too; whole-file hash covers all syntax.
    commands = [{"line": clean.count("\n", 0, m.start()) + 1, "command": m[1]}
                for m in re.finditer(r"(?m)^[ \t]*(#(?:guard_msgs|guard|print|check|eval))\b", clean)]
    audit = []
    if any(x in path for x in ("OrderedEffectfulScalar", "OrderedEffectfulStorage", "RecursiveScopeCompiler", "ScalarSourceCompiler", "EffectfulRuntime", "EffectfulStorageRuntime", "AllocatingArguments", "MutatingCaller")):
        audit.append(9)
    shared = [term for term in ("sourceReverted", "pushes_zero", "allocationCostProg", "HRef", "HeapRepr", "AllocatorRepr") if term in clean]
    if shared:
        audit.append(11)
    if path.endswith("Controls.lean"):
        audit.append(16)
    return {"path": path, "source_sha256": digest(source),
            "controls_file": path.endswith("Controls.lean"),
            "audit_candidates": audit, "audit11_search_hits": shared,
            "declarations": rows, "commands": commands}


def census(revision=None):
    if revision:
        paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", revision, FAMILY], cwd=ROOT, text=True).splitlines()
    else:
        paths = [str(p.relative_to(ROOT)) for p in (ROOT / FAMILY).rglob("*.lean")]
    files = []
    for path in sorted(p for p in paths if p.endswith(".lean")):
        source = (subprocess.check_output(["git", "show", f"{revision}:{path}"], cwd=ROOT).decode() if revision else (ROOT / path).read_bytes().decode())
        files.append(inventory(path, source))
    controls = [f for f in files if f["controls_file"]]
    return {"schema": 1, "boundary": "lexical headers; inferred types require Lean; heuristic audit/negative tags are candidates only",
            "files": files, "summary": {"files": len(files), "controls_files": len(controls),
            "declarations": sum(len(f["declarations"]) for f in files),
            "controls_declarations": sum(len(f["declarations"]) for f in controls),
            "controls_theorems": sum(d["kind"] in ("theorem", "lemma", "example") for f in controls for d in f["declarations"])}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--revision")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--compare", type=Path)
    args = ap.parse_args()
    baseline = None
    if args.compare:
        if args.output.resolve() == args.compare.resolve() or (args.output.exists() and args.output.samefile(args.compare)):
            ap.error("output must not overwrite comparison baseline")
        baseline = json.loads(args.compare.read_text())
    result = census(args.revision)
    encoded = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    args.output.write_text(encoded)
    print(json.dumps({"sha256": digest(encoded), **result["summary"]}, sort_keys=True))
    if args.compare:
        before = {f["path"]: f["source_sha256"] for f in baseline["files"]}
        after = {f["path"]: f["source_sha256"] for f in result["files"]}
        if before != after:
            raise SystemExit("FAIL: original family inventory or bytes changed")
        print("PASS: full original family inventory and bytes unchanged")


if __name__ == "__main__":
    main()
