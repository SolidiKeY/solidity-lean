#!/usr/bin/env python3
"""Conservative source census. This is NOT an elaborated theorem/witness check.

Read only frozen Git objects; include every named theorem/lemma, even controls
and private declarations, rather than silently guessing which are interfaces.
Bulk JSON goes outside Git. Exact source slices and file hashes are authoritative;
qualified names and binder classifications remain pending Lean verification.
"""
import argparse
import hashlib
import fnmatch
import json
import re
import subprocess
from pathlib import Path

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
AREAS = ("language", "source-definitions")

def git(*args):
    return subprocess.check_output(["git", *args])

def sha(data):
    return hashlib.sha256(data).hexdigest()

def mask(text):
    """Blank nested comments and string contents, preserving offsets/newlines."""
    out = list(text)
    i = 0
    def blank(a, b):
        for j in range(a, b):
            if text[j] != "\n": out[j] = " "
    while i < len(text):
        start = i
        if text.startswith("--", i):
            e = text.find("\n", i)
            i = len(text) if e < 0 else e
        elif text.startswith("/-", i):
            i += 2
            depth = 1
            while i < len(text) and depth:
                if text.startswith("/-", i): depth += 1; i += 2
                elif text.startswith("-/", i): depth -= 1; i += 2
                else: i += 1
            if depth: raise ValueError("unterminated comment")
        elif text[i] == '"' or (text[i] == "r" and re.match(r'r#+"', text[i:])):
            raw = re.match(r'r(#+)"', text[i:])
            if raw:
                terminal = '"' + raw[1]
                e = text.find(terminal, i + len(raw[0]))
                if e < 0: raise ValueError("unterminated raw string")
                i = e + len(terminal)
            else:
                i += 1
                while i < len(text):
                    if text[i] == "\\": i += 2
                    elif text[i] == '"': i += 1; break
                    else: i += 1
        elif text[i] == "'" and (i == 0 or not (text[i-1].isalnum() or text[i-1] in "_'")):
            char = re.match(r"'(?:\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\.|[^'\\\n])'", text[i:])
            if char: i += len(char[0])
            else: i += 1; continue
        else:
            i += 1
            continue
        blank(start, i)
    return "".join(out)

def proof_start(clean, start):
    depth = 0
    # Equation-style proofs and structures' `where` are proof boundaries too.
    for m in re.finditer(r":=|(?m:^[ \t]*\|)|\bwhere\b|[(){}\[\]⦃⦄]", clean[start:]):
        token = m[0]
        if depth == 0 and (token == ":=" or token == "where" or token.lstrip().startswith("|")):
            return start + m.start()
        if token in ("(", "{", "[", "⦃"): depth += 1
        elif token in (")", "}", "]", "⦄"): depth -= 1
    raise ValueError("no top-level proof delimiter before next command")

def scan(path, data, areas):
    text = data.decode()
    clean = mask(text)
    pattern = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*(namespace|section|mutual|end|variable|theorem|lemma)\b([^\n]*)")
    stack = []
    variables = []
    records = []
    consumed = 0
    events = list(pattern.finditer(clean))
    for index, m in enumerate(events):
        if m.start() < consumed: continue
        kind, tail = m[1], m[2].strip()
        if kind in ("namespace", "section", "mutual"):
            stack.append((kind, tail.split()[0] if tail else "", len(variables)))
        elif kind == "end":
            if stack:
                _, _, n = stack.pop(); variables = variables[:n]
        elif kind == "variable":
            # Preserve complete command through next non-indented source command.
            e = re.search(r"(?m)^\S", clean[m.end():])
            end = m.end() + e.start() if e else len(clean)
            variables.append(text[m.start():end].rstrip())
        else:
            name = re.match(r"[^\s({:\[]+", tail)
            if not name: raise ValueError(f"unnamed declaration: {path}:{m.start()}")
            limit = events[index + 1].start() if index + 1 < len(events) else len(clean)
            end = proof_start(clean[:limit], m.end(1))
            consumed = end + 2
            signature = text[m.start():end].strip()
            namespaces = [s[1] for s in stack if s[0] == "namespace"]
            candidate = name[0][7:] if name[0].startswith("_root_.") else ".".join(namespaces + [name[0]])
            records.append({
                "id": f"{path}:{text.count(chr(10), 0, m.start(1)) + 1}:{name[0]}",
                "path": path, "areas": sorted(areas),
                "line": text.count(chr(10), 0, m.start(1)) + 1,
                "name_candidate": candidate, "name_status": "pending-elaboration",
                "source_signature": signature, "signature_sha256": sha(signature.encode()),
                "section_variables": list(variables),
                "context_status": "pending-elaboration-includes-omit-open-universe-directives",
                "source_prefix_end": m.start(),
                "source_prefix_sha256": sha(text[:m.start()].encode()),
                "owner": "area producer (coordinator exact-file resolution pending)",
                "hypothesis_classification": "pending-elaboration",
                "simultaneous_witness": None, "status": "uncovered",
            })
    return records

def ownership_claims(paths):
    snapshot = Path("/workspace/h62-coordinator-inputs/ownership.json").read_bytes()
    if sha(snapshot) != "7f5d40d46d386ed17731db55ed87f0564f5c9e667bddee00c0f12b28772f9cce":
        raise ValueError("ownership snapshot differs from coordinator checksum")
    items = json.loads(snapshot)["items"]
    claims = {}
    for path in paths:
        candidates = []
        for item in items:
            patterns = re.findall(r'(?:Solidity|Bridge)/[^\s;,\]"\)]+', str(item.get("writeScope", "")))
            exclusions = re.findall(r'(?:Solidity|Bridge)/[^\s;,\]"\)]+', str(item.get("writeExclusions", "")))
            matched = [pattern for pattern in patterns if fnmatch.fnmatchcase(path, pattern)]
            if matched and not any(fnmatch.fnmatchcase(path, pattern) for pattern in exclusions):
                mode = item.get("writeMode", "live-producer-scope-candidate")
                candidates.append({"id": item["id"], "owner": item.get("owner"),
                                   "mode": mode, "matched_scope": matched})
        claims[path] = candidates
    return claims

def generate():
    files = set(git("ls-tree", "-r", "--name-only", BASE).decode().splitlines())
    modules = {}
    references = []
    maps = {}
    unresolved = []
    for area in AREAS:
        path = f"docs/module-map/{area}.md"
        data = git("show", f"{BASE}:{path}")
        maps[path] = sha(data)
        for line_no, line in enumerate(data.decode().splitlines(), 1):
            if not line.startswith("| "): continue
            for ref in re.findall(r"`([^`]+\.lean)`", line.split("|")[1]):
                candidates = [ref, "Solidity/" + ref]
                hits = [p for p in candidates if p in files]
                if len(hits) != 1:
                    unresolved.append({"map": path, "line": line_no, "reference": ref, "hits": hits})
                    continue
                p = hits[0]
                modules.setdefault(p, set()).add(area)
                references.append({"map": path, "line": line_no, "reference": ref, "path": p})
    declarations = []
    sources = {}
    errors = []
    for path, areas in sorted(modules.items()):
        data = git("show", f"{BASE}:{path}")
        sources[path] = {"sha256": sha(data), "areas": sorted(areas)}
        try: declarations.extend(scan(path, data, areas))
        except ValueError as e: errors.append({"path": path, "error": str(e)})
    claims = ownership_claims(sources)
    for path in sources:
        sources[path]["ownership_claims"] = claims[path]
    for record in declarations:
        record["ownership_claims"] = claims[record["path"]]
        live = [c for c in claims[record["path"]] if "migration" not in c["mode"] and not c["id"].startswith("H62-2-")]
        record["owner"] = live[0]["owner"] if len(live) == 1 else "area producer (coordinator exact-file resolution pending)"
        record["owner_status"] = "scope-candidate-needs-owner-confirmation" if len(live) == 1 else "unresolved-or-conflicting"
    ids = [r["id"] for r in declarations]
    if len(ids) != len(set(ids)): raise ValueError("duplicate declaration IDs")
    return {"base": BASE, "method": "conservative-source-census-not-Lean-certified",
            "maps": maps, "references": references, "unresolved_references": unresolved,
            "sources": sources, "scan_errors": errors, "declarations": declarations,
            "summary": {"files": len(sources), "declarations": len(declarations),
                        "uncovered": len(declarations), "certified_witnesses": 0,
                        "unresolved_references": len(unresolved), "scan_errors": len(errors)}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = generate()
    payload = (json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode()
    (args.output / "census.json").write_bytes(payload)
    (args.output / "census.sha256").write_text(sha(payload) + "  census.json\n")
    print(json.dumps(report["summary"], sort_keys=True))
    return int(bool(report["scan_errors"] or report["unresolved_references"]))

if __name__ == "__main__":
    raise SystemExit(main())
