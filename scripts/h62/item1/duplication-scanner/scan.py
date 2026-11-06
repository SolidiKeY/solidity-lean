#!/usr/bin/env python3
"""Conservative lexical duplicate discovery. Results are leads, not Lean proofs."""
import argparse
import fnmatch
import hashlib
import json
import re
from pathlib import Path

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)?(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+|local[ \t]+)*(theorem|lemma|def|abbrev|opaque|example|instance|structure|inductive|class|axiom|constant)(?=[\s(:{\[])(?:[ \t]+([^\s(:{\[]+))?")
TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|[\w\']+(?:\.[\w\']+)*|[^\s]')
BINDER = re.compile(r"([({\[])\s*((?:[^\W\d]|_)[\w']*(?:\s+(?:[^\W\d]|_)[\w']*)*)\s*:\s*([^(){}\[\]]*)([)}\]])\s*")

def mask(text):
    out = list(text)
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out[i:i+2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out[i:i+2] = "  "
                i += 2
            else:
                if text[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\": i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif text[i] == '"':
            string = True
            i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i+2] = "  "
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0: j = len(text)
            out[i:j] = " " * (j-i)
            i = j
        else: i += 1
    if depth or string: raise ValueError("unterminated comment or string")
    return "".join(out)

def hide_strings(text):
    out = list(text)
    i = 0
    inside = False
    while i < len(text):
        c = text[i]
        if inside:
            if c == "\\" and i+1 < len(text):
                out[i] = " "
                if text[i+1] != "\n": out[i+1] = " "
                i += 2
                continue
            if c == '"': inside = False
            if c != "\n": out[i] = " "
        elif c == '"':
            inside = True
            out[i] = " "
        i += 1
    return "".join(out)

def tokenize(s):
    return TOKEN.findall(s)

def normalize(header):
    # Types are read before introducing the names bound by their group.
    if "«" in header or "»" in header: return None
    env = {}
    out = []
    pos = 0
    while True:
        match = BINDER.match(header, pos)
        if not match: break
        opening, closing = match.group(1), match.group(4)
        if {"(": ")", "{": "}", "[": "]"}[opening] != closing: return None
        ns = match.group(2).split()
        if "_" in ns or len(set(ns)) != len(ns) or any(n in env for n in ns): return None
        type_text = match.group(3)
        if any(c in type_text for c in "λ∀") or re.search(r"\b(fun|let|forall|match)\b", type_text): return None
        typ = tokenize(type_text)
        if any("." in t and any(n in t.split(".") for n in env) for t in typ): return None
        if any(typ[i] == "." and i + 1 < len(typ) and typ[i+1] in env for i in range(len(typ))): return None
        out.extend([opening] + ["$binder" + str(len(env)+i) for i in range(len(ns))] + [":"])
        out.extend(env.get(t, t) for t in typ)
        out.append(closing)
        for n in ns: env[n] = "$binder" + str(len(env))
        pos = match.end()
    rest = header[pos:]
    if any(c in rest for c in "{}[]λ∀") or re.search(r"\b(fun|let|forall)\b", header): return None
    if re.search(r"\([^()]*:", rest): return None
    ts = tokenize(rest)
    if any("." in t and any(n in t.split(".") for n in env) for t in ts): return None
    if any(ts[i] == "." and i + 1 < len(ts) and ts[i+1] in env for i in range(len(ts))): return None
    out.extend(env.get(t, t) for t in ts)
    return out

def split_definition(content):
    """Find a top-level :=, ignoring strings and bracketed default values."""
    depth = 0
    string = False
    i = 0
    while i < len(content):
        c = content[i]
        if string:
            if c == "\\": i += 2; continue
            if c == '"': string = False
        elif c == '"': string = True
        elif c in "([{": depth += 1
        elif c in ")]}":
            depth -= 1
            if depth < 0: return None
        elif depth == 0 and content.startswith(":=", i):
            return content[:i], content[i+2:]
        i += 1
    return None

def scan(path, root):
    text = mask(path.read_text(encoding="utf-8"))
    skeleton = hide_strings(text)
    matches = list(DECL.finditer(skeleton))
    context_commands = list(re.finditer(r"(?m)^[ \t]*(?:import|namespace|section|end|open|variable|universe)\b[^\n]*", skeleton))
    rows = []
    for i, match in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else len(text)
        content = text[match.end():end]
        context = digest([m.group().strip() for m in context_commands if m.start() < match.start()])
        unsupported = match.group(1) in {"structure", "inductive", "class", "axiom", "constant"}
        parts = None if unsupported else split_definition(content)
        if parts is None:
            rows.append(dict(path=path.relative_to(root).as_posix(),
                             line=text.count("\n", 0, match.start())+1,
                             kind=match.group(1), name=match.group(2) or "<anonymous>",
                             statement=None, body=[], owner="unknown", context_hash=context,
                             reject_reason="unsupported-declaration-form" if unsupported else "missing-top-level-definition"))
            continue
        header, body = parts
        boundary = re.search(r"(?m)^[ \t]*(?:end|namespace|section|open|variable|attribute|#\w+)\b", hide_strings(body))
        if boundary: body = body[:boundary.start()]
        rows.append(dict(path=path.relative_to(root).as_posix(),
                         line=text.count("\n", 0, match.start())+1,
                         kind=match.group(1), name=match.group(2) or "<anonymous>",
                         statement=normalize(header.strip()), body=tokenize(body),
                         owner="unknown", context_hash=context,
                         reject_reason="unsupported-binder-syntax" if normalize(header.strip()) is None else None))
    return rows

def digest(obj):
    return hashlib.sha256(json.dumps(obj, ensure_ascii=False, separators=(",", ":")).encode()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--owners", type=Path, help="JSON mapping exact relative paths to owner labels")
    parser.add_argument("--previous", type=Path, help="previous scanner JSON report")
    parser.add_argument("--registry", type=Path, help="coordinator ownership snapshot; references are advisory")
    args = parser.parse_args()
    root = args.root.resolve()
    matched = {pat: sorted(f.resolve() for f in root.glob(pat) if f.is_file() and f.suffix == ".lean") for pat in args.paths}
    unmatched = sorted(pat for pat, paths in matched.items() if not paths)
    files = sorted({f for paths in matched.values() for f in paths})
    rows, errors, inputs = [], [], []
    owners = json.loads(args.owners.read_text()) if args.owners else {}
    if not isinstance(owners, dict) or not all(isinstance(k, str) and isinstance(v, str) and v for k, v in owners.items()):
        parser.error("owners must be a path-to-owner JSON object")
    registry_bytes = args.registry.read_bytes() if args.registry else b""
    registry = json.loads(registry_bytes) if registry_bytes else {}
    refs = set()
    def strings(value):
        if isinstance(value, str): yield value
        elif isinstance(value, dict):
            for child in value.values(): yield from strings(child)
        elif isinstance(value, list):
            for child in value: yield from strings(child)
    for item in registry.get("items", []):
        if not isinstance(item, dict): parser.error("invalid registry item")
        for value in strings(item):
            for pattern in re.findall(r"(?:Solidity|tests|scripts)/[A-Za-z0-9_./*?\[\]-]*", value):
                pattern = pattern.rstrip(".,;:)")
                refs.add((pattern, str(item.get("id", "")), str(item.get("owner", "")), str(item.get("status", ""))))
    for path in files:
        try:
            rel = path.relative_to(root).as_posix()
            inputs.append(dict(path=rel, sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
            found = scan(path, root)
            references = [dict(pattern=p, id=i, owner=o, status=st) for p, i, o, st in sorted(refs)
                if (rel.startswith(p) if p.endswith("/") else fnmatch.fnmatchcase(rel, p))]
            for row in found:
                row["owner"] = owners.get(rel, "unknown")
                row["registry_references"] = references
            rows.extend(found)
        except (ValueError, UnicodeError) as exc:
            errors.append(dict(path=str(path), reason=str(exc)))
    groups = {}
    for row in rows:
        if row["statement"] is not None:
            groups.setdefault(digest([row["kind"], row["statement"], row["context_hash"]]), []).append(row)
    candidates = []
    for key, group in sorted(groups.items()):
        if len(group) > 1:
            candidates.append(dict(lexical_key=key, reject_reasons=["intrinsic-signature-unresolved", "ownership-requires-live-verification"],
                members=[{k:v for k,v in row.items() if k not in ("statement", "body")} for row in group],
                body_hashes=sorted({digest(row["body"]) for row in group}),
                action="weak-lexical-lead-review-signatures-and-ownership"))
    bodies = {}
    for row in rows:
        if row["body"]:
            bodies.setdefault(digest(row["body"]), []).append(row)
    body_candidates = []
    for key, group in sorted(bodies.items()):
        if len(group) > 1:
            body_candidates.append(dict(body_hash=key,
                members=[{k:v for k,v in row.items() if k not in ("statement", "body")} for row in group],
                reject_reasons=sorted({"intrinsic-signature-unresolved", "ownership-requires-live-verification"} |
                    ({"different-or-unsupported-statements"}
                    if len({digest([row["statement"], row["context_hash"]]) for row in group}) > 1 or
                       any(row["statement"] is None for row in group) else set())),
                action="weak-lexical-lead-review-signatures-and-ownership"))
    previous = json.loads(args.previous.read_text()) if args.previous else None
    if previous is not None and (not isinstance(previous, dict) or previous.get("version") != 1 or not isinstance(previous.get("inputs"), list)):
        parser.error("unsupported or malformed previous report")
    old = {x["path"]: x["sha256"] for x in previous["inputs"]} if previous else {}
    new = {x["path"]: x["sha256"] for x in inputs}
    scanner_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    incremental = dict(added=sorted(new.keys()-old.keys()), removed=sorted(old.keys()-new.keys()),
        changed=sorted(k for k in old.keys() & new.keys() if old[k] != new[k]),
        owner_config_changed=previous is not None and previous.get("owner_config_sha256") != digest(owners),
        registry_changed=previous is not None and previous.get("registry_sha256") != hashlib.sha256(registry_bytes).hexdigest(),
        scanner_changed=previous is not None and previous.get("scanner_sha256") != scanner_sha256)
    rejected = [{k:r[k] for k in ("path", "line", "name", "reject_reason")} for r in rows if r["reject_reason"]]
    inventory = [{k:v for k,v in row.items() if k not in ("statement", "body")} for row in rows]
    print(json.dumps(dict(version=1, inputs=inputs, declarations=len(rows), inventory=inventory, candidates=candidates, rejected_declarations=rejected,
        body_candidates=body_candidates, incremental=incremental, unmatched_patterns=unmatched,
        owner_config_sha256=digest(owners), registry_sha256=hashlib.sha256(registry_bytes).hexdigest(), scanner_sha256=scanner_sha256,
        rejections=dict(unsupported_binder_syntax=sum(r["statement"] is None for r in rows),
                        unknown_ownership=sum(r["owner"] == "unknown" for r in rows)), errors=errors),
        sort_keys=True, ensure_ascii=False, indent=2))
    return bool(errors or unmatched)

if __name__ == "__main__":
    raise SystemExit(main())
