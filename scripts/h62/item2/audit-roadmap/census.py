#!/usr/bin/env python3
"""Source-level frozen census; never equates extraction with Lean verification.

Outputs are off git (H44). Every theorem is retained, including declarations
without explicit Prop binders, private declarations, and negative controls.
Section variables are recorded as context, not claimed to be used binders.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def sha(data):
    return hashlib.sha256(data).hexdigest()

def mask(src):
    """Preserve offsets/newlines while erasing nested comments and strings."""
    out = list(src)
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(src):
        pair = src[i:i+2]
        if line:
            if src[i] == "\n":
                line = False
            else:
                out[i] = " "
            i += 1
        elif depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                out[i:i+2] = "  "
                i += 2
            else:
                if src[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if src[i] == "\\":
                out[i:i+2] = "  "
                i += 2
            else:
                string = src[i] != '"'
                if src[i] != "\n":
                    out[i] = " "
                i += 1
        elif pair == "--":
            out[i:i+2] = "  "
            line = True
            i += 2
        elif pair == "/-":
            out[i:i+2] = "  "
            depth = 1
            i += 2
        elif src[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("unterminated comment/string")
    return "".join(out)

EVENT = re.compile(r"^[ \t]*(?:@\[[^\n]*\][ \t]*)*(?:deriving[ \t]+)?(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*(namespace|section|mutual|end|variable|theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\b([^\n]*)", re.M)

def signature_end(clean, start):
    depth = 0
    pending_lets = 0
    i = start
    while i < len(clean):
        ch = clean[i]
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        if depth == 0 and re.match(r"(?<![\w.])let\b", clean[i:]) and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] in "_.")):
            pending_lets += 1
        if depth == 0 and clean[i:i+2] == ":=" and pending_lets:
            pending_lets -= 1
            i += 2
            continue
        if depth == 0 and (clean[i:i+2] == ":=" or
                           re.match(r"where\b", clean[i:]) or
                           (ch == "|" and not clean[clean.rfind("\n",0,i)+1:i].strip())):
            return i
        i += 1
    raise ValueError("no theorem proof delimiter")

def scan(src, path, area, owner):
    clean = mask(src)
    stack = []
    variables = []
    rows = []
    candidates = []
    events = list(EVENT.finditer(clean))
    for k, m in enumerate(events):
        kind, tail = m.groups()
        word = tail.strip().split()
        if kind in ("namespace", "section", "mutual"):
            stack.append((kind, word[0] if word else "", len(variables)))
        elif kind == "end":
            if not stack:
                raise ValueError(f"unmatched end: {path}:{clean[:m.start()].count(chr(10))+1}")
            _, _, n = stack.pop()
            del variables[n:]
        elif kind == "variable":
            stop = events[k+1].start() if k+1 < len(events) else len(src)
            # Context text ends at the next command, not at the next theorem alone.
            next_command = re.search(r"^\S", clean[m.end()+1:stop], re.M)
            if next_command:
                stop = m.end()+1+next_command.start()
            variables.append(src[m.start():stop].strip())
        else:
            name = word[0]
            ns = ".".join(n for t,n,_ in stack if t == "namespace")
            fq = name[len("_root_."):] if name.startswith("_root_.") else ".".join(filter(None,[ns,name]))
            if kind not in ("theorem", "lemma"):
                candidates.append(dict(source_qualified_name=None if kind == "instance" and (name[0] in ":({[" or "deriving" in clean[m.start():m.start(1)].split()) else fq,
                    source_id=f"{path}:{src[:m.start()].count(chr(10))+1}", module=path,
                    line=src[:m.start()].count("\n")+1, kind=kind,
                    section_variable_context=variables.copy(),
                    source_form="deriving-instance-command" if "deriving" in clean[m.start():m.start(1)].split() else "declaration",
                    classification="pending-proof-bearing-interface-review"))
                continue
            end = signature_end(clean, m.end(1))
            sig = src[m.start():end].strip()
            visibility = "private" if "private" in clean[m.start():m.start(1)].split() else "public"
            rows.append(dict(source_qualified_name=fq, elaborated_name=None,
                visibility=visibility, source_name=name, area=area, module=path,
                line=src[:m.start()].count("\n")+1, kind=kind,
                signature=sig, signature_sha256=sha(sig.encode()),
                section_variable_context=variables.copy(), owner="unresolved",
                owner_candidate=owner, owner_evidence="module-family inference only; exact-path confirmation pending",
                witness_status="uncovered", witness=None,
                classification="pending-semantic-review",
                fidelity="source-exact; elaborated telescope pending"))
    return rows, candidates

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=pathlib.Path)
    args = ap.parse_args()
    root = pathlib.Path(__file__).resolve().parents[4]
    def frozen(path):
        return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=root)
    rows, modules, candidates = [], [], []
    for area in ("roadmap", "tools"):
        mapping = f"docs/module-map/{area}.md"
        paths = re.findall(r"^\| `([^`]+\.lean)`", frozen(mapping).decode(), re.M)
        for name in paths:
            path = name if name.startswith("Bridge/") else f"Solidity/{name}"
            data = frozen(path)
            # Explicit known producers only. No guessing from incidental imports.
            owner = ("V15 (v12-v17/v15-evm-agreement)" if name.startswith("Bridge/") else
                "V16 (v12-v17/v16-correctness-transfer)" if name.startswith(("Roadmap/V16/", "Examples/Roadmap/V16/", "Lowering/P8/")) else
                "area producer; exact owner unresolved")
            found, extra = scan(data.decode(), path, area, owner)
            candidates.extend(extra)
            modules.append(dict(path=path, area=area, sha256=sha(data), declarations=len(found), owner="unresolved", owner_candidate=owner))
            rows.extend(found)
    names = [r["source_qualified_name"] for r in rows]
    if len(set(names)) != len(names):
        raise ValueError("duplicate theorem names; resolve namespace extraction")
    result = dict(base=BASE, census_kind="source-level conservative all-theorem inventory",
        modules=modules, statements=rows, other_declaration_candidates=candidates,
        summary=dict(modules=len(modules), statements=len(rows), witnessed=0,
            uncovered=len(rows), other_declaration_candidates=len(candidates), elaborated_telescope_verified=False,
            owner_unresolved=sum(r["owner"].endswith("unresolved") for r in rows)))
    out = args.output.resolve()
    if out.is_relative_to(root):
        raise ValueError("H44: bulk output must stay outside git checkout")
    out.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(result, ensure_ascii=False, indent=2)+"\n").encode()
    (out/"census.json").write_bytes(data)
    (out/"SHA256SUMS").write_text(f"{sha(data)}  census.json\n")
    print(json.dumps(result["summary"],sort_keys=True))

if __name__ == "__main__":
    main()
