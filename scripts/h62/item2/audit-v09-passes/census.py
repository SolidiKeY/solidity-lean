#!/usr/bin/env python3
"""Frozen V09 source census. Source spans are evidence, not elaborated types.

Run from any directory: census.py --output /absolute/off-git/directory
Includes every theorem/lemma in the named map files and its explicit wildcard.
No source-based heuristic is allowed to mark hypotheses inhabited or absent.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MAP = "docs/module-map/v09-passes.md"
OWNER = "V09 (v07-v11/v09-compiler-passes)"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def masked(text):
    """Erase nested comments and strings while preserving character offsets."""
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text.startswith("/-", i):
            i += 2
            depth = 1
            while depth:
                if i >= len(text):
                    raise ValueError("unterminated comment")
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif text[i] == chr(34):
            i += 1
            while i < len(text) and text[i] != chr(34):
                i += 2 if text[i] == chr(92) else 1
            if i >= len(text):
                raise ValueError("unterminated string")
            i += 1
        else:
            i += 1
            continue
        for j in range(start, i):
            if text[j] != "\n":
                out[j] = " "
    return "".join(out)


DECL = re.compile(r"(?m)^[ \t]*(?:(private|protected) +)?(theorem|lemma) +([^\s:(\[{]+)")
COMMAND = re.compile(r"(?m)^[ \t]*(namespace|section|end)\b([^\n]*)")


def declarations(path, text):
    clean = masked(text)
    events = [(m.start(), "scope", m) for m in COMMAND.finditer(clean)]
    events += [(m.start(), "declaration", m) for m in DECL.finditer(clean)]
    scopes = []
    result = []
    for _, kind, match in sorted(events, key=lambda e: e[0]):
        if kind == "scope":
            command, arg = match.group(1), match.group(2).strip()
            if command == "end":
                if not scopes:
                    raise ValueError(f"unbalanced end in {path}")
                scope = scopes.pop()
                if arg and arg != scope[1]:
                    raise ValueError(f"scope name mismatch in {path}: {arg} / {scope}")
            else:
                scopes.append((command, arg))
            continue
        stack = []
        i = match.end()
        pending_lets = 0
        while i < len(clean):
            ch = clean[i]
            if not stack and (i == 0 or not (clean[i-1].isalnum() or clean[i-1] in "_'")) and re.match(r"let\b", clean[i:]):
                pending_lets += 1
            if not stack and clean.startswith(":=", i):
                if pending_lets:
                    pending_lets -= 1
                    i += 2
                    continue
                break
            if ch in "([{":
                stack.append(ch)
            elif ch in ")]}":
                if not stack or {")": "(", "]": "[", "}": "{"}[ch] != stack.pop():
                    raise ValueError(f"unbalanced signature in {path}")
            i += 1
        if i == len(clean):
            raise ValueError(f"missing theorem body in {path}: {match.group(3)}")
        namespace = ".".join(s[1] for s in scopes if s[0] == "namespace")
        name = match.group(3)
        signature = text[match.start():i].strip()
        result.append({
            "name": (namespace + "." + name).removeprefix("_root_."),
            "visibility": match.group(1) or "public",
            "kind": match.group(2), "path": path,
            "line": text.count("\n", 0, match.start()) + 1,
            "character_span": [match.start(), i],
            "signature": signature, "signature_sha256": sha(signature.encode()),
            "source_sha256": sha(text.encode()), "owner": OWNER,
            "owner_basis": "Assigned V09 area owner; no per-file live-writer claim.",
            "hypotheses": "pending-elaborated-classification",
            "simultaneous_witness": None, "witness_status": "uncovered",
            "source_context": "Read source prefix through character_span[0]; includes section variables and options.",
        })
    if scopes:
        raise ValueError(f"unclosed scopes in {path}")
    return result


def census(root):
    def frozen(path):
        return subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=root)
    module_map = frozen(MAP)
    named = set(re.findall(r"`(Backend/Passes/[A-Za-z0-9]+\.lean)`", module_map.decode()))
    tracked = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE, "Solidity/Backend/Passes"], cwd=root).decode().splitlines()
    paths = {"Solidity/" + name for name in named}
    paths.update(path for path in tracked if path.endswith(("Controls.lean", "Pins.lean")))
    if "Other `Backend/Passes/*Controls.lean` and `*Pins.lean`" not in module_map.decode():
        raise ValueError("frozen module-map wildcard changed; review expansion")
    records, files = [], []
    for path in sorted(paths):
        data = frozen(path)
        if (root / path).read_bytes() != data:
            raise ValueError(f"frozen interface changed: {path}")
        found = declarations(path, data.decode())
        records.extend(found)
        files.append({"path": path, "sha256": sha(data), "theorem_count": len(found),
                      "selection": "named" if path.removeprefix("Solidity/") in named else "wildcard"})
    keys = [(r["path"], r["name"]) for r in records]
    if len(set(keys)) != len(keys):
        raise ValueError("duplicate declaration identity")
    public = [r["name"] for r in records if r["visibility"] != "private"]
    if len(set(public)) != len(public):
        raise ValueError("duplicate public fully qualified name")
    return {"schema": 1, "base": BASE, "module_map_sha256": sha(module_map),
            "owner": OWNER, "files": files, "declarations": records,
            "boundary": "Syntactic source census only. Implicit variables, proof/data binders and global/per-input feasibility require Lean elaboration and review. No coverage claim.",
            "summary": {"files": len(files), "declarations": len(records), "witnesses_verified": 0,
                        "uncovered": len(records)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[4]
    result = census(root)
    args.output.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode()
    (args.output / "census.json").write_bytes(data)
    (args.output / "census.sha256").write_text(sha(data) + "  census.json\n")
    print(json.dumps(result["summary"], sort_keys=True))
    print("CENSUS_SOURCE_ONLY: no Lean witness or statement-fidelity gate claimed")


if __name__ == "__main__":
    main()
