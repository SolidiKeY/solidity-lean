#!/usr/bin/env python3
"""Frozen StructuredFlow source census; no Lean parser or semantic-proof claim.

Full source/statement records are regenerated off git (H44). Positions index
Unicode source characters, not UTF-8 bytes. Exact UTF-8 SHA256s are authoritative.
"""
import argparse
import collections
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FAMILY = "Solidity/Backend/StructuredFlow/"
DEST = ROOT / "tests/h62/item4/generic-structuredflow/frozen.json"
START = re.compile(r"(?m)^(?:(?:private|protected|noncomputable|unsafe) +)*(theorem|lemma|def|abbrev|structure|inductive|instance) +([^\s(:{]+)|^(#guard_msgs|#eval|#check|#print)\b|^(namespace|section|end)\b[^\n]*")


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"


def mask(text):
    """Mask nested comments and strings without moving any source position."""
    out = list(text)
    i = 0
    depth = 0
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
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i:i+2] = "  "
                i += 2
            else:
                if text[i] == '\"':
                    string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end-i)
            i = end
        elif text.startswith("/-", i):
            depth = 1
            out[i:i+2] = "  "
            i += 2
        elif text[i] == '\"':
            string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("Unclosed comment/string")
    return "".join(out)


def records(path, text):
    hidden = mask(text)
    starts = list(START.finditer(hidden))
    namespace = []
    result = []
    for n, item in enumerate(starts):
        kind, name, command, scope = item.groups()
        end = starts[n+1].start() if n+1 < len(starts) else len(text)
        if scope:
            label = item.group().split()
            if scope in ("namespace", "section"):
                namespace.append(label[1] if scope == "namespace" and len(label) > 1 else "")
            elif namespace:
                namespace.pop()
            continue
        begin = item.start()
        body_at = end
        depth = 0
        pending_lets = 0
        for i in range(item.end(), end):
            char = hidden[i]
            if char in "({[⟨":
                depth += 1
            elif char in ")}]⟩":
                depth -= 1
            if depth == 0:
                # A type-level `let x := ...; conclusion` is part of a
                # theorem statement. Its assignment is not the proof boundary.
                if re.match(r"let\b", hidden[i:i+4]) and (i == 0 or not hidden[i-1].isalnum()):
                    pending_lets += 1
                if hidden.startswith(":=", i):
                    if pending_lets:
                        pending_lets -= 1
                    else:
                        body_at = i
                        break
                elif re.match(r"where\b", hidden[i:i+6]) or (char == "|" and not hidden[text.rfind("\n", 0, i)+1:i].strip()):
                    body_at = i
                    break
        # Trailing whitespace/comments belong to no statement; exact original
        # file hash separately authenticates every byte including documentation.
        statement = text[begin:body_at].rstrip()
        full = text[begin:end].rstrip()
        line = text.count("\n", 0, begin) + 1
        qualified = ".".join(x for x in namespace + [name] if x) if name else f"{command}@{line}"
        result.append(dict(path=path, line=line, kind=kind or command,
                           name=qualified, statement=statement,
                           statement_sha256=sha(statement), source_sha256=sha(full),
                           negative_hint=bool(re.search(r"refus|wrong|not_|omitt|fault|revert|bad|failure", name or ""))))
    # Fail closed on an unhandled top-level declaration form rather than
    # silently losing one. This grammar covers the frozen family, not all Lean.
    allowed = {m.start() for m in starts}
    for m in re.finditer(r"(?m)^(?:theorem|lemma|def|abbrev|structure|inductive|instance|axiom|opaque|constant)\b", hidden):
        if m.start() not in allowed:
            raise ValueError(f"Unhandled declaration at {path}:{text.count(chr(10), 0, m.start())+1}")
    return result


def census(revision=None):
    if revision:
        names = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", revision, FAMILY], cwd=ROOT, text=True).splitlines()
        read = lambda name: subprocess.check_output(["git", "show", f"{revision}:{name}"], cwd=ROOT).decode()
    else:
        names = [p.relative_to(ROOT).as_posix() for p in (ROOT/FAMILY).rglob("*.lean")]
        read = lambda name: (ROOT/name).read_bytes().decode("utf-8")
    files, declarations = [], []
    for name in sorted(n for n in names if n.endswith(".lean")):
        text = read(name)
        rows = records(name, text)
        controls = name.endswith("Controls.lean")
        files.append(dict(path=name, sha256=sha(text), declarations=len(rows), controls=controls,
                          audit_items=[9,16] if controls else [9]))
        declarations.extend(rows)
    return dict(schema=1, base=BASE, files=files, declarations=declarations,
                audit_applicability={"9": "Loop twin and StructuredFlow controls census; Source conclusions remain distinct.",
                                     "11": "No named cons-revert, pushes_zero, allocationCostProg, sourceReverted, HRef split, Loc.data, HeapRepr/AllocatorRepr fixture copies in this family.",
                                     "16": "Typed observation fixtures only; no Yul Raw/vector generator duplicated (H55)."},
                counts=dict(collections.Counter(r["kind"] for r in declarations)),
                controls_counts=dict(collections.Counter(r["kind"] for r in declarations if r["path"].endswith("Controls.lean"))))


def seal(data):
    return dict(schema=1, base=BASE, census_sha256=sha(canonical(data)), files=data["files"],
                counts=data["counts"], controls_counts=data["controls_counts"], audit_applicability=data["audit_applicability"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="Off-git full inventory destination")
    parser.add_argument("--freeze", action="store_true", help="Initialize the scoped immutable seal; refuses overwrite")
    args = parser.parse_args()
    frozen = census(BASE)
    current = census()
    expected = seal(frozen)
    if args.freeze:
        with DEST.open("x") as f:
            f.write(json.dumps(expected, indent=2, sort_keys=True) + "\n")
    else:
        if json.loads(DEST.read_text()) != expected:
            raise SystemExit("FAIL: pinned census seal drift")
    if current != frozen:
        raise SystemExit("FAIL: original files, declaration inventory, or exact statements/proofs changed")
    args.output.write_text(json.dumps(frozen, indent=2, sort_keys=True) + "\n")
    print(canonical(dict(status="PASS", census_sha256=expected["census_sha256"], files=len(frozen["files"]),
                         counts=frozen["counts"], controls_counts=frozen["controls_counts"])), end="")


if __name__ == "__main__":
    main()
