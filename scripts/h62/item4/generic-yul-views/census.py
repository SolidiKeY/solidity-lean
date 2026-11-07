#!/usr/bin/env python3
"""Deterministic lexical inventory; not a Lean parser or a semantic proof.

Inventory every declaration/guard in every Views module, including non-Controls
files. Preserve exact UTF-8 source and statement hashes; do not normalize text.
The statement prefix ends at the first un-nested := or where. For guards the
entire command is retained. Output belongs off git (H44).
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re

KINDS = r"theorem|lemma|example|def|abbrev|opaque|axiom|constant|structure|inductive|instance|class"
DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|local|scoped)[ \t]+)*(?P<kind>" + KINDS + r"|#guard_msgs|#guard)(?=\s|$)")
COMMAND = re.compile(r"(?m)^[ \t]*(?:(?:namespace|end|section|open|variable|universe|set_option|attribute|export|import|initialize|syntax|macro|elab|notation|infix|prefix|postfix)\b|#(?:print|check|eval|reduce|exit)\b)")

def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()

def mask(text, strings=True, comments=None):
    # Keep offsets/newlines intact while removing nested comments and strings.
    out = list(text)
    i, depth, string, quoted = 0, 0, False, False
    comment_start = 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == "/-": depth += 1; n = 2
            elif pair == "-/":
                depth -= 1; n = 2
                if depth == 0 and comments is not None: comments.append((comment_start, i+2))
            else: n = 1
        elif string:
            n = 2 if text[i] == "\\" and i + 1 < len(text) else 1
            if text[i] == '"': string = False
        elif quoted:
            if text[i] == "»": quoted = False
            if strings: out[i] = "_"
            i += 1
            continue
        elif pair == "/-": depth = 1; comment_start = i; n = 2
        elif pair == "--":
            j = text.find("\n", i)
            n = (len(text) if j < 0 else j) - i
        elif text[i] == '"':
            if not strings:
                # Preserve literal text but skip its contents lexically.
                i += 1
                while i < len(text):
                    if text[i] == "\\": i += 2; continue
                    if text[i] == '"': i += 1; break
                    i += 1
                continue
            string = True; n = 1
        elif text[i] == "«":
            quoted = True
            if strings: out[i] = "_"
            i += 1; continue
        else: i += 1; continue
        for j in range(i, min(i+n, len(text))):
            if out[j] != "\n": out[j] = " "
        i += n
    if depth or string or quoted:
        raise ValueError("unterminated comment/string/quoted identifier")
    return "".join(out)

def statement_end(masked):
    depth = 0
    i = 0
    while i < len(masked):
        c = masked[i]
        if c in "([{⟨": depth += 1
        elif c in ")]}⟩": depth -= 1
        if depth == 0:
            if masked[i:i+2] == ":=": return i
            if masked[i:i+5] == "where" and (i == 0 or masked[i-1].isspace()) and (i+5 == len(masked) or masked[i+5].isspace()): return i
        i += 1
    return len(masked)

def scan(root):
    files, declarations = [], []
    views = root / "Solidity/Yul/Views"
    paths = sorted(views.rglob("*.lean"))
    if not views.is_dir() or not paths:
        raise ValueError("missing or empty Solidity/Yul/Views directory")
    for p in paths:
        text = p.read_bytes().decode("utf-8")
        comments = []
        masked = mask(text, comments=comments)
        comments_only = mask(text, strings=False)
        matches = list(DECL.finditer(masked))
        boundaries = sorted({m.start() for m in matches} | {m.start() for m in COMMAND.finditer(masked)} | {len(text)})
        path = p.relative_to(root).as_posix()
        files.append(dict(path=path, sha256=sha(text), bytes=len(text.encode("utf-8")), declarations=len(matches)))
        for m in matches:
            end = next(b for b in boundaries if b > m.start())
            # A multiline guard wraps the next command, including #eval or
            # a theorem on its own line. Also inventory that declaration.
            line_end = masked.find("\n", m.end())
            if m["kind"] == "#guard_msgs" and line_end >= 0:
                suffix = masked[m.end():line_end].strip()
                if suffix.endswith("in") and not masked[line_end:end].strip() and end < len(text):
                    end = next(b for b in boundaries if b > end)
            # Exclude trailing documentation owned by the following command.
            end = m.start() + len(comments_only[m.start():end].rstrip())
            block = text[m.start():end]
            kind = m["kind"]
            name_match = re.match(r"\s+([^\s({:]+)", text[m.end():end])
            name = name_match[1] if name_match and kind not in ("example", "#guard", "#guard_msgs") else None
            if kind == "instance" and name in (None, "where"):
                name = None
            cut = len(block) if kind.startswith("#") else statement_end(masked[m.start():end])
            expected = None
            if kind == "#guard_msgs":
                for a, b in reversed(comments):
                    if b <= m.start():
                        if not text[b:m.start()].strip() and text[a:a+3] == "/--":
                            expected = text[a:b]
                        break
            declarations.append(dict(path=path, line=text.count("\n", 0, m.start())+1,
                kind=kind, name=name, in_controls_file="Controls" in p.stem,
                disposition="current lexical declaration; frozen-source preservation not checked",
                expected_message_comment=expected,
                expected_message_sha256=sha(expected) if expected is not None else None,
                statement=block[:cut], statement_sha256=sha(block[:cut]), command_sha256=sha(block)))
    return dict(schema=1, boundary="lexical source inventory, not elaborated statement equivalence",
        files=files, declarations=declarations,
        summary=dict(files=len(files), declarations=len(declarations),
            controls_files=sum("Controls" in Path(f["path"]).stem for f in files),
            kinds=dict(sorted(collections.Counter(d["kind"] for d in declarations).items())),
            controls_kinds=dict(sorted(collections.Counter(d["kind"] for d in declarations if d["in_controls_file"]).items()))),
        audit_mapping={
            "9": dict(status="method_applicable", scope="Views twin/per-case controls; listed Backend/Evm targets remain outside this lane"),
            "11": dict(status="method_applicable", scope="Views typed fixtures and shared semantic helpers; listed Evm/Backend helpers remain outside this lane"),
            "16": dict(status="method_applicable", scope="Views typed table plus universal lemma; Yul Raw and vector generation remain H55, not duplicated")})

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--verify", type=Path, help="fail if fresh inventory differs from saved inventory")
    args = ap.parse_args()
    result = scan(args.root.resolve())
    data = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if args.verify and args.verify.read_bytes() != data.encode("utf-8"):
        raise SystemExit("CENSUS_MISMATCH")
    args.output.write_bytes(data.encode("utf-8"))
    print(json.dumps(result["summary"], sort_keys=True))
    print("CENSUS_SHA256=" + sha(data))

if __name__ == "__main__": main()
