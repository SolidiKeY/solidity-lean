#!/usr/bin/env python3
"""Exact lexical type correspondence; external acceptance, not a Lean proof."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
from acceptance import BASE
import census

PAIRS = {"byte_component": "original_byte_component", "byte_component_decode": "original_byte_component_decode"}

def normalize_type(text):
    """Normalize whitespace outside strings/quoted identifiers only."""
    parts = []
    i = 0
    while i < len(text):
        if text[i].isspace():
            while i < len(text) and text[i].isspace(): i += 1
            parts.append(" ")
        elif text[i] in ('"', '«'):
            start = i
            close = '"' if text[i] == '"' else '»'
            i += 1
            while i < len(text):
                if close == '"' and text[i] == "\\": i += 2; continue
                if text[i] == close: i += 1; break
                i += 1
            else: raise ValueError("unterminated literal/identifier")
            parts.append(text[start:i])
        else:
            parts.append(text[i]); i += 1
    return "".join(parts).strip()

def theorem_types(text):
    # Raw-string parsing is outside this lexical check; fail closed.
    if re.search(r'\br#*"', text):
        raise ValueError("unsupported Lean raw string literal")
    if re.search(r"'(?:\\.|[^'\\])'", text):
        raise ValueError("unsupported Lean character literal")
    code = census.mask(text)
    preserved = census.mask(text, strings=False)
    declarations = list(census.DECL.finditer(code))
    result = {}
    for i, match in enumerate(declarations):
        if match["kind"] != "theorem": continue
        end = declarations[i+1].start() if i+1 < len(declarations) else len(text)
        tail = code[match.end():end]
        name = re.match(r"\s+([^\s({:]+)", tail)
        if not name or not re.fullmatch(r"[\w']+(?:\.[\w']+)*", name[1]):
            raise ValueError("unsupported theorem identifier")
        raw_name = preserved[match.end()+name.start(1):match.end()+name.end(1)]
        if raw_name != name[1]: raise ValueError("unsupported quoted theorem identifier")
        if name[1] in result:
            raise ValueError("ambiguous duplicate theorem identifier: " + name[1])
        prefix = tail[name.end():]
        cut = census.statement_end(prefix)
        # A delimiter-only scanner cannot locate proof assignment reliably
        # inside compound term types. Refuse known forms, never truncate them.
        if re.search(r"\b(?:letI?|haveI?|match|do|by|show|calc)\b", prefix[:cut]):
            raise ValueError("unsupported term-level syntax in lexical theorem type")
        start = match.end() + name.end()
        result[name[1]] = normalize_type(preserved[start:start+cut])
    return result

def compare(original, candidate):
    before, after = theorem_types(original), theorem_types(candidate)
    result = []
    for old, new in PAIRS.items():
        if old not in before or new not in after or before[old] != after[new]:
            raise ValueError("statement correspondence failed: " + old + " -> " + new)
        result.append(dict(original=old, candidate=new,
            normalized_type=before[old], sha256=hashlib.sha256(before[old].encode()).hexdigest()))
    return result

def frozen_blobs(root, *, base=BASE):
    """Authenticate and enumerate the existing frozen source universe."""
    try:
        subprocess.run(["git", "merge-base", "--is-ancestor", base, "HEAD"],
            cwd=root, check=True, capture_output=True)
        tree = subprocess.check_output(["git", "ls-tree", "-rz", base, "--",
            "Solidity/Yul/Views/"], cwd=root, stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as error:
        raise ValueError("cannot authenticate frozen source baseline") from error
    originals = {}
    for entry in tree.split(b"\0"):
        if not entry: continue
        metadata, path = entry.split(b"\t", 1)
        if path.endswith(b".lean"):
            originals[path.decode()] = metadata.split()[2].decode()
    if not originals:
        raise ValueError("empty frozen Views source universe")
    return originals

def source_preservation(root, current_files, *, base=BASE):
    """Bind preservation labels to full frozen Git blobs, not masked types."""
    originals = frozen_blobs(root, base=base)
    current_files = list(current_files)
    expected_paths = {info["path"] for info in current_files}
    def check_universe():
        actual_paths = {p.relative_to(root).as_posix()
            for p in (root / "Solidity/Yul/Views").rglob("*.lean")}
        if actual_paths != expected_paths:
            raise ValueError("source universe changed after census")
    check_universe()
    files = {}
    for info in current_files:
        path = info["path"]
        if path in files: raise ValueError("duplicate current source path: " + path)
        raw = (root / path).read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        if digest != info["sha256"]:
            raise ValueError("source changed after census: " + path)
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        baseline = originals.get(path)
        status = "added" if baseline is None else "unchanged" if blob == baseline else "modified"
        files[path] = dict(status=status, baseline_git_blob=baseline,
            current_git_blob=blob, source_sha256=digest)
    check_universe()
    removed = sorted(set(originals) - set(files))
    return dict(base=base, baseline_files=len(originals), current_files=len(files),
        removed_files=removed, files=files,
        boundary="Whole-file source identity only; unchanged text does not prove elaborated types or transitive dependency/meaning preservation.")

def control_rows(inventory, preservation):
    rows = []
    for declaration in inventory["declarations"]:
        if not declaration["in_controls_file"] or declaration["kind"] != "theorem": continue
        path = declaration["path"]
        if path not in preservation["files"]:
            raise ValueError("missing source preservation data: " + path)
        status = preservation["files"][path]["status"]
        candidate = path == "Solidity/Yul/Views/ReadControls.lean" and declaration["name"] in PAIRS
        progress = "candidate correspondence available" if candidate else "generic migration pending"
        claim = "preserved original source" if status == "unchanged" else status + "; preservation not established"
        rows.append(dict(path=path, line=declaration["line"], name=declaration["name"],
            statement_sha256=declaration["statement_sha256"], preservation_status=status,
            disposition=claim + "; " + progress))
    return rows

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    if args.output.resolve().is_relative_to(root): raise SystemExit("bulk output must be outside checkout")
    inventory = census.scan(root)
    preservation = source_preservation(root, inventory["files"])
    original_bytes = (root/"Solidity/Yul/Views/ReadControls.lean").read_bytes()
    if hashlib.sha256(original_bytes).hexdigest() != preservation["files"][
            "Solidity/Yul/Views/ReadControls.lean"]["source_sha256"]:
        raise ValueError("original source changed after preservation check")
    candidate_bytes = (root/"tests/h62/item4/generic-yul-views/Fixtures.lean").read_bytes()
    pairs = compare(original_bytes.decode(), candidate_bytes.decode())
    controls = control_rows(inventory, preservation)
    result = dict(schema_version=1,status="LEXICAL_CORRESPONDENCE_PASS",
        boundary="Unique unquoted theorem-name tokens and simple type syntax only; known compound term forms are refused, not parsed. Kernel equivalence/proofs pending. Preservation labels require matching frozen Git blobs; modified/added sources are not accepted as preserved. Control rows cover the current inventory; removed baseline files are listed separately.",
        pairs=pairs,original_control_theorems=controls,source_preservation=preservation,
        control_rows_scope="Current inventory under a legacy field name; not a reconstruction of the frozen case inventory.",
        original_sha256=hashlib.sha256(original_bytes).hexdigest(),
        candidate_sha256=hashlib.sha256(candidate_bytes).hexdigest())
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(status=result["status"],pairs=len(pairs),original_control_theorems=len(controls))))

if __name__ == "__main__": main()
