#!/usr/bin/env python3
"""Frozen-source census. Source signatures are evidence, never Lean validation.

Include every theorem (even unconditional ones), so a heuristic cannot omit a
premise. Preserve raw signatures and source hashes. Section context is retained
as raw source as well; elaborated types/witnesses require a separate Lean gate.
Bulk JSON is written only to the requested external destination.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPRESENTATIONS = {
    "CallerWordBytes.recovered": ["WordFrame"],
    "CallerWordBytes.typed": ["StateRepr", "WordFrame"],
    "NativeParentWord.represented_counter": ["StateRepr"],
    "NativeParentWord.native_parent": ["InterfaceV1.Entry"],
    "MutatingEntryWords.represented_element": ["StateRepr"],
    "MutatingEntryWords.observed_activation": ["StateRepr", "StructAllocatorRepr"],
    "MutatingWritePhysical.write_prefix": ["StateRepr", "WordFrame"],
}

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MAP = "docs/module-map/abi-world.d/00-base.md"

def frozen(path):
    return subprocess.check_output(["git", "show", f"{BASE}:{path}"]).decode()

def digest(s):
    return hashlib.sha256(s.encode()).hexdigest()

def mask(source):
    # Preserve offsets/newlines while masking nested comments and strings.
    out = list(source)
    i, depth = 0, 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i+2] = "  "; depth += 1; i += 2
            elif source.startswith("-/", i):
                out[i:i+2] = "  "; depth -= 1; i += 2
            else:
                if source[i] != "\n": out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            out[i:i+2] = "  "; depth = 1; i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0: end = len(source)
            out[i:end] = " " * (end-i); i = end
        elif source[i] == chr(34):
            out[i] = " "; i += 1
            while i < len(source):
                c = source[i]
                if c != "\n": out[i] = " "
                i += 1
                if c == chr(92) and i < len(source):
                    out[i] = " "; i += 1
                elif c == chr(34): break
        else: i += 1
    assert depth == 0, "unclosed source comment"
    return "".join(out)

def module_paths(text):
    paths = []
    for cell in re.findall(r"^\| `([^`]+)` \|", text, re.M):
        if cell.startswith("Backend/"): path = "Solidity/" + cell
        elif cell.startswith("Solidity.Backend."): path = cell.replace(".", "/") + ".lean"
        else: raise ValueError(f"unrecognized module-map row: {cell}")
        assert path not in paths, f"duplicate map module {path}"
        paths.append(path)
    return paths

def declarations(path, source):
    clean = mask(source)
    # These frozen files use ordinary namespace/end and no namespace aliases.
    events = list(re.finditer(r"(?m)^\s*(?:(private|protected)\s+)?(namespace|section|end|variable|theorem|lemma)\b([^\n]*)", clean))
    stack, rows = [], []
    for event in events:
        kind, rest = event.group(2), event.group(3).strip()
        if kind in ("namespace", "section"):
            stack.append((kind, rest.split()[0] if rest else "")); continue
        if kind == "end":
            assert stack, (path, event.start())
            stack.pop(); continue
        if kind == "variable": continue
        name = rest.split()[0]
        begin = clean.index(kind, event.start())
        pos, nesting, pending_let = begin, 0, 0
        while pos < len(clean):
            c = clean[pos]
            if c in "({[⟨": nesting += 1
            elif c in ")}]⟩": nesting -= 1
            if nesting == 0 and re.match(r"let\b", clean[pos:]) and (pos == 0 or not clean[pos-1].isalnum()):
                pending_let += 1
            if nesting == 0 and clean.startswith(":=", pos):
                if pending_let:
                    pending_let -= 1
                    # Frozen-map by-valued result lets are single-line blocks.
                    # Skip their nested `have ... :=` assignments as one value.
                    if re.match(r"\s*by\b", clean[pos+2:]):
                        pos = clean.index("\n", pos)
                        continue
                    pos += 2
                    continue
                break
            pos += 1
        assert pos < len(clean), (path, name, "missing proof delimiter")
        signature = source[begin:pos].rstrip()
        namespace = ".".join(n for k,n in stack if k == "namespace")
        fq = name.removeprefix("_root_.") if name.startswith("_root_.") else namespace + "." + name
        provenance = subprocess.check_output(["git", "log", "-1", "--format=%H %an %s", BASE, "--", path], text=True).strip()
        rows.append(dict(name=fq, path=path, line=source.count("\n", 0, begin)+1,
            visibility=event.group(1) or "public", signature=signature,
            signature_sha256=digest(signature), source_sha256=digest(source),
            section_context=[source[e.start():clean.find("\n",e.start())].strip() for e in events if e.start()<event.start() and e.group(2)=="variable"],
            owner="solidity-v12-v17-20261031/v13-abi-world",
            owner_key="H30-WRITER-solidity-v12-v17-20261031--v13-abi-world",
            owner_status="coordination-only",
            owner_snapshot_sha256="7f5d40d46d386ed17731db55ed87f0564f5c9e667bddee00c0f12b28772f9cce",
            last_change_provenance=provenance,
            global_producer_premises=[],
            representation_premises=REPRESENTATIONS.get(fq.removeprefix("Solidity.Backend.AbiWorld."), []),
            premise_classification="fixed-input representation plus local feasibility" if fq.removeprefix("Solidity.Backend.AbiWorld.") in REPRESENTATIONS else "data/type/instance parameters and local feasibility, or no binders; no direct global producer premise",
            classification_boundary="source-reviewed; individual elaborated binder census remains a final gate",
            simultaneous_witness="pending", fidelity_gate="pending"))
    assert not stack, (path, stack)
    return rows

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    assert not args.output.resolve().is_relative_to(root), "H44 bulk output must be outside git"
    mapping = frozen(MAP)
    paths = module_paths(mapping)
    rows = [row for p in paths for row in declarations(p, frozen(p))]
    assert len({r["name"] for r in rows}) == len(rows), "duplicate declaration"
    all_files = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE, "Solidity/Backend/AbiWorld"], text=True).splitlines()
    result = dict(base=BASE, module_map=MAP, module_map_sha256=digest(mapping),
        mapped_modules=paths, unmapped_directory_files=sorted(set(all_files)-set(paths)),
        count=len(rows), declarations=rows,
        boundary="Conservative source census including unconditional declarations. No proof or elaborated-signature claim.")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps(dict(mapped_modules=len(paths), declarations=len(rows),
        unmapped=len(result["unmapped_directory_files"]), sha256=hashlib.sha256(args.output.read_bytes()).hexdigest())))

if __name__ == "__main__": main()
