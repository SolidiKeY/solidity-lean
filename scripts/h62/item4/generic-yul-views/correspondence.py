#!/usr/bin/env python3
"""Exact lexical type correspondence; external acceptance, not a Lean proof."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import census

PAIRS = {"byte_component": "original_byte_component", "byte_component_decode": "original_byte_component_decode"}

def theorem_types(text):
    code = census.mask(text)
    declarations = list(census.DECL.finditer(code))
    result = {}
    for i, match in enumerate(declarations):
        if match["kind"] != "theorem": continue
        end = declarations[i+1].start() if i+1 < len(declarations) else len(text)
        tail = code[match.end():end]
        name = re.match(r"\s+(\w+)", tail)
        if not name: raise ValueError("unsupported theorem identifier")
        prefix = tail[name.end():]
        prefix = prefix[:census.statement_end(prefix)]
        result[name[1]] = " ".join(prefix.split())
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

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    if args.output.resolve().is_relative_to(root): raise SystemExit("bulk output must be outside checkout")
    original = (root/"Solidity/Yul/Views/ReadControls.lean").read_text()
    candidate = (root/"tests/h62/item4/generic-yul-views/Fixtures.lean").read_text()
    pairs = compare(original, candidate)
    inventory = census.scan(root)
    controls = [dict(path=d["path"],line=d["line"],name=d["name"],statement_sha256=d["statement_sha256"],
        disposition="preserved original; candidate correspondence available" if d["path"].endswith("/ReadControls.lean") and d["name"] in PAIRS else "preserved original; generic migration pending")
        for d in inventory["declarations"] if d["in_controls_file"] and d["kind"] == "theorem"]
    result = dict(schema_version=1,status="LEXICAL_CORRESPONDENCE_PASS",boundary="whitespace-normalized lexical types only; kernel equivalence and proofs pending",pairs=pairs,original_control_theorems=controls)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(status=result["status"],pairs=len(pairs),original_control_theorems=len(controls))))

if __name__ == "__main__": main()
