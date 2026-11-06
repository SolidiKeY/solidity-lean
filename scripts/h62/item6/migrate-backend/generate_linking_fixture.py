#!/usr/bin/env python3
"""Produce an unapplied proof-only Linking proposal; never edit the original."""
import argparse
import difflib
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT/"Solidity/Backend/Creation/Linking.lean"
OLD = "  · simpa only [Vector.length_toList] using disjoint"
NEW = "  · simpa only [Vector.length_toList, Location.Disjoint] using disjoint"

def validate_outputs(copy, patch, metadata):
    outputs = [path.resolve() for path in (copy,patch,metadata)]
    if SOURCE.resolve() in outputs or len(set(outputs)) != len(outputs):
        raise ValueError("outputs must be distinct and cannot alias the original source")
    allowed = (ROOT/"tests/h62/item6/migrate-backend", Path("/workspace/migrate-backend-evidence"))
    if any(not any(path.is_relative_to(folder.resolve()) for folder in allowed) for path in outputs):
        raise ValueError("proposal outputs must stay in assigned tests or off-git evidence")
    return outputs

def generate():
    original = SOURCE.read_text()
    if original.count(OLD) != 1:
        raise ValueError("expected unique frozen disjoint proof step")
    proposed = original.replace(OLD,NEW)
    # Git accepts empty context lines without their optional leading space.
    # Omit that space so a tracked patch also passes git diff --check.
    patch = "".join(difflib.unified_diff(original.splitlines(keepends=True),proposed.splitlines(keepends=True),
        fromfile="a/Solidity/Backend/Creation/Linking.lean",tofile="b/Solidity/Backend/Creation/Linking.lean"))
    patch = "".join("\n" if line == " \n" else line for line in patch.splitlines(keepends=True))
    return proposed, patch, {"status":"unverified draft; no original edit or compatible-build claim",
        "source":"Solidity/Backend/Creation/Linking.lean",
        "source_sha256":hashlib.sha256(original.encode()).hexdigest(),
        "proposed_sha256":hashlib.sha256(proposed.encode()).hexdigest(),
        "patch_sha256":hashlib.sha256(patch.encode()).hexdigest(),
        "theorem":"Solidity.Backend.Creation.two_links_commute",
        "change":"Explicitly unfold Location.Disjoint in the existing simpa proof; all statements and other source bytes remain unchanged.",
        "ticket_basis":"H70 supplied line109 failure summary only; full staged payload requested and not yet reviewed",
        "remaining":["full verified H70 payload","live-owner coordination before original-file edits","Lean4.24/4.35 diagnostics","axiom and frozen API checks","proof budgets and timings","full affected validation"]}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--copy",type=Path,required=True)
    parser.add_argument("--patch",type=Path,required=True)
    parser.add_argument("--metadata",type=Path,required=True)
    parser.add_argument("--check",action="store_true")
    args = parser.parse_args()
    args.copy,args.patch,args.metadata = validate_outputs(args.copy,args.patch,args.metadata)
    proposed,patch,metadata = generate()
    if args.check:
        if args.copy.read_text() != proposed or args.patch.read_text() != patch:
            raise SystemExit("linking proposal differs from deterministic generator")
    else:
        args.copy.write_text(proposed);args.patch.write_text(patch)
    args.metadata.write_text(json.dumps(metadata,indent=2,sort_keys=True)+"\n")
    print(json.dumps(metadata))
