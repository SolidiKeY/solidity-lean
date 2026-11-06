#!/usr/bin/env python3
"""Generate a complete Backend.Op recursor diagnostic; no original file edits."""
import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT/"Solidity/Backend/Opcode.lean"
SLICE = ROOT/"Solidity/Backend/Scalar/Slice.lean"
DEFAULT = ROOT/"tests/h62/item6/migrate-backend/OpcodeTernaryDependency.lean"

def generate():
    text = SOURCE.read_text()
    section = text.split("inductive Op where", 1)[1].split("deriving DecidableEq, Repr", 1)[0]
    constructors = re.findall(r"^  \| (\w+)(.*)$", section, re.M)
    expected = {"DUP": "(n : Fin 16)", "SWAP": "(n : Fin 16)", "LOG": "(n : Fin 5)"}
    if len(constructors) != 83 or len({name for name, _ in constructors}) != 83:
        raise ValueError("pinned opcode constructor inventory changed")
    parameters = {name: args.strip() for name, args in constructors if args.strip()}
    if parameters != expected:
        raise ValueError("pinned opcode parameters changed")
    original = SLICE.read_text()
    body = original.split("def ternary : Op → Option (Word → Word → Word → Word)", 1)[1].split("\ndef applyUnary", 1)[0]
    branches = []
    for name, args in constructors:
        if name == "ADDMOD":
            branch = "(some (fun a b k => if k == 0 then 0\n      else BitVec.ofNat 256 ((a.toNat + b.toNat) % k.toNat)))"
        elif name == "MULMOD":
            branch = "(some (fun a b k => if k == 0 then 0\n      else BitVec.ofNat 256 ((a.toNat * b.toNat) % k.toNat)))"
        elif args.strip():
            branch = "(fun _ => none)"
        else:
            branch = "none"
        branches.append("    " + branch + " -- " + name)
    result = """import Solidity.Backend.Opcode

/-!
Generated additive diagnostic; run generate_opcode_fixture.py --check.
The observed function copies the exact pinned Scalar.ternary body and type.
The candidate uses all 83 constructors of the actual Backend.Op datatype.
This fixture does not modify the original function or its frozen axiom pin.
-/
namespace MigrateBackendOpcodeFixture
open Solidity.Backend
abbrev Word := BitVec 256

def observed : Op → Option (Word → Word → Word → Word)""" + body + """
def candidate (op : Op) : Option (Word → Word → Word → Word) :=
  Op.casesOn op
""" + "\n".join(branches) + """

theorem candidate_eq_observed (op : Op) : candidate op = observed op := by
  cases op <;> rfl

/-- info: 'MigrateBackendOpcodeFixture.candidate' does not depend on any axioms -/
#guard_msgs in #print axioms candidate
#print axioms observed
#print axioms candidate_eq_observed

example (n : Fin 16) : candidate (.DUP n) = none := rfl
example (n : Fin 16) : candidate (.SWAP n) = none := rfl
example (n : Fin 5) : candidate (.LOG n) = none := rfl
example : (candidate .ADDMOD).map (fun f => f 7 9 0) = some 0 := rfl
example : (candidate .MULMOD).map (fun f => f 7 9 0) = some 0 := rfl
example : (candidate .ADDMOD).map (fun f => f 3 4 5) = some 2 := rfl
example : (candidate .MULMOD).map (fun f => f 3 4 5) = some 2 := rfl
example : (candidate .ADDMOD).map (fun f => f 3 4 5) ≠ some 3 := by
  decide +kernel

end MigrateBackendOpcodeFixture
"""
    metadata = {"constructors": [name for name, _ in constructors],
                "parameterized": parameters,
                "opcode_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                "slice_sha256": hashlib.sha256(SLICE.read_bytes()).hexdigest(),
                "fixture_sha256": hashlib.sha256(result.encode()).hexdigest(),
                "proof_status": "pending Lean verification; generation is not proof"}
    return result, metadata

def proposed_slice(fixture):
    original = SLICE.read_text()
    signature = "def ternary : Op → Option (Word → Word → Word → Word)"
    if original.count(signature) != 1:
        raise ValueError("ambiguous original ternary signature")
    candidate = fixture.split("def candidate (op : Op) : Option (Word → Word → Word → Word) :=",1)[1].split("\ntheorem candidate_eq_observed",1)[0]
    candidate = "\n".join("  "+line for line in candidate.strip("\n").splitlines())
    start = original.index(signature)
    end = original.index("\ndef applyUnary",start)
    replacement = signature+" :=\n  fun op =>\n"+candidate+"\n\n"
    proposed = original[:start]+replacement+original[end:]
    patch = "".join(difflib.unified_diff(original.splitlines(keepends=True),proposed.splitlines(keepends=True),
                      fromfile="a/Solidity/Backend/Scalar/Slice.lean",tofile="b/Solidity/Backend/Scalar/Slice.lean"))
    return proposed, patch

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT)
    parser.add_argument("--metadata", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--proposed-copy",type=Path)
    parser.add_argument("--proposal-patch",type=Path)
    args = parser.parse_args()
    source, metadata = generate()
    if args.check:
        if not args.output.exists() or args.output.read_text() != source:
            raise SystemExit("generated opcode fixture differs")
    else:
        args.output.write_text(source)
    if args.proposed_copy or args.proposal_patch:
        proposed, patch = proposed_slice(source)
        if args.proposed_copy: args.proposed_copy.write_text(proposed)
        if args.proposal_patch: args.proposal_patch.write_text(patch)
        metadata["proposed_copy_sha256"] = hashlib.sha256(proposed.encode()).hexdigest()
        metadata["proposal_patch_sha256"] = hashlib.sha256(patch.encode()).hexdigest()
        metadata["proposal_status"] = "not applied; owner relay, Lean proofs, full API validation and timing pending"
    if args.metadata:
        args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"constructors": len(metadata["constructors"]),
                      "fixture_sha256": metadata["fixture_sha256"],
                      "proof_status": metadata["proof_status"]}))
