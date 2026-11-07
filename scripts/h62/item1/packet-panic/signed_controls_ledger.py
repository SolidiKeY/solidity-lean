#!/usr/bin/env python3
"""Map reviewed signed checked Controls headers to case observations.

This is a textual ledger, not Lean elaboration, semantic closure, or an
ownership grant. Raw source hashes and all literal headers must match.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re

PIN = {
    "SignedCheckedAdd": "f81ee25a921f121417b3fdf17361185d49ef87e42e49196a023270751ed95f0a",
    "SignedCheckedSub": "a43b1300cbd02de51caf88d733db1aa3f8e270d96d2b4cc8467d0db0bf333f91",
    "SignedCheckedMul": "de7957f5fc5798d9ec349851e6aa9c0ee0bd3fbfc03b2e2121d6a02d462d8519",
}
HEADER = re.compile(r"^(theorem|lemma|def|abbrev)\s+([^\s(:]+)")
ADD = {
    "Γ": ("fixture", "Source context with two signed integer locals."),
    "input": ("fixture", "Source locals and initial state for in-range signed operands."),
    "success": ("source_success", "Checked signed addition succeeds when both inputs and their sum fit; pipeline parameter, fuel 3 and Source state are explicit."),
    "failure": ("source_failure", "Checked signed addition outside range yields Source arithmetic panic and unchanged state at fuel 3."),
    "maximum": ("source_success", "Instantiate hi+0 for pipeline p."),
    "minimum": ("source_success", "Instantiate lo+0 for pipeline p."),
    "positiveOverflow": ("source_failure", "Instantiate hi+1 for pipeline p."),
    "negativeOverflow": ("source_failure", "Instantiate lo+(-1) for pipeline p."),
    "mixedSigns": ("source_success", "Instantiate (-7)+9 for pipeline p."),
    "panic_not_empty": ("source_bytes_negative", "Source arithmetic panic is not empty."),
    "exact_panic": ("source_bytes", "Source arithmetic panic equals selector, 31 zeros and 0x11."),
}
COMMON = {
    "si": ("fixture", "Select one of two Source signed local indices."),
    "ti": ("fixture", "Select one of two target signed local indices in SignedDiv fixture."),
    "family": ("fixture", "Prove Source/target local correspondence and alias relation."),
    "maximum": ("fixture", "Maximum signed 256-bit value 2^255-1."),
    "minimum": ("fixture", "Minimum signed 256-bit value -2^255."),
    "one": ("fixture", "Signed integer value 1."),
    "minus": ("fixture", "Signed integer value -1."),
    "seven": ("fixture", "Signed integer value 7."),
    "two": ("fixture", "Signed integer value 2."),
    "zero": ("fixture", "Signed integer value 0."),
    "exact_panic": ("source_bytes", "Source arithmetic panic equals decimal selector, 31 zeros and code 17."),
}
SUB = {
    "joint_success": ("joint_success", "For fitting a-b, instantiate Source and target success with pipeline p and arbitrary saved tail."),
    "joint_overflow": ("joint_failure", "For outside-range a-b, instantiate Source panic and coarse target revert with pipeline p and tail."),
    "upper": ("joint_failure", "Instantiate maximum-(-1), upper overflow."),
    "lower": ("joint_failure", "Instantiate minimum-1, lower overflow."),
    "regular": ("joint_success", "Instantiate 7-2 success."),
    "minimum_success": ("joint_success", "Instantiate minimum-0 success."),
    "maximum_success": ("joint_success", "Instantiate maximum-0 success."),
    "upper_not_wrap": ("negative", "Upper-overflow run is not a successful wrapped-minimum result."),
    "wrong_result": ("negative", "Successful 7-2 run is not a successful result 9."),
    "low_fuel": ("timeout", "Source checked 7-2 at zero fuel times out."),
}
MUL = {
    "negSeven": ("fixture", "Signed integer value -7."),
    "nine": ("fixture", "Signed integer value 9."),
    "negNine": ("fixture", "Signed integer value -9."),
    "joint_success": ("joint_success", "For fitting a*b, instantiate Source and target success with pipeline p and arbitrary saved tail."),
    "joint_overflow": ("joint_failure", "For outside-range a*b, instantiate Source panic and coarse target revert with pipeline p and tail."),
    "minimum_minus": ("joint_failure", "Instantiate minimum*(-1), overflow."),
    "minus_minimum": ("joint_failure", "Instantiate (-1)*minimum, overflow."),
    "upper": ("joint_failure", "Instantiate maximum*2, upper overflow."),
    "upper_negative": ("joint_failure", "Instantiate minimum*minimum, upper overflow."),
    "lower": ("joint_failure", "Instantiate minimum*2, lower overflow."),
    "lower_swapped": ("joint_failure", "Instantiate 2*minimum, lower overflow."),
    "lower_maximum": ("joint_failure", "Instantiate maximum*(-9), lower overflow."),
    "regular": ("joint_success", "Instantiate (-7)*9 success."),
    "regular_positive": ("joint_success", "Instantiate (-7)*(-9) success."),
    "regular_both_positive": ("joint_success", "Instantiate 7*9 success."),
    "regular_swapped": ("joint_success", "Instantiate 9*(-7) success."),
    "minimum_one": ("joint_success", "Instantiate minimum*1 success."),
    "one_minimum": ("joint_success", "Instantiate 1*minimum success."),
    "maximum_minus": ("joint_success", "Instantiate maximum*(-1) success."),
    "minus_maximum": ("joint_success", "Instantiate (-1)*maximum success."),
    "minimum_zero": ("joint_success", "Instantiate minimum*0 success."),
    "zero_minimum": ("joint_success", "Instantiate 0*minimum success."),
    "guard_classification": ("target_guard", "For bounded operand words and arbitrary tail, sTail mul returns the in-range signed product or coarse revert."),
    "minimum_minus_not_wrap": ("negative", "minimum*(-1) is not a successful wrapped-minimum run."),
    "minus_minimum_not_wrap": ("negative", "(-1)*minimum is not a successful wrapped-minimum run."),
    "regular_exact": ("target_success", "The (-7)*9 run pushes the exact -63 word with arbitrary saved tail."),
    "wrong_result": ("negative", "The (-7)*9 run does not successfully push +63."),
    "low_fuel": ("timeout", "Source checked 7*2 at zero fuel times out."),
}

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
parser.add_argument("--declarations", type=pathlib.Path, required=True)
args = parser.parse_args()
root = args.root.resolve()
rows = json.loads(args.declarations.read_text())["declarations"]
result = []
for family, descriptions in (("SignedCheckedAdd", ADD), ("SignedCheckedSub", {**COMMON, **SUB}), ("SignedCheckedMul", {**COMMON, **MUL})):
    relative = f"Solidity/Backend/PrimitivePackets/{family}/Controls.lean"
    selected = [row for row in rows if row["file"] == relative]
    names = [row["name"] for row in selected]
    if len(set(names)) != len(names) or set(names) != set(descriptions):
        parser.error(f"{relative}: missing descriptions {sorted(set(names)-set(descriptions))}; stale descriptions {sorted(set(descriptions)-set(names))}; duplicates={len(names)!=len(set(names))}")
    source = (root / relative).read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    if digest != PIN[family] or any(row["sha256"] != digest for row in selected):
        parser.error(f"{relative}: reviewed source hash mismatch")
    headers = []
    for line_no, line in enumerate(source.decode("utf-8").splitlines(), 1):
        found = HEADER.match(line)
        if found:
            headers.append((line_no, found.group(1), found.group(2)))
    if [(row["line"], row["kind"], row["name"]) for row in selected] != headers:
        parser.error(f"{relative}: census headers differ from source")
    for row in selected:
        category, observation = descriptions[row["name"]]
        result.append({**row, "category": category, "observation": observation})
print(json.dumps({"method": "manual observations mapped to pinned literal headers; not Lean parsing, proof checking or semantic dependency closure", "counts": dict(sorted(collections.Counter(row["category"] for row in result).items())), "declarations": result}, ensure_ascii=False, indent=2))
