#!/usr/bin/env python3
"""Reconcile manually reviewed observations with three textual Controls censuses."""
import argparse
import collections
import hashlib
import json
import pathlib
import re

REVIEWED_SHA256 = {
    "CheckedAdd": "ff70bbe874d62c9ef29ef8aafbaba13806024522feb9a2dcfe4f1843ff78aaad",
    "CheckedSub": "6076f049bccc97e12e08c10512770cb9597a1cd79394a0111a41367a0143c945",
    "CheckedMul": "1ed6c50483da571ca9ab70e85c5e71900fe112a7a05e24ef359899bdc49a56a8",
}
HEADER = re.compile(r"^(theorem|lemma|def|abbrev)\s+([^\s(:]+)")

COMMON = {
    "Γ": ("fixture", "Target context with two uint locals and caller context."),
    "F": ("fixture", "Initial fragment for the target context."),
    "srcΓ": ("fixture", "Source context with two uint256 locals."),
    "nat_range": ("fixture", "A natural below W fits the source uint256 range."),
    "u": ("fixture", "Construct target uint value from an in-range natural."),
    "source": ("fixture", "Construct source locals and initial source state."),
    "target": ("fixture", "Construct target locals with caller context."),
    "machine": ("fixture", "Write y at cell 4 and x at cell 5 in the populated machine."),
    "si": ("fixture", "Select one of two Source local indices."),
    "ti": ("fixture", "Select one of two target local indices."),
    "family": ("fixture", "Prove Source and target local correspondence."),
    "represented": ("fixture", "Prove StateRepr 1 0 8 for the populated machine; Add/Sub use CompileExamples and Mul uses Populated."),
    "wrong_value_refused": ("negative", "A mismatched Source and target value cannot satisfy local correspondence."),
    "wrong_index_refused": ("negative", "Aliasing both target indices cannot satisfy the stated correspondence."),
    "protectedCells": ("fixture", "List the selected protected memory locations."),
    "protected_frame": ("fixture", "Compute the selected initial memory cells in the populated fixture."),
    "low_fuel": ("timeout", "Zero Source fuel yields timeout on the regular checked expression."),
    "exact_panic_bytes": ("source_bytes", "Source arithmetic panic equals selector plus 31 zeros and code 0x11."),
    "panic_not_truncated": ("source_bytes_negative", "Source arithmetic panic differs from the five-byte truncated sequence."),
    "panic_not_empty": ("source_bytes_negative", "Source arithmetic panic is not empty."),
}
ADD = {
    "sumCode": ("fixture", "Selected checked addition instruction code."),
    "result": ("target_success", "For x<W, y<W and x+y<W, selected code pushes the exact sum with arbitrary saved tail."),
    "minimum": ("target_success", "0+0 yields 0."),
    "maximum": ("target_success", "(W-1)+0 yields W-1."),
    "regular": ("target_success", "7+9 yields 16."),
    "overflow": ("target_revert", "(W-1)+1 yields coarse target revert."),
    "double_overflow": ("target_revert", "(W-1)+(W-1) yields coarse target revert."),
    "jointSuccess": ("joint_success", "Instantiates Source/target success for 7+9, pipeline p and saved tail."),
    "jointOverflow": ("joint_failure", "Instantiates Source panic and coarse target revert for (W-1)+1, pipeline p and saved tail."),
    "sourceSuccess": ("source_success", "Instantiates Source success for 7+9 and pipeline p at theorem fuel parameter 0 (evaluation fuel 3)."),
    "sourceOverflow": ("source_failure", "Instantiates Source arithmetic panic for (W-1)+1 and pipeline p at theorem fuel parameter 0 (evaluation fuel 3)."),
}
SUB = {
    "differenceCode": ("fixture", "Selected checked subtraction instruction code."),
    "result": ("target_success", "For x<W, y<W and y≤x, selected code pushes the exact difference with arbitrary saved tail."),
    "minimum": ("target_success", "0-0 yields 0."),
    "maximum": ("target_success", "(W-1)-0 yields W-1."),
    "equal": ("target_success", "7-7 yields 0."),
    "regular": ("target_success", "9-7 yields 2."),
    "underflow": ("target_revert", "0-1 yields coarse target revert."),
    "far_underflow": ("target_revert", "0-(W-1) yields coarse target revert."),
    "wrong_order_refused": ("target_revert", "7-9 yields coarse target revert."),
    "jointSuccess": ("joint_success", "Instantiates classification for 9-7, pipeline p and saved tail."),
    "jointUnderflow": ("joint_failure", "Instantiates classification for 0-1, pipeline p and saved tail."),
    "sourceSuccess": ("source_success", "Instantiates Source success for 9-7 and pipeline p at theorem fuel parameter 0 (evaluation fuel 3)."),
    "sourceUnderflow": ("source_failure", "Instantiates Source arithmetic panic for 0-1 and pipeline p at theorem fuel parameter 0 (evaluation fuel 3)."),
    "corrupted_tail_refused": ("negative", "The 9-7 success cannot replace saved word 77 by 88."),
    "underflow_does_not_wrap": ("negative", "The 0-1 run is not a successful W-1 result."),
}
MUL = {
    "productCode": ("fixture", "Selected checked multiplication instruction code."),
    "result": ("target_success", "For x<W, y<W and x*y<W, selected code pushes the exact product with arbitrary saved tail."),
    "minimum": ("target_success", "0*0 yields 0."),
    "zero_left": ("target_success", "0*(W-1) yields 0."),
    "zero_right": ("target_success", "(W-1)*0 yields 0."),
    "maximum": ("target_success", "(W-1)*1 yields W-1."),
    "regular": ("target_success", "7*9 yields 63."),
    "overflow": ("target_revert", "(W-1)*2 yields coarse target revert."),
    "double_overflow": ("target_revert", "(W-1)*(W-1) yields coarse target revert."),
    "jointSuccess": ("joint_success", "Instantiates Source/target success for 7*9, pipeline p and saved tail."),
    "jointMaximum": ("joint_success", "Instantiates Source/target success for (W-1)*1, pipeline p and saved tail."),
    "jointZeroLeft": ("joint_success", "Instantiates Source/target success for 0*(W-1), pipeline p and saved tail."),
    "jointZeroRight": ("joint_success", "Instantiates Source/target success for (W-1)*0, pipeline p and saved tail."),
    "jointOverflow": ("joint_failure", "Instantiates Source panic and coarse target revert for (W-1)*2, pipeline p and saved tail."),
    "sourceSuccess": ("source_success", "Instantiates Source success for 7*9 and pipeline p at theorem fuel parameter 0 (evaluation fuel 3)."),
    "sourceOverflow": ("source_failure", "Instantiates Source arithmetic panic for (W-1)*2 and pipeline p at theorem fuel parameter 0 (evaluation fuel 3)."),
}

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
parser.add_argument("--declarations", type=pathlib.Path, required=True)
args = parser.parse_args()
root = args.root.resolve()
rows = json.loads(args.declarations.read_text())["declarations"]
result = []
for family, extra in (("CheckedAdd", ADD), ("CheckedSub", SUB), ("CheckedMul", MUL)):
    descriptions = {**COMMON, **extra}
    relative = f"Solidity/Backend/PrimitivePackets/{family}/Controls.lean"
    selected = [row for row in rows if row["file"] == relative]
    names = [row["name"] for row in selected]
    if len(set(names)) != len(names) or set(names) != set(descriptions):
        parser.error(f"{relative}: missing descriptions {sorted(set(names)-set(descriptions))}; stale descriptions {sorted(set(descriptions)-set(names))}; duplicate names={len(names)!=len(set(names))}")
    source = (root / relative).read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    if digest != REVIEWED_SHA256[family]:
        parser.error(f"{relative}: reviewed base hash mismatch")
    if any(row["sha256"] != digest for row in selected):
        parser.error(f"{relative}: source hash mismatch")
    headers = []
    for line_no, line in enumerate(source.decode("utf-8").splitlines(), 1):
        found = HEADER.match(line)
        if found:
            headers.append((line_no, found.group(1), found.group(2)))
    supplied = [(row["line"], row["kind"], row["name"]) for row in selected]
    if supplied != headers:
        parser.error(f"{relative}: census headers differ from source")
    for row in selected:
        category, observation = descriptions[row["name"]]
        result.append({**row, "category": category, "observation": observation})
print(json.dumps({"method": "manual observations mapped to literal declaration headers; not Lean parsing or proof checking", "counts": dict(sorted(collections.Counter(row["category"] for row in result).items())), "declarations": result}, ensure_ascii=False, indent=2))
