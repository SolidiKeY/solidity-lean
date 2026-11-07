#!/usr/bin/env python3
"""Read-only observations for checked Source/Selected/Target/Agreement headers.

The original source bytes are pinned by the assigned base Git tree. This is a
manual textual ledger, not Lean parsing, proof checking or full case closure.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import re
import subprocess

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
FAMILIES = ("CheckedAdd", "CheckedSub", "CheckedMul", "SignedCheckedAdd", "SignedCheckedSub", "SignedCheckedMul")
FILES = ("Source.lean", "Selected.lean", "Target.lean", "Agreement.lean")
HEADER = re.compile(r"^(theorem|lemma|def|abbrev)\s+([^\s(:]+)")


def entries(family):
    sub = family.endswith("Sub")
    signed = family.startswith("Signed")
    operation = "subtraction" if sub else ("multiplication" if family.endswith("Mul") else "addition")
    failure = "underflow" if sub and not signed else "overflow"
    table = {
        "Source.lean": {
            "U": ("source_type", "Original 256-bit Source integer type."),
            "source_success": ("source_success", f"Checked {operation} succeeds when the original input/read and result-range premises hold; Source state is retained."),
            f"source_{failure}": ("source_failure", f"With the original in-range input and Source-read premises, checked {operation} outside its result range yields Source arithmetic panic data and retains Source state."),
        },
        "Selected.lean": {
            "value": ("selected_definition", f"Original intrinsic checked {operation} value over two target locals."),
            "selected": ("selected_definition", "Original compiled value with operand loads and its guard."),
            "public_selection": ("selection", "The public memory compiler selects the stated compiled value."),
            "original_guard": ("guard", "The selected code equals the stated original operand-load and guard sequence."),
        },
        "Target.lean": {
            "value_success": ("target_value_success", f"Under the original range/read premises, intrinsic {operation} value evaluation returns the fitted result."),
            f"value_{failure}": ("target_value_revert", f"Under the original in-range input, target-read and outside-result-range premises, intrinsic {operation} value evaluation returns revert."),
            "target_success": ("target_run_success", "Under the original representation/read/range premises, selected code pushes a represented result over the arbitrary saved tail."),
            f"target_{failure}": ("target_run_revert", "Under the original in-range input, read, representation and outside-result-range premises, selected code yields coarse revert, without target payload or reverted-state assertion."),
        },
        "Agreement.lean": {
            "success": ("joint_success", "Public selection, Source success and represented target success under the original input/result ranges, reads, correspondence, state-representation and arbitrary-tail premises."),
            failure: ("joint_failure", "Public selection, Source arithmetic panic/state and coarse target revert under the original in-range inputs, reads, outside-result-range, correspondence, representation and tail premises."),
        },
    }
    agreement = table["Agreement.lean"]
    if family in ("CheckedAdd", "CheckedMul"):
        agreement["overflow_iff"] = ("range_classification", "For the original in-range unsigned operands, result outside the range iff it exceeds the upper bound.")
    elif family in ("SignedCheckedSub", "SignedCheckedMul"):
        agreement["overflow_iff"] = ("range_classification", "Result outside signed range iff below the lower bound or above the upper bound, with the original hypotheses.")
    elif family == "CheckedSub":
        agreement.update({
            "underflow_iff": ("range_classification", "For the original in-range unsigned operands, difference outside range iff x<y."),
            "success_iff": ("range_classification", "For the original in-range unsigned operands, difference fits iff y≤x."),
            "classification": ("joint_classification", "Under the original correspondence/representation premises, classify the fitting y≤x branch and the underflow branch, including their stated Source and target observations."),
            "target_underflow_iff": ("target_classification", "Under the original target read/representation and arbitrary-tail premises, selected code reverts iff x<y."),
        })
    if family == "CheckedMul":
        agreement.update({
            "source_overflow_exact": ("source_classification", "Under the original Source reads and ranges, Source arithmetic panic/state iff product exceeds the unsigned upper bound."),
            "target_overflow_exact": ("target_classification", "Under the original target reads/representation and tail, selected code coarsely reverts iff product exceeds the unsigned upper bound."),
        })
    if family == "SignedCheckedMul":
        table["Selected.lean"]["guard_is_sTail"] = ("guard", "The selected original signed multiplication guard is the stated sTail code.")
    return table

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path.cwd())
parser.add_argument("--declarations", type=pathlib.Path, required=True)
parser.add_argument("--base-repository", type=pathlib.Path, help="Git repository containing the assigned base; defaults to --root")
args = parser.parse_args()
root = args.root.resolve()
base_repository = args.base_repository.resolve() if args.base_repository else root
rows = json.loads(args.declarations.read_text())["declarations"]
result = []
for family in FAMILIES:
    descriptions = entries(family)
    for name in FILES:
        relative = f"Solidity/Backend/PrimitivePackets/{family}/{name}"
        selected = [row for row in rows if row["file"] == relative]
        names = [row["name"] for row in selected]
        expected = descriptions[name]
        if len(set(names)) != len(names) or set(names) != set(expected):
            parser.error(f"{relative}: missing descriptions {sorted(set(names)-set(expected))}; stale descriptions {sorted(set(expected)-set(names))}; duplicates={len(names)!=len(set(names))}")
        source = (root / relative).read_bytes()
        original = subprocess.check_output(["git", "show", BASE + ":" + relative], cwd=base_repository)
        digest = hashlib.sha256(source).hexdigest()
        if source != original or any(row["sha256"] != digest for row in selected):
            parser.error(f"{relative}: source bytes differ from assigned base or census")
        headers = []
        for line_no, line in enumerate(source.decode("utf-8").splitlines(), 1):
            match = HEADER.match(line)
            if match:
                headers.append((line_no, match.group(1), match.group(2)))
        if [(row["line"], row["kind"], row["name"]) for row in selected] != headers:
            parser.error(f"{relative}: census headers differ from source")
        for row in selected:
            category, observation = expected[row["name"]]
            result.append({**row, "category": category, "observation": observation})
print(json.dumps({"method": "manual observations of pinned literal headers; original premises remain binding; not Lean parsing, proof checking or complete dependency closure", "counts": dict(sorted(collections.Counter(r["category"] for r in result).items())), "declarations": result}, ensure_ascii=False, indent=2))
