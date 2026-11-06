#!/usr/bin/env python3
"""Reconcile the named relations with the supplemental lease, lexically.

This is not a Lean parser: import closure follows single-line, column-zero
`import` commands and ignores external modules and other import syntax.
"""
import hashlib
import json
import pathlib
import re
import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lexical import code_only, unknown_identifiers

ROOT = pathlib.Path(__file__).resolve().parents[4]
AGREEMENT = ROOT / "Solidity/Source/Agreement"
LEASED = """BoolSlotAndControls BoolSlotConditionalControls BoolSlotControls
BoolSlotNotControls BoolSlotOrControls BoolSlotReadControls BoolSlotRepeatedControls
BoolSlotSavedControls BoolSlotToggleControls NormalBoolAssignControls NormalBoolControls
NormalControls NormalDefaultControls PrimitiveCopySequenceControls PrimitiveSavedAssignControls
PrimitiveSlotAssignControls PrimitiveSlotControls PrimitiveSlotReverseControls""".split()
V07 = """AddressConversionControls AddressQualifierControls EnumConversionControls
EnumSignedCastControls FixedBytesAssignmentControls P12Controls UdvtAddressAssignmentControls
UdvtAssignmentControls UdvtBoolAssignmentControls UdvtFixedBytesAssignmentControls""".split()
G19 = """AssignmentDoWhileBreakControls AssignmentDoWhileContinueControls
AssignmentForBreakControls AssignmentForReturnControls AssignmentReturnFlagControls
AssignmentWhileBreakControls WhileReturnControls""".split()


def relative(path):
    return str(path.relative_to(ROOT))


def closure(path):
    seen, pending = set(), [path]
    while pending:
        current = pending.pop()
        if current in seen or not current.is_file():
            continue
        seen.add(current)
        for line in code_only(current.read_text()).splitlines():
            if line.startswith("import "):
                for module in line[7:].split():
                    pending.append(ROOT.joinpath(*module.split(".")).with_suffix(".lean"))
    return seen


def record(path):
    data = path.read_bytes()
    lines = code_only(data.decode()).splitlines()
    return {"path": relative(path), "sha256": hashlib.sha256(data).hexdigest(),
            "unknown_quoted_identifiers": unknown_identifiers(data.decode()),
            "declarations": [{"line": i, "name": m.group(2), "kind": m.group(1)}
                for i, line in enumerate(lines, 1)
                if (m := re.match(r"^(theorem|def|abbrev|lemma)\s+(\w+)", line))]}


def main():
    leased = [AGREEMENT / (name + ".lean") for name in LEASED]
    relations = ([ROOT / "Solidity/Lowering/V07" / (name + ".lean") for name in V07] +
                 [ROOT / "Solidity/Lowering/G19" / (name + ".lean") for name in G19])
    leased_set, relation_set = set(leased), set(relations)
    rows = []
    for path in leased + relations:
        row = record(path)
        reachable = closure(path)
        targets = relation_set if path in leased_set else leased_set
        row["opposite_set_reachable"] = sorted(map(relative, reachable & targets))
        row["bindingrel_lines"] = [i for i, line in enumerate(code_only(path.read_text()).splitlines(), 1)
                                   if re.search(r"\bBindingRel\b", line)]
        rows.append(row)
    print(json.dumps({"method": "comment/string-masked column-zero single-line imports; source files only",
                      "leased_controls": rows[:len(leased)], "relation_controls": rows[len(leased):]}, indent=2))


if __name__ == "__main__":
    main()
