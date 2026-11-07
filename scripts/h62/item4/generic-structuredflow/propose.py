#!/usr/bin/env python3
"""Export an UNAPPLIED exact-statement owner patch; never modify originals.
The generated patch is a proposal, not a proof or owner authorization.
"""
import argparse
import difflib
import json
from pathlib import Path
import re
import census as c

HELPER = "import tests.h62.item4.«generic-structuredflow».GenericMapped\n"
TARGETS = {"ForBreakCompilerControls": ["observed", "nonzero_frame"],
           "WhileBreakCompilerControls": ["observed", "nonzero_frame"],
           "ForReturnCompilerControls": ["observed", "nonzero_frame"],
           "WhileReturnCompilerControls": ["observed", "nonzero_frame"],
           "DoWhileBreakCompilerControls": ["observed"],
           "DoWhileContinueCompilerControls": ["observed"]}


def proposal():
    inventory = c.census(c.BASE)
    if c.census() != inventory:
        raise ValueError("original source drift; review before proposal")
    changes, rows = [], []
    for basename, selected in sorted(TARGETS.items()):
        path = c.FAMILY + basename + ".lean"
        old = (c.ROOT/path).read_bytes().decode()
        new = old
        originals = [row for row in inventory["declarations"] if row["path"] == path]
        for short in selected:
            row, = [row for row in originals if row["name"].endswith("."+short)]
            statement = row["statement"]
            goal = statement.split(" :\n", 1)[1]
            goal, replaced = re.subn(r"emit (?:\(C := C\) )?(0|128) mapping \.here \(\.there \.here\) rfl rfl",
                                     lambda m: f"compileProg {m[1]} (GenericMapped.program C GenericMapped.copyFixture)", goal)
            if replaced != 1:
                raise ValueError("unexpected selected statement " + row["name"])
            start = new.index(statement) + len(statement)
            end = new.find("\n\n", start)
            if end < 0:
                raise ValueError("missing proof boundary " + row["name"])
            proof = " := by\n  change " + goal.strip() + "\n  rw [GenericMapped.compiled_execution]\n  rfl"
            new = new[:start] + proof + new[end:]
            rows.append(dict(name=row["name"], path=path, statement_sha256=row["statement_sha256"],
                             helper="GenericMapped.compiled_execution", fixture="copyFixture", checked=False))
        new = HELPER + new
        parsed = c.records(path, new)
        if [(r["name"],r["statement_sha256"]) for r in originals] != [(r["name"],r["statement_sha256"]) for r in parsed]:
            raise ValueError("statement or inventory drift in proposal " + path)
        changes.append("".join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True), fromfile="a/"+path, tofile="b/"+path)))
    return "".join(changes), rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output == c.ROOT or c.ROOT in output.parents:
        raise SystemExit("H44: export outside git")
    output.mkdir(parents=True, exist_ok=True)
    patch, rows = proposal()
    (output/"proposed-owner.patch").write_text(patch)
    report = dict(status="UNVALIDATED_UNAPPLIED", checked=False, integration_ready=False, registration_required="tests/h62/item4/generic-structuredflow/registration.md", owner="V17", scope="Exact six listed original Controls files; no source outcomes/refusals changed",
                  files=sorted({r["path"] for r in rows}), changed_proofs=rows,
                  exact_statement_preservation=True, owner_agreement_received=False,
                  patch_sha256=c.sha(patch), negatives="Every original declaration is retained; original negative proofs are byte-identical.")
    (output/"proposal.json").write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps(dict(status=report["status"], changed_proofs=len(rows), files=len(report["files"]), sha256=report["patch_sha256"])))


if __name__ == "__main__":
    main()
