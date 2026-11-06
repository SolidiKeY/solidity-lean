#!/usr/bin/env python3
"""Refresh owned audit artifacts from source and an actual kernel axiom report.
Never writes the shared roots, module maps or central trust inventory.
"""
import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "tests/sol-expression-uniqueness"
AREA = ROOT / "Solidity/Frontend/ExpressionUniqueness"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def read(name):
    return json.loads((DATA/name).read_text())


def write(name, value):
    (DATA/name).write_text(json.dumps(value, indent=2)+"\n")


def collect():
    rows = []
    for path in sorted(AREA.rglob("*.lean")):
        source = path.read_text()
        matches = list(re.finditer(r"^(def|theorem|inductive)\s+(\w+)", source, re.M))
        for i, match in enumerate(matches):
            segment = source[match.start():matches[i+1].start() if i+1 < len(matches) else len(source)]
            rows.append(dict(module=path.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."),
                             kind=match[1], name="Solidity.Frontend.ExpressionUniqueness."+match[2],
                             source_signature=segment.split(":=", 1)[0].strip()))
    return rows


def inventory(tag):
    assert re.fullmatch(r"[a-z][a-z0-9-]*", tag)
    rows = collect()
    write("declarations.json", rows)
    imports = sorted({r["module"] for r in rows})
    (DATA/"signatures.lean").write_text("\n".join("import "+m for m in imports)+"\n\n"+
        "".join("#check "+r["name"]+"\n#print axioms "+r["name"]+"\n" for r in rows))
    manifest = read("registration-manifest.json")
    paths = sorted(AREA.rglob("*.lean"))
    manifest["modules"] = [p.relative_to(ROOT).as_posix() for p in paths]
    manifest["declarations"] = [r["name"] for r in rows]
    manifest["module_map_rows"] = []
    for path in paths:
        header = re.search(r"^# (.+)$", path.read_text(), re.M)
        manifest["module_map_rows"].append(dict(file="docs/module-map/frontend.d/expression-uniqueness.md",
            module=path.relative_to(ROOT).as_posix()[9:], description=header[1] if header else path.stem))
    manifest["central_axiom_registration"]["count"] = len(rows)
    write("registration-manifest.json", manifest)
    write("audit-runs.json", dict(proof_stem="checkpoint-proof-"+tag,
        proof_gate_dir="checkpoint-gates-"+tag, signature_stem="signature-audit-"+tag,
        signature_gate_dir="signature-gates-"+tag))
    print(f"AUDIT_INVENTORY: {len(paths)} modules, {len(rows)} source declarations")


def pins(report):
    """`report`: actual Lean output of `#print axioms` for every declaration, e.g.
    the messages of `signatures.lean` (the Codex-VM log was externalized under H44)."""
    rows = read("declarations.json")
    assert report is not None and report.is_file(), "pins needs --report <actual kernel axiom output>"
    axioms = {}
    messages = {}
    pattern = r"^'([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])$"
    for match in re.finditer(pattern, report.read_text(), re.M):
        assert match[1] not in axioms, "duplicate actual kernel axiom report"
        messages[match[1]] = match[0]
        axioms[match[1]] = [x.strip() for x in match[2].split(",") if x.strip()] if match[2] else []
    assert set(axioms) == {r["name"] for r in rows}, "incomplete actual kernel report"
    assert all(set(a) <= STANDARD for a in axioms.values()), "non-standard axiom"
    write("axioms.json", axioms)
    imports = sorted({r["module"] for r in rows})
    source = "\n".join("import "+m for m in imports)+"\n\n/-! Exact kernel-reported axiom pins for every source declaration in this lane. -/\n\n"
    for row in rows:
        name = row["name"]
        message = messages[name]
        source += f"/-- info: {message} -/\n#guard_msgs in #print axioms {name}\n\n"
    (AREA/"AxiomPins.lean").write_text(source.rstrip()+"\n")
    print(f"AUDIT_PINS: {len(axioms)} exact standard-only kernel axiom sets")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["inventory", "pins"])
    parser.add_argument("--tag", default="balance")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.mode == "inventory":
        inventory(args.tag)
    else:
        pins(args.report)
