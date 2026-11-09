#!/usr/bin/env python3
"""Guard duplicate/negative source credit when planning a fresh kernel witness audit.

This generates external code and a source-only index, never kernel or historical
acceptance. Imported schema/axiom diagnostics are emitted by WitnessAccounting.
"""
import argparse
import contextlib
import hashlib
import json
import re
from pathlib import Path
from census import BASE, mask, scan
from source_only import generate

ROOT = Path(__file__).resolve().parents[4]


def associations(path, source):
    declarations = [r["name_candidate"] for r in scan(path, source.encode(), {"language"})]
    rows, negatives, guard = [], [], False
    for line in mask(source).splitlines():
        line = line.strip()
        if not line:
            continue
        if line == "#guard_msgs in":
            if guard:
                raise ValueError("nested guard needs explicit handling")
            guard = True
            continue
        if line.startswith("#guard_msgs"):
            raise ValueError("unsupported guard syntax: " + line)
        match = re.fullmatch(r"#verify_(?:fixed_)?hypotheses (\S+) for (\S+)", line)
        if match:
            witness, target = match.groups()
            if guard:
                negatives.append({"module": path, "witness": witness, "target": target})
                guard = False
                continue
            hits = [d for d in declarations if d == witness or d.endswith("." + witness)]
            if len(hits) != 1 or not target.startswith("Solidity."):
                raise ValueError("unresolved witness or target: " + line)
            rows.append({"module": path, "witness": hits[0], "target": target})
        elif guard or line.startswith(("#verify_hypotheses", "#verify_fixed_hypotheses")):
            raise ValueError("unsupported guarded/association syntax: " + line)
    if guard:
        raise ValueError("unterminated guard")
    return rows, negatives


def unique(rows):
    for key in ("witness", "target"):
        values = [row[key] for row in rows]
        if len(values) != len(set(values)):
            raise ValueError("duplicate " + key)


def plan(paths):
    frozen = generate()
    by_name = {}
    for row in frozen["declarations"]:
        by_name.setdefault(row["name_candidate"], []).append(row)
    rows, negatives, hashes = [], [], {}
    for path in paths:
        module = Path(path)
        if module.is_absolute() or ".." in module.parts or module.suffix != ".lean":
            raise ValueError("repository-relative Lean module required")
        raw = (ROOT / path).read_bytes()
        source = raw.decode()
        hashes[path] = hashlib.sha256(raw).hexdigest()
        positive, negative = associations(path, source)
        rows.extend(positive)
        negatives.extend(negative)
    unique(rows)
    if not rows:
        raise ValueError("no positive associations supplied")
    accounting = "tests/h62/item2/audit-language/WitnessAccounting.lean"
    hashes[accounting] = hashlib.sha256((ROOT / accounting).read_bytes()).hexdigest()
    current = {}
    for row in rows:
        hits = by_name.get(row["target"], [])
        if len(hits) != 1:
            raise ValueError("ambiguous or absent frozen target: " + row["target"])
        original = hits[0]
        path = original["path"]
        if path not in current:
            raw = (ROOT / path).read_bytes()
            hashes[path] = hashlib.sha256(raw).hexdigest()
            parsed = scan(path, raw, {"language"})
            current[path] = {r["name_candidate"]: r for r in parsed}
            if len(current[path]) != len(parsed):
                raise ValueError("duplicate current source declaration")
        live = current[path][row["target"]]
        for field in ("source_signature", "section_variables"):
            if live[field] != original[field]:
                raise ValueError("frozen header/context changed: " + row["target"])
        row.update(source_id=original["id"], signature_sha256=original["signature_sha256"],
                   frozen_header_context_match=True)
    return {"base": BASE, "rows": rows, "negative_controls_not_credited": negatives,
            "source_sha256": hashes, "kernel_checked": False, "historical_replay": False,
            "meaning_checked": False}


def code(report):
    modules = sorted({r["module"] for r in report["rows"]} |
                     {"tests/h62/item2/audit-language/WitnessAccounting.lean"})
    imports = []
    for path in modules:
        parts = Path(path).with_suffix("").parts
        if any("«" in part or "»" in part for part in parts):
            raise ValueError("unsupported module quoting")
        imports.append("import " + ".".join(part if re.fullmatch(r"[A-Za-z_]\w*", part)
                                             else "«" + part + "»" for part in parts))
    commands = ["#audit_witness " + r["witness"] + " for " + r["target"] for r in report["rows"]]
    return "\n".join(imports + [""] + commands) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witness", action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--index", type=Path, required=True)
    args = parser.parse_args()
    for path in (args.output, args.index):
        if path.resolve().is_relative_to(ROOT) or path.exists() or path.is_symlink():
            raise ValueError("output must be new and outside checkout")
    report = plan(args.witness)
    generated = code(report)
    report["generated_sha256"] = hashlib.sha256(generated.encode()).hexdigest()
    report["planner_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    with contextlib.ExitStack() as stack:
        output = stack.enter_context(args.output.open("x"))
        index = stack.enter_context(args.index.open("x"))
        output.write(generated)
        index.write(json.dumps(report, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"planned_associations": len(report["rows"]),
                      "negative_controls_not_credited": len(report["negative_controls_not_credited"]),
                      "kernel_checked": False}))


if __name__ == "__main__":
    main()
