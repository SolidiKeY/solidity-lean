#!/usr/bin/env python3
"""Consolidate SAVED H78 exports without Lean or changes to their evidence.

Usage: h78-inventory.py EVIDENCE OUTPUT_DIRECTORY
All original exported names are retained, including hygienic/private candidates.
Visibility and attributes were not captured: no public/private exemption follows.
Type hashes compare raw compiler records, not definitional/semantic equivalence.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path
import re
import sys


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def record_hash(row):
    return digest_bytes(json.dumps(row, sort_keys=True, ensure_ascii=False,
                                  separators=(",", ":")).encode("utf-8"))


def application(text):
    """Split one printed constructor application, preserving raw argument text.

    No eval or Lean parser is used. Balanced parentheses/brackets, quoted strings
    and escaped identifier guillemets are preserved as indivisible arguments.
    """
    text = text.strip()
    def split(s):
        stack = []
        quoted = escaped = False
        start = None
        parts = []
        for i, c in enumerate(s):
            if start is None and not c.isspace():
                start = i
            if quoted:
                if escaped:
                    escaped = False
                elif c == "\\":
                    escaped = True
                elif c == '"':
                    quoted = False
            elif c == '"' and (not stack or stack[-1] != "«"):
                quoted = True
            elif c == "«":
                stack.append(c)
            elif stack and stack[-1] == "«":
                if c == "»":
                    stack.pop()
            elif c in "([":
                stack.append(c)
            elif c in ")]":
                if not stack or stack.pop() != {')': '(', ']': '['}[c]:
                    raise ValueError("unbalanced printed expression")
            elif c.isspace() and not stack and start is not None:
                parts.append(s[start:i])
                start = None
        if stack or quoted:
            raise ValueError("unterminated printed expression")
        if start is not None:
            parts.append(s[start:])
        return parts
    parts = split(text)
    if len(parts) == 1 and text.startswith("(") and text.endswith(")"):
        return split(text[1:-1].strip())
    return parts


def telescope(text):
    """Decode only the leading forallE chain; retain domains/result verbatim."""
    binders = []
    while True:
        parts = application(text)
        if not parts or parts[0] != "Lean.Expr.forallE":
            return {"binders": binders, "result_repr": text.strip()}
        if len(parts) != 5:
            raise ValueError("forallE requires exactly four printed arguments")
        kind = parts[4].strip("() ")
        if kind not in ["Lean.BinderInfo." + k for k in
                        ["default", "implicit", "strictImplicit", "instImplicit"]]:
            raise ValueError("unrecognized binder kind: " + kind)
        binders.append({"position": len(binders) + 1,
                        "name_repr": parts[1], "domain_repr": parts[2],
                        "binder_kind": kind})
        text = parts[3]


def family(name):
    tail = name.rsplit(".", 1)[-1]
    if tail in {"noConfusion", "noConfusionType", "rec", "recOn", "casesOn",
                "brecOn", "below", "toCtorIdx", "ctorIdx"}:
        return tail
    if re.fullmatch(r"match_\d+", tail):
        return "match_N"
    if re.fullmatch(r"eq_\d+", tail) or tail == "eq_def":
        return "equation_name_candidate"
    return "other_original_name"


def unique_rows(rows, label):
    result = {r["name"]: r for r in rows}
    if len(result) != len(rows):
        raise ValueError("duplicate exported names: " + label)
    return result


def generate(evidence, out):
    filenames = ["frozen-interfaces-old.json", "api-partial-old.json",
                 "api-partial-new.json", "census-base.json"]
    blobs = {name: (evidence / name).read_bytes() for name in filenames}
    ledger, old, new, census = [json.loads(blobs[name]) for name in filenames]
    if not ledger["complete_old_inventory"] or census["assigned_count"] != 199:
        raise ValueError("complete 199-module old fingerprint inventory required")
    if ledger["base"] != census["base"]:
        raise ValueError("different frozen bases")
    if set(old["requested_modules"]) != set(new["requested_modules"]):
        raise ValueError("partial old/new requested module sets differ")
    modules = set(new["requested_modules"])
    original = unique_rows(ledger["rows"], "full old ledger")
    old_rows = unique_rows(old["rows"], "partial old export")
    new_rows = unique_rows(new["rows"], "partial new export")
    assigned = {r["module"] for r in census["files"]}
    if len(assigned) != 199 or ledger["entries"] != len(original):
        raise ValueError("inconsistent complete inventory counts")
    if not modules.issubset(assigned):
        raise ValueError("unexpected requested module")
    for capture in [old, new]:
        if len(set(capture["requested_modules"])) != len(capture["requested_modules"]):
            raise ValueError("duplicate requested module")
        if capture["assigned_module_count"] != 199:
            raise ValueError("inconsistent assigned module count")
        if capture["complete"] != (modules == assigned):
            raise ValueError("inconsistent complete/partial label")
        if any(r["module"] not in modules for r in capture["rows"]):
            raise ValueError("exported record outside requested module set")
    for name, row in old_rows.items():
        if record_hash(row) != original[name]["sha256"]:
            raise ValueError("partial old export differs from frozen fingerprint: " + name)
    rows = []
    for name, row in sorted(original.items()):
        target = new_rows.get(name)
        status = ("not_target_checked" if row["module"] not in modules else
                  "absent_in_partial_target" if target is None else
                  "identical_raw_record" if record_hash(target) == row["sha256"] else
                  "changed_raw_record")
        rows.append({**row, "name_family_hint": family(name), "target_status": status,
                     "target_record_sha256": record_hash(target) if target else None,
                     "visibility": "not_captured", "attributes": "not_captured"})
    detail = []
    for name in ["Solidity.Source.Syn.noConfusion", "Solidity.Source.Syn.noConfusionType"]:
        for role, records in [("old", old_rows), ("new", new_rows)]:
            row = records[name]
            detail.append({"role": role, **row, "record_sha256": record_hash(row),
                           "telescope": telescope(row["type_repr"]),
                           "visibility": "not_captured", "attributes": "not_captured"})
    inventory = {"schema": "schema-v1", "base": census["base"],
                 "source": "saved exports only; no Lean invocation",
                 "input_sha256": {n: digest_bytes(b) for n, b in blobs.items()},
                 "all_original_names_retained": True, "old_entries": len(rows),
                 "assigned_modules": 199, "target_checked_modules": sorted(modules),
                 "target_complete": new["complete"],
                 "status_counts": dict(sorted(Counter(r["target_status"] for r in rows).items())),
                 "name_family_counts": dict(sorted(Counter(r["name_family_hint"] for r in rows).items())),
                 "new_names": [new_rows[n] for n in sorted(new_rows.keys() - original.keys())],
                 "rows": rows,
                 "boundary": "Full old name/fingerprint superset, partial target only. Visibility/attributes absent in original capture: no complete public API compatibility verdict. Family hints never exclude a name. Raw differences do not establish semantic inequivalence; raw identity does not establish value/metadata/trust equality."}
    out.mkdir(parents=True, exist_ok=True)
    for filename, data in [("inventory.json", inventory), ("syn-exact-signatures.json", detail)]:
        (out / filename).write_text(json.dumps(data, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"old_entries": len(rows), "target_checked_modules": len(modules),
                      "status_counts": inventory["status_counts"], "installed_shims": [],
                      "visibility": "not_captured", "new_lean_runs": 0}, sort_keys=True))


if __name__ == "__main__":
    generate(Path(sys.argv[1]), Path(sys.argv[2]))
