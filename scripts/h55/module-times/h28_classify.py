#!/usr/bin/env python3
"""Guard regression: H28 fixture rows lose driver and mutation-phase context.

Static references are candidate evidence, not authenticated executable recipes.
"""
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
GROUPS = {
    "tests/h28-sol/statement-grammar/": "statement-grammar",
    "tests/h28-sol/mutation-testing/oracles/": "mutation-testing",
    "tests/h28-sol/non-vacuity/lean/": "non-vacuity",
}


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get("rows"), list):
        raise ValueError("invalid census")
    root = pathlib.Path(root)
    references = {}
    manifest_dir = root / "tests/h28-sol/mutation-testing/manifests"
    for file in sorted(manifest_dir.glob("*.json")):
        manifest_bytes = file.read_bytes()
        data = json.loads(manifest_bytes)
        if not isinstance(data, dict) or not isinstance(data.get("cases"), list):
            raise ValueError("invalid mutation manifest")
        for case in data["cases"]:
            if not isinstance(case, dict):
                raise ValueError("invalid mutation case")
            for role in ("oracle", "witness", "regression", "equivalence"):
                if isinstance(case.get(role), str):
                    references.setdefault(case[role], []).append({"manifest": str(file.relative_to(root)),
                        "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
                        "case_id": case.get("id"), "kind": case.get("kind"), "role": role})
    out, seen = [], set()
    for row in manifest["rows"]:
        if not isinstance(row, dict) or not isinstance(row.get("path"), str):
            raise ValueError("invalid census row")
        path = row["path"]
        matches = [group for prefix, group in GROUPS.items() if path.startswith(prefix)]
        if not matches:
            continue
        if (len(matches) != 1 or path in seen or not path.endswith(".lean") or "\\" in path
                or any(part in ("", ".", "..") for part in path.split("/"))):
            raise ValueError("invalid selected path")
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError("invalid source")
        raw = source.read_bytes()
        if hashlib.sha256(raw).hexdigest() != row.get("sha256"):
            raise ValueError("source differs from supplied census")
        group = matches[0]
        imports = [{"line": n, "text": line} for n, line in enumerate(raw.decode("utf-8").splitlines(), 1)
                   if re.match(r"^import\s", line)]
        record = {"candidate": row, "group": group, "lexical_import_lines": imports,
                  "status": "static-driver-reference-not-acceptance"}
        if group == "statement-grammar":
            record.update(driver="tests/h28-sol/statement-grammar/runtime.py", mode="generic per-file gate/diag; individual invocation unverified",
                          expected="driver requires successful gate/diag and resource checks", effects="runtime evidence, server/container actions; details per invocation")
        elif group == "non-vacuity":
            prefix = "tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/"
            if not path.startswith(prefix) or "/" in path[len(prefix):]:
                raise ValueError("non-vacuity file is outside harness discovery")
            record.update(driver="tests/h28-sol/non-vacuity/kernel.py", module="Solidity.Assurance.NonVacuityH28." + source.stem,
                          expected="successful private Lean checks when selected; not observed", effects="private oleans, index and symlink mirror")
        else:
            record.update(driver="tests/h28-sol/mutation-testing/tools/runner.py", implementation="tests/h28-sol/mutation-testing/tools/engine.py", references=references.get(path, []),
                          expected="case and baseline/mutant phase dependent; unresolved per invocation", effects="disposable trees, patch and evidence")
            if not record["references"]:
                raise ValueError("mutation file lacks manifest reference")
        out.append(record)
    return out


def main():
    if len(sys.argv) != 2:
        print("usage: h28_classify.py CENSUS.json", file=sys.stderr)
        return 2
    try:
        raw = pathlib.Path(sys.argv[1]).read_bytes()
        result = classify(ROOT, json.loads(raw))
        print(json.dumps({"status": "partial-static-classification-not-acceptance",
                          "coverage": "unverified-subsets-accepted", "census_sha256": hashlib.sha256(raw).hexdigest(),
                          "rows": result}, indent=2, sort_keys=True))
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"classification unavailable: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
