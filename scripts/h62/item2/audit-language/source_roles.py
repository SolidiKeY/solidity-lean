#!/usr/bin/env python3
"""Guard against dropping hypotheses when historical ownership cannot be replayed.

Fresh source-role inventory using the existing classifier and frozen scanner.
All candidates remain in scope; no historical owners, feasibility certificates,
Lean telescope membership or historical acceptance are inferred.
"""
import argparse
import collections
import json
from pathlib import Path
from census import mask, sha
from classify import DECL, classify_row, declaration_index, frozen_sources
from source_only import generate as source_census


def generate():
    census = source_census()
    sources = frozen_sources()
    for path, meta in census["sources"].items():
        if sha(sources[path].encode()) != meta["sha256"]:
            raise ValueError("frozen source mismatch: " + path)
    histories = {}
    for path in census["sources"]:
        text = sources[path]
        clean = mask(text)
        lines = text.splitlines()
        histories[path] = [
            {"kind": m[1], "line": clean.count("\n", 0, m.start(1)) + 1,
             "source": lines[clean.count("\n", 0, m.start(1))].strip()}
            for m in DECL.finditer(clean) if m[1] in ("include", "omit", "open")]
    symbols, tails = declaration_index(sources)
    used, rows, errors = {}, [], []
    for row in census["declarations"]:
        try:
            result = classify_row(row, symbols, tails, used)
        except (ValueError, RecursionError) as error:
            result = {"source_id": row["id"], "path": row["path"],
                      "signature_sha256": row["signature_sha256"],
                      "in_scope": True, "exclusion": None,
                      "witness_status": "not-established-by-classification",
                      "error": str(error)}
            errors.append({"source_id": row["id"], "error": str(error)})
        result["source_signature"] = row["source_signature"]
        result["section_variables"] = row["section_variables"]
        result["owner"] = None
        result["owner_status"] = "UNVERIFIABLE-historical-snapshot"
        result["source_directive_history"] = [
            d for d in histories[row["path"]] if d["line"] < row["line"]]
        result["directive_history_boundary"] = "Lexical history only; activation needs Lean"
        rows.append(result)
    expected = {r["id"] for r in census["declarations"]}
    actual = [r["source_id"] for r in rows]
    if len(actual) != len(set(actual)) or set(actual) != expected:
        raise ValueError("source candidate accounting mismatch")
    return {"base": census["base"], "method": "fresh-source-role-classification",
            "historical_replay": False, "historical_ownership": "UNVERIFIABLE",
            "kernel_checked": False, "certified_witnesses": 0,
            "sources": census["sources"], "definitions_used": used,
            "declarations": rows, "parse_errors": errors,
            "summary": {**census["summary"], "excluded": 0,
                        "source_parse_errors": len(errors),
                        "source_sort_resolution": dict(collections.Counter(
                            r.get("source_sort_resolution", "parse-blocked") for r in rows))}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.resolve().is_relative_to(Path(__file__).resolve().parents[4]):
        raise ValueError("bulk classification must remain outside checkout")
    if args.output.exists() or args.output.is_symlink():
        raise ValueError("refusing existing output")
    report = generate()
    payload = (json.dumps(report, sort_keys=True, ensure_ascii=False) + "\n").encode()
    with args.output.open("xb") as stream:
        stream.write(payload)
    print(json.dumps({**report["summary"], "sha256": sha(payload)}))
    return int(bool(report["parse_errors"]))


if __name__ == "__main__":
    raise SystemExit(main())
