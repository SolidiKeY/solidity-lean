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


def refine_known_domains(report):
    """Apply existing frozen definition refinements without inventing witnesses."""
    from refine_remaining import fact, refine
    if report["parse_errors"]:
        raise ValueError("refinement requires all source rows parsed")
    sources = frozen_sources()
    facts = {
        "constructors": fact(sources, "Solidity/AST.lean", "inductive PrimTy where\n  | bool\n  | uint\n  | int", "PrimTy-constructors"),
        "denote": fact(sources, "Solidity/Semantics.lean", "def PrimTy.Denote : PrimTy → Type\n  | .bool => Bool\n  | .uint => {n : Int // PrimTy.uint.inRange n = true}\n  | .int => {n : Int // PrimTy.int.inRange n = true}", "PrimTy-Denote-branches"),
        "address": fact(sources, "Solidity/Semantics/ContractWorld.lean", "abbrev Address := { w : Word // w.1 < (2 : Int) ^ 160 }", "ContractWorld-Address-refinement"),
        "world-word": fact(sources, "Solidity/Semantics/ContractWorld.lean", "abbrev Word := Semantics.Word", "ContractWorld-Word-alias"),
        "semantics-word": fact(sources, "Solidity/Semantics.lean", "abbrev Word := PrimTy.uint.Denote", "Semantics-Word-alias"),
        "fx": fact(sources, "Solidity/Language/FixedPoint.lean", "def Fx (t : FxTy) : Type := {v : Int // t.inRange v = true}", "FixedPoint-Fx-refinement")}
    symbols, tails = declaration_index(sources)
    result, changes = refine(report, sources, symbols, tails, facts)
    for before, after in zip(report["declarations"], result["declarations"]):
        for key in ("source_id", "source_signature", "signature_sha256", "section_variables", "owner", "owner_status", "in_scope", "exclusion"):
            if before[key] != after[key]:
                raise ValueError("refinement changed frozen source identity or claim boundary")
    if len(result["declarations"]) != len(report["declarations"]):
        raise ValueError("refinement changed candidate count")
    result["refinement"] = {"facts": facts, "changes": changes,
                            "boundary": "source refinements only; every range constraint remains a joint-witness obligation"}
    result["summary"]["binder_refinements"] = len(changes)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--refine", action="store_true", help="reuse frozen PrimTy/Address/Fx refinements; no witness credit")
    args = parser.parse_args()
    if args.output.resolve().is_relative_to(Path(__file__).resolve().parents[4]):
        raise ValueError("bulk classification must remain outside checkout")
    if args.output.exists() or args.output.is_symlink():
        raise ValueError("refusing existing output")
    report = generate()
    if args.refine:
        report = refine_known_domains(report)
    payload = (json.dumps(report, sort_keys=True, ensure_ascii=False) + "\n").encode()
    with args.output.open("xb") as stream:
        stream.write(payload)
    print(json.dumps({**report["summary"], "sha256": sha(payload)}))
    return int(bool(report["parse_errors"]))


if __name__ == "__main__":
    raise SystemExit(main())
