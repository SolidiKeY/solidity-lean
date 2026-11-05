"""Direct finite compiler/resolver comparison over existing intrinsic fixtures."""
if not __debug__:
    raise SystemExit("Optimized Python disables required assertions; rerun without -O/PYTHONOPTIMIZE.")

import json
import re

PREFIX = "Solidity.Frontend.QualifiedUnits.DifferentialControls."


def lean_queries(matrix):
    def literal(value):
        return json.dumps(value, ensure_ascii=False)

    def strings(values):
        return "[" + ", ".join(literal(value) for value in values) + "]"

    text = """import Lean
import Solidity.Frontend.QualifiedUnits.DifferentialControls
import Solidity.Frontend.QualifiedUnits.SignatureResolution
open Lean Solidity.Source Solidity.Frontend.QualifiedUnits
namespace QualifiedUnitsQueryAudit
def symbolJson : Sym → Json
  | .decl i => Json.mkObj [("kind", toJson "decl"), ("unit", toJson i.unit), ("index", toJson i.idx)]
  | .unit u => Json.mkObj [("kind", toJson "unit"), ("unit", toJson u)]
def reason : Failure → String
  | .missing => "missing"
  | .ambiguous => "ambiguous"
  | .invalidScope => "invalidScope"
  | .localShadow _ => "localShadow"
def answerJson : Except Failure (List Sym) → Json
  | .ok symbols => Json.mkObj [("status", toJson "ok"), ("symbols", Json.arr (symbols.map symbolJson).toArray)]
  | .error error => Json.mkObj [("status", toJson "error"), ("reason", toJson (reason error)),
      ("local_index", match error with | .localShadow i => toJson i | _ => Json.null)]
def queryJson (caseId reference : String) (answer : Except Failure (List Sym)) : Json :=
  Json.mkObj [("id", toJson caseId), ("reference", toJson reference), ("answer", answerJson answer)]
"""
    calls = []
    for row in matrix["rows"]:
        parts = row["input"].split()
        assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", parts[0])
        program = PREFIX + parts[0]
        if len(parts) == 2:
            assert parts[0] == "shadowInput" and parts[1] in (".priv", ".internal")
            program = "(" + program + " " + parts[1] + ")"
        else:
            assert len(parts) == 1
        scope = row["scope"]
        scope_text = "none" if scope is None else "(some ⟨" + literal(scope["unit"]) + ", " + str(scope["index"]) + "⟩)"
        for query in row["queries"]:
            assert query["path"]
            path = "⟨" + literal(query["path"][0]) + ", " + strings(query["path"][1:]) + "⟩"
            call = "Solidity.Frontend.QualifiedUnits.SignatureResolution.resolve " + program + " [] \"A.sol\" " + scope_text + " " + strings(row["locals"]) + " " + path
            calls.append("queryJson " + literal(row["id"]) + " " + literal(query["reference"]) + " (" + call + ")")
    text += '#eval IO.println ("RESOLVER_QUERY_REPORT " ++ (Json.arr #[' + ",\n".join(calls) + ']).compress)\n'
    text += "end QualifiedUnitsQueryAudit\n"
    return text


def compare_queries(observed, matrix, compiler):
    by_query = {(row["id"], row["reference"]): row["answer"] for row in observed}
    expected_count = sum(len(row["queries"]) for row in matrix["rows"])
    assert len(by_query) == len(observed) == expected_count, "query inventory drift"
    by_compiler = {row["id"]: row for row in compiler["rows"]}
    results = []
    for row in matrix["rows"]:
        external = by_compiler[row["id"]]
        assert external["passed"] and external["accepted"] == row["accepted"]
        refs = {ref["expected"]["name"]: ref for ref in external["references"]}
        graph = {(entry["unit"], entry["index"]) for entry in external["declaration_graph"]}
        queries = []
        for query in row["queries"]:
            answer = by_query[(row["id"], query["reference"])]
            if row["accepted"]:
                expected = {("decl", item["unit"], item["index"]) for item in query["expected_candidates"]}
                assert all((unit, index) in graph for _, unit, index in expected), "candidate absent from compiler graph"
                actual_refs = {("decl", target["unit"], target["index"]) for target in refs[query["reference"]]["targets"] if target.get("unit") is not None}
                assert actual_refs and actual_refs <= expected, "compiler-selected identity absent from expected candidate set"
                actual = {(symbol["kind"], symbol["unit"], symbol.get("index")) for symbol in answer.get("symbols", [])}
                matched = answer["status"] == "ok" and actual == expected
                detail = {"expected": [list(item) for item in sorted(expected)], "actual": [list(item) for item in sorted(actual)], "missing": [list(item) for item in sorted(expected - actual)], "extra": [list(item) for item in sorted(actual - expected)]}
            else:
                matched = answer["status"] == "error" and answer["reason"] == query["expected_refusal"]
                if query["expected_refusal"] == "localShadow":
                    matched = matched and answer["local_index"] == row["locals"].index(query["path"][0])
                detail = {"expected_refusal": query["expected_refusal"], "actual": answer}
            queries.append({"reference": query["reference"], "matched": matched, **detail})
        results.append({"id": row["id"], "matched": all(q["matched"] for q in queries), "queries": queries, "recorded_gap": row["resolution_gap"]})
    return {"rows": results, "compiler_agreement": all(row["matched"] for row in results),
            "mismatches": [row["id"] for row in results if not row["matched"]]}
