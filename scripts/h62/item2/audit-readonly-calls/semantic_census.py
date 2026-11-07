#!/usr/bin/env python3
"""Expand hidden top-level premises of the 339 syntactically binder-free types.

This is inspection, not a witness generator. Preserve the original Expr hash;
reduce its outer telescope without changing transparency or proof budgets.
Proof axiom dependencies and exact identities are emitted by Lean. Canonical
records remain bound to successful query/log/toolchain receipts.
"""
import argparse
import importlib.util
import json
from pathlib import Path

spec = importlib.util.spec_from_file_location("exporter", Path(__file__).with_name("export_signatures.py"))
exporter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exporter)
BASE = exporter.census.BASE

HELPER = r'''namespace Solidity.H62.ReadonlyAudit.SemanticMetadata
open Lean Elab Command Meta
private def exportSemantic (source moduleName : Lean.Name) (privateName : Bool) : CommandElabM Unit := do
  let full := if privateName then mkPrivateNameCore moduleName source else source
  let env ← getEnv
  let some info := env.find? full | throwError "missing declaration {full}"
  unless getOriginalConstKind? env full == some .thm do throwError "expected theorem {full}"
  let some index := env.getModuleIdxFor? full | throwError "missing module {full}"
  unless env.header.moduleNames[index.toNat]! == moduleName do throwError "wrong module {full}"
  let inspected ← liftTermElabM do
    forallTelescopeReducing info.type fun vars result => do
      let binders ← vars.mapM fun var => do
        let decl ← var.fvarId!.getDecl
        let prop ← isProp decl.type
        let pretty ← ppExpr decl.type
        return Json.mkObj [
          ("name", toJson decl.userName.toString),
          ("is_proposition", toJson prop),
          ("type_expr", toJson (toString (repr decl.type))),
          ("pretty_type", toJson pretty.pretty)]
      let head := match result.getAppFn with
        | .const name _ => name
        | _ => .anonymous
      let pretty ← ppExpr result
      return Json.mkObj [
        ("reducing_binders", Json.arr binders),
        ("result_head", toJson head.toString),
        ("result_expr", toJson (toString (repr result))),
        ("pretty_result", toJson pretty.pretty)]
  let axioms ← collectAxioms full
  let rawHead := match info.type.getAppFn with
    | .const name _ => name
    | _ => .anonymous
  let record := Json.mkObj [
    ("source_name", toJson source.toString),
    ("kernel_name", toJson full.toString),
    ("module", toJson moduleName.toString),
    ("raw_type_expr", toJson (toString (repr info.type))),
    ("raw_head", toJson rawHead.toString),
    ("axioms", toJson (axioms.toList.map Lean.Name.toString)),
    ("inspection", inspected)]
  logInfo m!"H62-SEMANTIC {record.compress}"
'''


def selected(data, exact):
    by_name = {r["source_name"]: r for r in exact["declarations"]}
    return [r for r in data["declarations"] if not by_name[r["source_name"]]["forall_binders"]]


def generate(data, exact):
    imports = ["import Lean"] + ["import "+r["file"][:-5].replace("/", ".") for r in data["modules"]]
    lines = imports + ["", HELPER]
    for row in selected(data, exact):
        private = "true" if "private" in row["visibility"] else "false"
        lines.append("run_cmd exportSemantic `"+row["source_name"]+" `"+row["file"][:-5].replace("/", ".")+" "+private)
    return "\n".join(lines+["end Solidity.H62.ReadonlyAudit.SemanticMetadata", ""])


def collect(log, data, exact):
    if any(exporter.re.search(r":\d+:\d+: error(?:\(|:)", line) for line in log.splitlines() if not line.startswith("H62-SEMANTIC ")):
        raise ValueError("Lean error in semantic log")
    wanted = {r["source_name"]: r for r in selected(data, exact)}
    types = {r["source_name"]: r for r in exact["declarations"]}
    found = {}
    for line in log.splitlines():
        if not line.startswith("H62-SEMANTIC "):
            continue
        item = json.loads(line.removeprefix("H62-SEMANTIC "))
        name = item["source_name"]
        if name not in wanted or name in found:
            raise ValueError("unknown/duplicate semantic declaration: "+name)
        original = types[name]
        if any(item[k] != original[k] for k in ["kernel_name", "module", "raw_type_expr"]):
            raise ValueError("semantic statement identity/type mismatch: "+name)
        item["signature_sha256"] = wanted[name]["signature_sha256"]
        item["raw_type_sha256"] = original["raw_type_sha256"]
        item["owner"] = wanted[name]["owner"]
        found[name] = item
    if set(found) != set(wanted):
        raise ValueError("missing semantic declarations: "+str(sorted(set(wanted)-set(found))))
    return dict(schema=1, base=BASE, declaration_count=len(found),
                boundary="Reduced telescope and axiom inspection only; no automatic witness or no-premise classification",
                declarations=[found[r["source_name"]] for r in selected(data, exact)])


def verify(query, log, receipt_path, data, exact):
    return exporter.verify_receipt(query, log, receipt_path, data, query_text=generate(data, exact))


def verify_artifact(semantic, data, exact):
    exporter.verify_artifact(exact, data)
    p = semantic["provenance"]
    q, log, receipt_path = (Path(p[k]) for k in ["query", "log", "receipt"])
    receipt = verify(q, log, receipt_path, data, exact)
    canonical = collect(log.read_text(), data, exact)
    canonical["provenance"] = {k: receipt[k] for k in ["command", "gate_exit", "log_sha256", "input_source_sha256", "lean_version", "lake_version", "lean_binary_sha256", "lake_binary_sha256", "toolchain_file_sha256"]}
    canonical["provenance"].update(query=str(q.resolve()), log=str(log.resolve()), receipt=str(receipt_path.resolve()), exact=str(Path(p["exact"]).resolve()))
    if semantic != canonical:
        raise ValueError("semantic artifact differs from canonical verified log")
    if json.loads(Path(p["exact"]).read_text()) != exact:
        raise ValueError("semantic exact export mismatch")
    return canonical


def classification(item, policy):
    standard = {"propext", "Classical.choice", "Quot.sound"}
    if set(policy["allowed_axioms"]) != standard:
        raise ValueError("semantic axiom policy must retain the standard three")
    if not set(item["axioms"]).issubset(standard):
        raise ValueError("unsupported proof axiom dependencies: "+item["source_name"])
    inspection = item["inspection"]
    binders = inspection["reducing_binders"]
    controls = {r["source_name"]: r for r in policy["intentional_controls"]}
    name = item["source_name"]
    if name in controls:
        pin = controls[name]
        if pin["raw_type_sha256"] != item["raw_type_sha256"] or pin["signature_sha256"] != item["signature_sha256"]:
            raise ValueError("intentional-control type pin mismatch: "+name)
        if item["raw_head"] not in ["Not", "Ne"] or len(binders) != 1 or not binders[0]["is_proposition"] or inspection["result_head"] != "False":
            raise ValueError("intentional-control implication shape mismatch: "+name)
        return "checked-joint-impossibility"
    if not binders and inspection["result_head"] in policy["rigid_logical_result_heads"]:
        return "no-top-level-input-hypotheses"
    return "pending"


def attach(result, semantic, exact, policy):
    verify_artifact(semantic, result, exact)
    if policy["base"] != BASE:
        raise ValueError("semantic policy base mismatch")
    pins = policy["intentional_controls"]
    if len(pins) != len({r["source_name"] for r in pins}):
        raise ValueError("duplicate intentional-control pin")
    by_name = {r["source_name"]: r for r in result["declarations"]}
    inspected_names = {r["source_name"] for r in semantic["declarations"]}
    if not {r["source_name"] for r in pins}.issubset(inspected_names):
        raise ValueError("uncovered intentional-control pin")
    for item in semantic["declarations"]:
        row = by_name[item["source_name"]]
        if row["signature_sha256"] != item["signature_sha256"]:
            raise ValueError("semantic signature drift")
        kind = classification(item, policy)
        row["semantic_inspection"] = {
            "raw_type_sha256": item["raw_type_sha256"], "raw_head": item["raw_head"],
            "reduced_binder_count": len(item["inspection"]["reducing_binders"]),
            "result_head": item["inspection"]["result_head"], "axioms": item["axioms"],
            "audit_status": kind}
        if kind != "pending":
            if row["witness_status"] != "pending":
                raise ValueError("semantic outcome overlaps explicit coverage: "+row["source_name"])
            row["witness_status"] = kind
            row["proof"] = item["kernel_name"]
            row["premise_assessment"] = ("H69 intentional refutation: existing checked proof establishes the sole refused premise implies False; not a positive witness" if kind == "checked-joint-impossibility" else
                "No top-level input hypotheses after reducing inspection to a rigid logical result. No claim about nested semantic guards, global representation feasibility, or compiler success.")
    result["semantic_provenance"] = semantic["provenance"]
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--exact", type=Path, required=True)
    p.add_argument("--query", type=Path, required=True)
    p.add_argument("--log", type=Path)
    p.add_argument("--receipt", type=Path)
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    data = exporter.census.census()
    exact = json.loads(a.exact.read_text())
    exporter.verify_artifact(exact, data)
    if not a.log:
        a.query.write_text(generate(data, exact))
        print("SEMANTIC_QUERY_GENERATED declarations="+str(len(selected(data, exact))))
        return
    assert a.receipt and a.output
    receipt = verify(a.query, a.log, a.receipt, data, exact)
    result = collect(a.log.read_text(), data, exact)
    result["provenance"] = {k: receipt[k] for k in ["command", "gate_exit", "log_sha256", "input_source_sha256", "lean_version", "lake_version", "lean_binary_sha256", "lake_binary_sha256", "toolchain_file_sha256"]}
    result["provenance"].update(query=str(a.query.resolve()), log=str(a.log.resolve()), receipt=str(a.receipt.resolve()), exact=str(a.exact.resolve()))
    a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
    print("SEMANTIC_EXPORT_PASS declarations="+str(result["declaration_count"]))


if __name__ == "__main__":
    main()
