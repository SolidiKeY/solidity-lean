#!/usr/bin/env python3
"""Generate a bounded, exact-name Lean type census. No witness inference.

Imports frozen interfaces without modifying registrations. Public declarations
are looked up directly; private names use Lean.mkPrivateNameCore and are checked
against the environment module index. Raw Expr representations accompany pretty
types. Each declaration gets a separate command under the original budget.
Generated bulk query and JSON records belong outside Git.
"""
import argparse
import importlib.util
import json
import hashlib
import re
from pathlib import Path

spec = importlib.util.spec_from_file_location("census", Path(__file__).with_name("census.py"))
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

HELPER = r'''namespace Solidity.H62.ReadonlyAudit.Metadata
open Lean Elab Command Meta
private def exportOne (source moduleName : Lean.Name) (privateName : Bool) : CommandElabM Unit := do
  let full := if privateName then mkPrivateNameCore moduleName source else source
  let env ← getEnv
  let some info := env.find? full | throwError "missing frozen declaration {full}"
  unless getOriginalConstKind? env full == some .thm do throwError "expected theorem {full}"
  let some index := env.getModuleIdxFor? full | throwError "missing module identity {full}"
  let actualModule := env.header.moduleNames[index.toNat]!
  unless actualModule == moduleName do throwError "wrong module {actualModule} for {full}"
  if info.type.hasMVar || info.type.hasFVar then throwError "nonclosed type {full}"
  let binders ← liftTermElabM do
    forallTelescope info.type fun vars _ => vars.mapM fun var => do
      let decl ← var.fvarId!.getDecl
      let prop ← isProp decl.type
      let head := match decl.type.getAppFn with
        | .const name _ => name
        | _ => .anonymous
      let isStruct := (getStructureInfo? env head).isSome
      return Json.mkObj [
        ("name", toJson decl.userName.toString),
        ("binder_info", toJson (toString (repr decl.binderInfo))),
        ("type_expr", toJson (toString (repr decl.type))),
        ("is_proposition", toJson prop),
        ("head_constant", toJson head.toString),
        ("is_structure_type", toJson isStruct)]
  let pretty ← liftTermElabM do
    withOptions (fun opts => (opts.setBool `pp.fullNames true).setBool `pp.universes true) do
      ppExpr info.type
  let data := Json.mkObj [
    ("source_name", toJson source.toString),
    ("kernel_name", toJson full.toString),
    ("module", toJson actualModule.toString),
    ("level_parameters", toJson (info.levelParams.map Lean.Name.toString)),
    ("pretty_type", toJson pretty.pretty),
    ("forall_binders", Json.arr binders),
    ("raw_type_expr", toJson (toString (repr info.type)))]
  logInfo m!"H62-SIGNATURE {data.compress}"
'''


def generate(data):
    imports = ["import Lean"] + ["import " + p["file"][:-5].replace("/", ".") for p in data["modules"]]
    lines = imports + ["", HELPER]
    for row in data["declarations"]:
        source = row["source_name"]
        module = row["file"][:-5].replace("/", ".")
        private = "true" if "private" in row["visibility"] else "false"
        lines.append(f"run_cmd exportOne `{source} `{module} {private}")
    lines += ["end Solidity.H62.ReadonlyAudit.Metadata", ""]
    return "\n".join(lines)


def collect(log, data):
    if any(re.search(r":\d+:\d+: error(?:\(|:)", line) for line in log.splitlines() if not line.startswith("H62-SIGNATURE ")):
        raise ValueError("Lean error in signature log")
    wanted = {r["source_name"]: r for r in data["declarations"]}
    found = {}
    for line in log.splitlines():
        if line.startswith("H62-SIGNATURE "):
            item = json.loads(line.removeprefix("H62-SIGNATURE "))
            name = item["source_name"]
            if name not in wanted or name in found:
                raise ValueError("unknown/duplicate exported declaration: " + name)
            row = wanted[name]
            module = row["file"][:-5].replace("/", ".")
            if item["module"] != module:
                raise ValueError("module identity mismatch: " + name)
            expected = ("_private."+module+".0." if "private" in row["visibility"] else "") + name
            if item["kernel_name"] != expected:
                raise ValueError("kernel identity mismatch: " + name)
            if not item["raw_type_expr"] or not item["pretty_type"]:
                raise ValueError("missing exported type: " + name)
            item["raw_type_sha256"] = census.sha(item["raw_type_expr"])
            item["signature_sha256"] = row["signature_sha256"]
            item["owner"] = row["owner"]
            found[name] = item
    if found.keys() != wanted.keys():
        raise ValueError("uncovered exported declarations: " + str(sorted(wanted.keys()-found.keys())))
    return dict(schema=1, base=census.BASE, boundary="Elaborated frozen types and private names only; no hypothesis witness claim",
        declaration_count=len(found), declarations=[found[r["source_name"]] for r in data["declarations"]])


def verify_receipt(query, log, receipt, data, query_text=None):
    r = json.loads(receipt.read_text())
    if r.get("gate_exit") != 0 or r.get("status") != "pass" or r.get("stop_reason") is not None:
        raise ValueError("signature export Lean gate did not pass")
    expected_command = ["lake", "env", "lean", "-j1", "--tstack=131072", "--root=/workspace", str(query.resolve())]
    if r["command"] != expected_command or Path(r["log"]).resolve() != log.resolve():
        raise ValueError("signature export command/log mismatch")
    if r["log_sha256"] != hashlib.sha256(log.read_bytes()).hexdigest():
        raise ValueError("signature export log hash mismatch")
    actual_query = hashlib.sha256(query.read_bytes()).hexdigest()
    expected_query = hashlib.sha256((generate(data) if query_text is None else query_text).encode()).hexdigest()
    if actual_query != expected_query or r["input_source_sha256"].get(str(query.resolve())) != actual_query:
        raise ValueError("signature export query hash mismatch")
    tool = Path("/workspace/.setup/tools/lean-4.24.0-linux/bin")
    for name in ["lean", "lake"]:
        if r[name+"_binary_sha256"] != hashlib.sha256((tool/name).read_bytes()).hexdigest():
            raise ValueError("signature export tool binary mismatch")
    if r["toolchain_file_sha256"] != hashlib.sha256((census.ROOT/"lean-toolchain").read_bytes()).hexdigest():
        raise ValueError("signature export toolchain file mismatch")
    expected_version = (census.ROOT/"lean-toolchain").read_text().strip().split(":")[-1].removeprefix("v")
    if "version "+expected_version not in r["lean_version"]:
        raise ValueError("signature export version mismatch")
    return r


def verify_artifact(exported, data):
    provenance = exported["provenance"]
    query, log, receipt_path = (Path(provenance[k]) for k in ["query", "log", "receipt"])
    receipt = verify_receipt(query, log, receipt_path, data)
    canonical = collect(log.read_text(), data)
    canonical["provenance"] = {key: receipt[key] for key in ["command", "gate_exit", "log_sha256", "input_source_sha256", "lean_version", "lake_version", "lean_binary_sha256", "lake_binary_sha256", "toolchain_file_sha256"]}
    canonical["provenance"].update(query=str(query.resolve()), log=str(log.resolve()), receipt=str(receipt_path.resolve()))
    if exported != canonical:
        raise ValueError("elaborated artifact differs from verified log records/provenance")
    return canonical


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--query", type=Path)
    p.add_argument("--log", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--receipt", type=Path)
    a = p.parse_args()
    data = census.census()
    if a.query and not a.log:
        a.query.write_text(generate(data))
        print("SIGNATURE_QUERY_GENERATED declarations="+str(data["theorem_count"]))
    if a.log:
        assert a.output and a.query and a.receipt
        receipt = verify_receipt(a.query, a.log, a.receipt, data)
        result = collect(a.log.read_text(), data)
        result["provenance"] = {key: receipt[key] for key in ["command", "gate_exit", "log_sha256", "input_source_sha256", "lean_version", "lake_version", "lean_binary_sha256", "lake_binary_sha256", "toolchain_file_sha256"]}
        result["provenance"].update(query=str(a.query.resolve()), log=str(a.log.resolve()), receipt=str(a.receipt.resolve()))
        a.output.write_text(json.dumps(result, indent=2, ensure_ascii=False)+"\n")
        print("ELABORATED_CENSUS_PASS declarations="+str(result["declaration_count"]))


if __name__ == "__main__":
    main()
