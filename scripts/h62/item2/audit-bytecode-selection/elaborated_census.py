#!/usr/bin/env python3
"""Generate an off-Git Lean inspection program for frozen mapped modules.

Run the emitted program against source-checked imports. It records kernel type
expressions and pretty types for named/generated theorems, structure projections,
and all remaining constants, with non-proof bodies, without proving new statements.
The program imports Lean only in this external audit; the core is unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from census import BASE, mapped_paths

TEMPLATE = r'''
open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let selected : List Name := [MODULES]
  let manifestFingerprint : String := "FINGERPRINT"
  let selectedSet := selected.foldl (fun result name => result.insert name) ({} : NameSet)
  for moduleName in selected do
    unless env.header.moduleNames.contains moduleName do
      throwError "selected module not loaded"
  let mut recordedModules : List Name := []
  let moduleOf (name : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? name
    env.header.moduleNames[idx.toNat]?
  let inScope (name : Name) : Bool :=
    (moduleOf name).any selectedSet.contains
  let constants := (env.constants.toList.filter (fun pair => inScope pair.1)).mergeSort (fun a b => Name.quickLt a.1 b.1)
  let mut fields : NameSet := {}
  for (name, _) in constants do
    if inScope name then
      if let some structureInfo := getStructureInfo? env name then
        for field in structureInfo.fieldInfo do
          fields := fields.insert field.projFn
  for (name, info) in constants do
    if inScope name then
      let moduleName := (moduleOf name).get!
      let moduleString := moduleName.toString
      let isTheorem := wasOriginallyTheorem env name
      let isProjection := fields.contains name
      let isInterface := decide ((moduleString.splitOn "Interface").length > 1 ∨ (moduleString.splitOn "Premises").length > 1)
      do
        let (pretty, isProof, predicateValued, binders) ← liftTermElabM do
          let pretty ← ppExpr info.type
          let isProof ← isProp info.type
          let (predicateValued, binders) ← forallTelescope info.type fun xs result => do
            let result ← whnf result
            let predicateValued := result == .sort .zero
            let mut entries : Array Json := #[]
            for x in xs do
              let localDecl ← x.fvarId!.getDecl
              let binderType ← ppExpr localDecl.type
              let proofBinder ← isProp localDecl.type
              entries := entries.push <| Json.mkObj [
                ("name", toJson localDecl.userName.toString),
                ("binder_info", toJson (reprStr localDecl.binderInfo)),
                ("type", toJson binderType.pretty),
                ("proof_binder", toJson proofBinder),
                ("head_constant", toJson (localDecl.type.getAppFn.constName?.map Name.toString))]
            pure (predicateValued, entries)
          pure (pretty.pretty, isProof, predicateValued, binders)
        let parents : Array Json := match getStructureInfo? env name with
          | none => #[]
          | some structureInfo => structureInfo.parentInfo.map fun (parent : StructureParentInfo) =>
            Json.mkObj [("structure", toJson parent.structName.toString),
              ("projection", toJson parent.projFn.toString),
              ("subobject", toJson parent.subobject)]
        let ranges ← findDeclarationRanges? name
        let rangeJson := ranges.map fun r => Json.mkObj [
          ("start_line", toJson r.range.pos.line),
          ("end_line", toJson r.range.endPos.line),
          ("selection_line", toJson r.selectionRange.pos.line),
          ("selection_column", toJson r.selectionRange.pos.column),
          ("selection_end_line", toJson r.selectionRange.endPos.line),
          ("selection_end_column", toJson r.selectionRange.endPos.column),
          ("position_units", toJson ("one-based lines; zero-based Unicode codepoint columns" : String))]
        let body := if isTheorem || isProof then none else info.value? (allowOpaque := true)
        let record := Json.mkObj [
          ("manifest_sha256", toJson manifestFingerprint),
          ("name", toJson name.toString),
          ("user_name", toJson (privateToUserName name).toString),
          ("private", toJson (isPrivateName name)),
          ("original_kind", toJson ((getOriginalConstKind? env name).map reprStr)),
          ("declaration_range", toJson rangeJson),
          ("module", toJson moduleString),
          ("kind", toJson (if isProjection then "field" else if isTheorem then "theorem" else "constant")),
          ("interface_or_premises_module", toJson isInterface),
          ("predicate_valued", toJson predicateValued),
          ("body_expr", toJson (body.map reprStr)),
          ("body_status", toJson (if isTheorem || isProof then "proof body intentionally omitted; declaration retained" else if body.isSome then "available expression; not unfolded dependency closure" else "no available value")),
          ("is_theorem", toJson isTheorem),
          ("is_projection", toJson isProjection),
          ("proof_type", toJson isProof),
          ("type_expr", toJson (reprStr info.type)),
          ("type", toJson pretty),
          ("level_params", toJson (info.levelParams.map Name.toString)),
          ("binders", toJson binders),
          ("parents", toJson parents)]
        recordedModules := moduleName :: recordedModules
        liftIO <| IO.println ("H62_CENSUS_JSON " ++ record.compress)
  let counts := selected.map fun moduleName =>
    (moduleName.toString, toJson ((recordedModules.filter (fun name => name == moduleName)).length))
  let complete := Json.mkObj [("manifest_sha256", toJson manifestFingerprint), ("counts", Json.mkObj counts)]
  liftIO <| IO.println ("H62_CENSUS_DONE " ++ complete.compress)
'''


def manifest_sha256(pins):
    data = {key: pins[key] for key in ["base", "modules", "source_sha256", "inspection_template_sha256"]}
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()).hexdigest()


def inspection_source(modules, fingerprint):
    """Reconstruct the exact external inspector, not an acceptance certificate."""
    imports = "".join("import " + module + "\n" for module in modules)
    return "import Lean\n" + imports + TEMPLATE.replace("MODULES", ", ".join("`" + module for module in modules)).replace("FINGERPRINT", fingerprint)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--module", action="append", help="limit to a mapped module; default all core mapped modules")
    args = p.parse_args()
    repo = args.repo.resolve()
    paths, _ = mapped_paths(repo)
    core = {path[:-5].replace("/", "."): path for path in paths if path.startswith("Solidity/")}
    modules = sorted(args.module or core)
    assert set(modules) <= core.keys(), "requested module outside frozen mapped core"
    pins = {}
    for module in modules:
        path = core[module]
        data = (repo / path).read_bytes()
        original = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo)
        if data != original:
            raise ValueError("frozen source differs: " + path)
        pins[path] = hashlib.sha256(data).hexdigest()
    pins_data = {"base": BASE, "modules": modules, "source_sha256": pins, "inspection_template_sha256": hashlib.sha256(TEMPLATE.encode()).hexdigest()}
    fingerprint = manifest_sha256(pins_data)
    source = inspection_source(modules, fingerprint)
    args.output.write_text(source)
    args.output.with_suffix(".pins.json").write_text(json.dumps(dict(pins_data, manifest_sha256=fingerprint, inspection_sha256=hashlib.sha256(source.encode()).hexdigest()), indent=2) + "\n")
    print(json.dumps({"modules": len(modules), "inspection": str(args.output)}))


if __name__ == "__main__":
    main()
