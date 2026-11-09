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


PROJECTION_TEMPLATE = r'''
namespace Solidity.H62.BytecodeSelection.ProjectionAudit
open Lean Meta Elab Command

-- Guard inferring projection structure/type arguments from spelling alone.
structure RegistryBase where
  flag : Bool
structure RegistryChild extends RegistryBase where
  count : Nat
class RegistryClass where
  flag : Bool
def registryValue : Nat := 0

private def registryIndex : CommandElabM (Std.HashMap String (List Lean.Name)) := do
  let mut index : Std.HashMap String (List Lean.Name) := {}
  for (name, _) in (← getEnv).constants.toList do
    index := index.insert name.toString (name :: index.getD name.toString [])
  return index

private def constantSnapshot (info : ConstantInfo) : Json :=
  Json.mkObj [("name",toJson info.name.toString),("type_expr",toJson (reprStr info.type)),
    ("level_params",toJson (info.levelParams.map Lean.Name.toString))]

private def observeProjection (index : Std.HashMap String (List Lean.Name))
    (target expectedType expectedModule : String) : CommandElabM Json := do
  let names := index.getD target []
  unless names.length == 1 do throwError "projection audit: missing or ambiguous name"
  let name := names.head!
  let info ← getConstInfo name
  unless reprStr info.type == expectedType do throwError "projection audit: recorded type differs"
  let env ← getEnv
  let some moduleIndex := env.getModuleIdxFor? name
    | throwError "projection audit: target module unavailable"
  let moduleName := env.header.moduleNames[moduleIndex.toNat]!.toString
  unless moduleName == expectedModule do throwError "projection audit: recorded module differs"
  let mut status := "no_registered_projection"
  let mut registry : Json := .null
  let mut constructorData : Json := .null
  let mut inductiveData : Json := .null
  let mut structureInfo : Json := .null
  if let some projection := env.getProjectionFnInfo? name then
    registry := Json.mkObj [("ctor_name",toJson projection.ctorName.toString),
      ("num_params",toJson projection.numParams),("field_index",toJson projection.i),
      ("from_class",toJson projection.fromClass)]
    status := "constructor_metadata_unavailable"
    if let some (.ctorInfo value) := env.find? projection.ctorName then
      constructorData := Json.mkObj [("name",toJson value.name.toString),
        ("type_expr",toJson (reprStr value.type)),
        ("level_params",toJson (value.levelParams.map Lean.Name.toString)),
        ("inductive",toJson value.induct.toString),("num_params",toJson value.numParams),
        ("num_fields",toJson value.numFields),("constructor_index",toJson value.cidx)]
      status := "inductive_metadata_unavailable"
      if let some owner@(.inductInfo _) := env.find? value.induct then
        inductiveData := constantSnapshot owner
        status := "structure_metadata_unavailable"
        if let some structureData := getStructureInfo? env value.induct then
          structureInfo := Json.mkObj [("name",toJson value.induct.toString),
            ("projections",toJson (structureData.fieldInfo.map fun field => field.projFn.toString)),
            ("parents",toJson (structureData.parentInfo.map fun parent => Json.mkObj [
              ("structure",toJson parent.structName.toString),
              ("projection",toJson parent.projFn.toString),("subobject",toJson parent.subobject)]))]
          status := "registered_projection_observed"
  return Json.mkObj [("fingerprint",toJson ("FINGERPRINT" : String)),
    ("name",toJson name.toString),("module",toJson moduleName),("private",toJson (isPrivateName name)),
    ("type_expr",toJson (reprStr info.type)),("level_params",toJson (info.levelParams.map Lean.Name.toString)),
    ("metadata_status",toJson status),("registry",registry),("constructor",constructorData),
    ("inductive",inductiveData),("structure",structureInfo)]

run_cmd do
  let env ← getEnv
  let some base := env.getProjectionFnInfo? ``RegistryBase.flag
    | throwError "projection control: missing direct field"
  unless base.ctorName == ``RegistryBase.mk && base.numParams == 0 && base.i == 0 do
    throwError "projection control: wrong direct field metadata"
  let some parent := env.getProjectionFnInfo? ``RegistryChild.toRegistryBase
    | throwError "projection control: missing parent projection"
  unless parent.ctorName == ``RegistryChild.mk do
    throwError "projection control: wrong parent constructor"
  let some classField := env.getProjectionFnInfo? ``RegistryClass.flag
    | throwError "projection control: missing class field"
  unless classField.fromClass do throwError "projection control: class flag lost"
  unless (env.getProjectionFnInfo? ``registryValue).isNone do
    throwError "projection control: nonprojection falsely tagged"

/-- error: projection audit: missing or ambiguous name -/
#guard_msgs in
run_cmd do
  let _ ← observeProjection (← registryIndex) "missing.kernel.name" "" ""
  pure ()
/-- error: projection audit: recorded type differs -/
#guard_msgs in
run_cmd do
  let _ ← observeProjection (← registryIndex)
    "Solidity.H62.BytecodeSelection.ProjectionAudit.RegistryBase.flag" "corrupted type" ""
  pure ()

/-- error: projection audit: recorded module differs -/
#guard_msgs in
run_cmd do
  let index ← registryIndex
  let target : String := FIRST_TARGET
  let name := (index.getD target []).head!
  let info ← getConstInfo name
  let _ ← observeProjection index target (reprStr info.type) "wrong.recorded.module"
  pure ()

run_cmd do
  let targets : List (String × String × String) := [TARGETS]
  let index ← registryIndex
  for (name, expectedType, expectedModule) in targets do
    let record ← observeProjection index name expectedType expectedModule
    Lean.Elab.Command.liftCoreM <| Lean.Core.liftIOCore <|
      IO.println ("H62_PROJECTION_JSON " ++ record.compress)
  Lean.Elab.Command.liftCoreM <| Lean.Core.liftIOCore <|
    IO.println ("H62_PROJECTION_DONE " ++ (Json.mkObj [
      ("fingerprint",toJson ("FINGERPRINT" : String)),("count",toJson targets.length)]).compress)
end Solidity.H62.BytecodeSelection.ProjectionAudit
'''


def projection_inspection_source(repo, rows):
    """Supplement the existing inspector with actual registry/constructor data.

    Old TEMPLATE/FIELDS and source generation remain unchanged. Registry facts
    are observations, not source ownership or instantiated inherited proofs.
    """
    import kernel_metadata as metadata
    from exact_domains import _frozen_scope
    metadata.validate_rows(rows)
    selected=sorted((row for row in rows if row["is_projection"]),key=lambda row:row["name"])
    if not selected:
        raise ValueError("no supplied projection records")
    modules=sorted({row["module"] for row in selected})
    frozen_map,sources=_frozen_scope(repo,modules)
    pins={"base":BASE,"targets":{row["name"]:metadata.observed_type(row) for row in selected},
        "modules":modules,"source_sha256":sources,
        "frozen_map_sha256":hashlib.sha256(frozen_map).hexdigest(),
        "projection_template_sha256":hashlib.sha256(PROJECTION_TEMPLATE.encode()).hexdigest()}
    fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()).hexdigest()
    entries=["("+",".join(json.dumps(value,ensure_ascii=False) for value in (row["name"],row["type_expr"],row["module"]))+")" for row in selected]
    program="import Lean\n"+"".join("import "+module+"\n" for module in modules)
    program+="/-! Guard projection metadata from name-prefix guesses and stale field types. Registry data is uninstantiated; no source or proof acceptance. -/\n"
    program+=PROJECTION_TEMPLATE.replace("FINGERPRINT",fingerprint).replace("TARGETS",",\n".join(entries)).replace("FIRST_TARGET",json.dumps(selected[0]["name"],ensure_ascii=False))
    pins.update(fingerprint=fingerprint,generated_lean_sha256=hashlib.sha256(program.encode()).hexdigest(),
                kernel_accepted=False,source_correspondence_established=False,inherited_instantiation_accepted=False)
    return program,pins
