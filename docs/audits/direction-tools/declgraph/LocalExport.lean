import Lean
open Lean
namespace DeclgraphLocal

/- Serialize each requested leaf in its own imported environment. This permits
   mutually incompatible global CLI names such as main without merging them.
   Only native constant data/ranges are exported; no editor-reference edges.
-/
def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def nativeRefs (ci : ConstantInfo) : Array Name := Id.run do
  let mut refs := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then refs := refs ++ value.getUsedConstants
  match ci with
  | .inductInfo v => refs := refs ++ v.all.toArray ++ v.ctors.toArray
  | .ctorInfo v => refs := refs.push v.induct
  | .recInfo v =>
    refs := refs ++ v.all.toArray
    for rule in v.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return refs

def rangeJson (r : DeclarationRange) : Json :=
  toJson #[r.pos.line - 1,r.charUtf16,r.endPos.line - 1,r.endCharUtf16]


unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [modules,output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let names := (← IO.FS.lines modules).filter (· != "")
    let out ← IO.FS.Handle.mk output .write
    let mut count := 0
    for name in names do
      let moduleName := name.toName
      let env ← importModules #[{module := moduleName}] {} 0 (loadExts := true)
      let mut own : Option Nat := none
      let moduleNames := env.header.moduleNames
      for i in [:moduleNames.size] do
        if moduleNames[i]! == moduleName then own := some i
      let some i := own | throw (IO.userError s!"missing imported root {moduleName}")
      let data := env.header.moduleData[i]!
      if data.isModule then throw (IO.userError "only legacy root contexts are supported")
      out.putStrLn <| (Json.mkObj [("record",toJson "module"),("module",toJson name),
        ("selected",toJson true),("is_module",toJson data.isModule),
        ("imports",toJson (data.imports.map (·.module.toString))),
        ("names",toJson (data.constNames.map Name.toString))]).compress
      let mut ranges : NameMap DeclarationRanges := {}
      for (n,r) in declRangeExt.getModuleEntries env i (level := .private) do ranges := ranges.insert n r
      for ci in data.constants do
        count := count + 1
        let rs := ranges.find? ci.name
        out.putStrLn <| (Json.mkObj [("record",toJson "constant"),("module",toJson name),
          ("name",toJson ci.name.toString),("kind",toJson (constantKind ci)),
          ("refs",toJson ((nativeRefs ci).map Name.toString)),
          ("range",rs.map (fun r => rangeJson r.range) |>.getD Json.null),
          ("selection",rs.map (fun r => rangeJson r.selectionRange) |>.getD Json.null)]).compress
    IO.println s!"LOCAL_MODULE_EXPORT_PASS {names.size} {count}"
    return 0
  | _ =>
    IO.eprintln "usage: LocalExport.lean MODULES OUTPUT"
    return 2

end DeclgraphLocal

unsafe def main := DeclgraphLocal.main
