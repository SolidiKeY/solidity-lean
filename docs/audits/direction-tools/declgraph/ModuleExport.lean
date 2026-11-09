import Lean

open Lean

/- Native per-module serialization. ModuleData preserves constants that the
   merged Environment constant-name map collapses. Declaration ranges come
   directly from declRangeExt, not the editor's aliased reference index.
   Reads cache only; no project source commands or proof bodies are elaborated. -/

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

-- Exact pinned Lean 4.24 Environment.finalizeImport preference relation.
-- Lean/Environment.lean:2086 (private subsumesInfo); theorem proof irrelevance
-- permits repeated theorem names with equal types and differing proof bodies.
def subsumes (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.type == b.type && a.levelParams == b.levelParams &&
  match a,b with
  | .thmInfo x,.thmInfo y => x.all == y.all
  | .thmInfo x,.axiomInfo y => x.all == [y.name] && !y.isUnsafe
  | .axiomInfo x,.axiomInfo y => x.isUnsafe == y.isUnsafe
  | _,_ => false

def rangeJson (r : DeclarationRange) : Json :=
  toJson #[r.pos.line - 1,r.charUtf16,r.endPos.line - 1,r.endCharUtf16]

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [modules,output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let names := (← IO.FS.lines modules).filter (· != "")
    let chosen : NameSet := names.foldl (fun s n => s.insert n.toName) {}
    let env ← importModules (names.map fun n => {module := n.toName}) {} 0 (loadExts := true)
    let out ← IO.FS.Handle.mk output .write
    let mut occurrences : NameMap (Array (Nat × ConstantInfo)) := {}
    let mut count := 0
    let mut selectedCount := 0
    for i in [:env.header.moduleData.size] do
      let m := env.header.moduleNames[i]!
      let data := env.header.moduleData[i]!
      let selected := chosen.contains m
      out.putStrLn <| (Json.mkObj [("record",toJson "module"),("module",toJson m.toString),
        ("selected",toJson selected),("is_module",toJson data.isModule),("imports",toJson (data.imports.map (·.module.toString))),
        ("names",toJson (data.constNames.map Name.toString))]).compress
      let mut ranges : NameMap DeclarationRanges := {}
      if selected then
        for (n,r) in declRangeExt.getModuleEntries env i (level := .private) do ranges := ranges.insert n r
      for ci in data.constants do
        occurrences := occurrences.insert ci.name ((occurrences.find? ci.name).getD #[] |>.push (i,ci))
        count := count + 1
        if selected then selectedCount := selectedCount + 1
        let rs := ranges.find? ci.name
        out.putStrLn <| (Json.mkObj [("record",toJson "constant"),("module",toJson m.toString),
          ("name",toJson ci.name.toString),("kind",toJson (constantKind ci)),
          ("refs",toJson ((nativeRefs ci).map Name.toString)),
          ("range",rs.map (fun r => rangeJson r.range) |>.getD Json.null),
          ("selection",rs.map (fun r => rangeJson r.selectionRange) |>.getD Json.null)]).compress
    let mut collisions := 0
    for (n,versions) in occurrences do
      if versions.size < 2 then continue
      collisions := collisions + 1
      let typedVersions : Array (Nat × ConstantInfo) := versions
      let matrix : Array (Array Bool) := typedVersions.map fun a => typedVersions.map fun b => subsumes a.2 b.2
      out.putStrLn <| (Json.mkObj [("record",toJson "collision"),("name",toJson n.toString),
        ("modules",toJson (typedVersions.map fun entry => env.header.moduleNames[entry.1]!.toString)),
        ("subsumes",toJson matrix)]).compress
    IO.println s!"MODULE_CONSTANT_EXPORT_PASS {count} {selectedCount} {collisions}"
    return 0
  | _ =>
    IO.eprintln "usage: ModuleExport.lean MODULES OUTPUT"
    return 2
