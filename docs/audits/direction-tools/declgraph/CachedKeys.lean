import Lean
open Lean
namespace DeclgraphCachedKeys
/- Read explicit cache artifacts without executing project initializers. Query
   strings only select candidate records; native structural keys stay explicit.
   Regions are retained until every output has been written. -/
def nameKey : Name → Json
  | .anonymous => toJson "anonymous"
  | .str parent value => Json.arr #[toJson "str",nameKey parent,toJson value]
  | .num parent value => Json.arr #[toJson "num",nameKey parent,toJson value]

def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"


unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [query,output] =>
    let input ← IO.ofExcept <| Json.parse (← IO.FS.readFile query)
    let requests ← IO.ofExcept input.getArr?
    if requests.isEmpty then throw (IO.userError "Empty cache-key query")
    let out ← IO.FS.Handle.mk output .write
    let mut regions : Array CompactedRegion := #[]
    let mut found := 0
    let mut missing := 0
    for request in requests do
      let moduleName ← IO.ofExcept <| request.getObjValAs? String "module"
      let fileNames ← IO.ofExcept <| request.getObjValAs? (Array String) "artifacts"
      let requested ← IO.ofExcept <| request.getObjValAs? (Array String) "names"
      if fileNames.isEmpty || requested.isEmpty then throw (IO.userError "Empty module query")
      let wanted := requested.foldl (fun set name => set.insert name) ({} : Std.HashSet String)
      if fileNames.size != 1 then throw (IO.userError "Legacy key lookup requires exactly the main artifact")
      if wanted.size != requested.size then throw (IO.userError "Duplicate requested name")
      let parts ← readModuleDataParts (fileNames.map System.FilePath.mk)
      let mut seen : Std.HashSet String := {}
      for (data,region) in parts do
        regions := regions.push region
        if data.isModule then throw (IO.userError "Split module needs explicit import-level resolution")
        for ci in data.constants do
          let printed := ci.name.toString
          if wanted.contains printed then
            seen := seen.insert printed
            found := found + 1
            out.putStrLn <| (Json.mkObj [("record",toJson "key"),("module",toJson moduleName),
              ("name",toJson printed),("name_key",nameKey ci.name),("constant_kind",toJson (constantKind ci))]).compress
      let absent := requested.filter fun name => !seen.contains name
      missing := missing + absent.size
      out.putStrLn <| (Json.mkObj [("record",toJson "module"),("module",toJson moduleName),
        ("requested_names",toJson wanted.size),("missing_names",toJson absent)]).compress
    IO.println s!"CACHED_KEYS_PASS {requests.size} {found} {missing} {regions.size}"
    return 0
  | _ => IO.eprintln "usage: CachedKeys.lean QUERY OUTPUT"; return 2
end DeclgraphCachedKeys
unsafe def main := DeclgraphCachedKeys.main
