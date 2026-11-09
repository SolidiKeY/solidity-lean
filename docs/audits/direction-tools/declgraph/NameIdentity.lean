import Lean
open Lean
namespace DeclgraphNames
/- Verify that graph display-name keys are injective on the actual native
   constant/reference universe plus structurally keyed check observations. -/
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


partial def decodeName (j : Json) : Except String Name := do
  if j == Json.str "anonymous" then return .anonymous
  match (← j.getArr?).toList with
  | [tag,parent,value] =>
    match (← tag.getStr?) with
    | "str" => return .str (← decodeName parent) (← value.getStr?)
    | "num" => return .num (← decodeName parent) (← value.getNat?)
    | _ => throw "Unknown native name tag"
  | _ => throw "Invalid native name key"

structure Census where
  seen : Std.HashMap String Name := {}
  occurrences : Nat := 0
  collisions : Array Json := #[]

def add (s : Census) (n : Name) : Census := Id.run do
  let printed := n.toString
  let mut result := {s with occurrences := s.occurrences + 1}
  if let some old := s.seen[printed]? then
    if old != n then
      result := {result with collisions := result.collisions.push (Json.mkObj [("printed",toJson printed),("old_repr",toJson (reprStr old)),("new_repr",toJson (reprStr n))])}
  else result := {result with seen := result.seen.insert printed n}
  return result

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [modules,observations,output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let names := (← IO.FS.lines modules).filter (· != "")
    if names.isEmpty then throw (IO.userError "Empty module universe")
    let env ← importModules (names.map fun n => {module := n.toName}) {} 0 (loadExts := true)
    let mut census : Census := {}
    let mut constants := 0
    for data in env.header.moduleData do
      for ci in data.constants do
        constants := constants + 1
        census := add census ci.name
        for n in nativeRefs ci do census := add census n
    let input ← IO.ofExcept <| Json.parse (← IO.FS.readFile observations)
    let rows ← IO.ofExcept input.getArr?
    for row in rows do
      let n ← IO.ofExcept <| decodeName (← IO.ofExcept (row.getObjVal? "name_key"))
      let display ← IO.ofExcept <| row.getObjValAs? String "name"
      unless n.toString == display do throw (IO.userError "Observation display/key mismatch")
      census := add census n
    let nameOutput ← IO.FS.Handle.mk (output ++ ".names.jsonl") .write
    let sortedNames := (census.seen.toArray.map Prod.fst).qsort (· < ·)
    for printed in sortedNames do nameOutput.putStrLn (toJson printed).compress
    IO.FS.writeFile output <| (Json.mkObj [("loaded_modules",toJson env.header.moduleData.size),("constant_records",toJson constants),("name_occurrences",toJson census.occurrences),("unique_printed_names",toJson census.seen.size),("observation_rows",toJson rows.size),("collisions",toJson census.collisions)]).pretty ++ "\n"
    IO.println s!"NAME_IDENTITY_CHECK_PASS {constants} {census.seen.size} {census.collisions.size}"
    return if census.collisions.isEmpty then 0 else 1
  | _ => IO.eprintln "usage: NameIdentity.lean MODULES OBSERVATIONS OUTPUT"; return 2
end DeclgraphNames
unsafe def main := DeclgraphNames.main
