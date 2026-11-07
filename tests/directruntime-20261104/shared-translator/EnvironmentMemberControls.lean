import Solidity.Tools.DirectRuntime
/-! Guards existing msg.value/block.timestamp environment routing against ordinary
field confusion, mismatched/missing builtin metadata and unsupported siblings. Uses
the shared executable reader and existing intrinsic environment semantics only;
model/checker observations are not source/ABI/world/native adequacy proofs. -/
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def baseNode (root magic : String) (identity : Option Int) : Json :=
  let base := Json.mkObj [("nodeType",toJson "Identifier"),("name",toJson root),
    ("typeDescriptions",Json.mkObj [("typeString",toJson root),("typeIdentifier",toJson magic)])]
  match identity with | some i => base.setObjVal! "referencedDeclaration" (toJson i) | none => base
private def cases : List (String × String × String × String × EnvKey) :=
  [("msg","sender","t_magic_message","address",.msgSender),
   ("msg","value","t_magic_message","uint256",.msgValue),
   ("block","timestamp","t_magic_block","uint256",.timestamp)]
#guard cases.all fun (root,member,magic,result,key) =>
  environmentMember? (baseNode root magic (some (-15))) member result == some key
#guard cases.all fun (root,member,magic,result,_) =>
  [(baseNode root magic none,result),(baseNode root magic (some 42),result),
   (baseNode root "t_struct$_User_$1_storage_ptr" (some (-15)),result),
   (baseNode root magic (some (-15)),"bool"),
   ((baseNode root magic (some (-15))).setObjVal! "nodeType" (toJson "Literal"),result)].all fun (base,result) =>
    (environmentMember? base member result).isNone
#guard (environmentMember? (baseNode "block" "t_magic_block" (some (-4))) "number" "uint256").isNone
#guard (environmentMember? (baseNode "tx" "t_magic_transaction" (some (-26))) "origin" "address").isNone
private def memberNode : Json := Json.mkObj [("nodeType",toJson "MemberAccess"),
  ("expression",baseNode "msg" "t_magic_message" (some (-15))),("memberName",Json.null),
  ("typeDescriptions",Json.mkObj [("typeString",toJson "uint256")])]
#guard match expressionStep (fun _ => .error "base-first") memberNode with
  | .error "base-first" => true | _ => false
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
#eval show IO Unit from do
  let packet ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/environment/EnvironmentMembers.ast.json"))
  let some source := (J.nodes packet).find? (fun j => J.str? j "name" == some "EnvironmentMembers") |
    throw (IO.userError "environment fixture missing")
  for (name,expected,reason) in [("valueSelf","proved",""),("valueCopy","proved",""),
      ("nonnegativeValue","proved",""),("wrongValue","refuted","counterexample found"),
      ("timeCopy","proved",""),("wrongTime","refuted","counterexample found"),
      ("siblingBlock","unsupported","unknown name block"),("siblingTx","unsupported","unknown name tx")] do
    let some expectedId := ((J.arrD source "nodes").find? (fun n => J.str? n "name" == some name)).bind J.id? |
      throw (IO.userError "environment source identity missing")
    for box in [false,true] do
      let nodes := (J.arrD source "nodes").map fun n => if box && J.str? n "name" == some name then
        n.setObjVal! "documentation" (Json.mkObj [("nodeType",toJson "StructuredDocumentation"),("text",toJson "@custom:key box")]) else n
      let tagged := source.setObjVal! "nodes" (toJson nodes)
      let rows ← checked (Tools.DirectRuntime.check (Json.mkObj [("contract",tagged),("function",toJson name)]))
      let rows ← checked rows.getArr?
      unless rows.size == 1 do throw (IO.userError "environment row count")
      let row := rows[0]!
      unless (row.getObjValAs? Int "sourceId").toOption == some expectedId do
        throw (IO.userError "environment source identity drift")
      unless J.str? row "status" == some expected && J.str? row "reason" == some reason &&
          J.str? row "tag" == some (if box then "box" else "diamond") do
        throw (IO.userError s!"{name} box={box}: {row}")
      IO.println s!"ENVIRONMENT_MEMBER {name} sourceId={expectedId} box={box}: {expected}"
#print axioms environmentMember?
