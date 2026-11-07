import Solidity.Tools.DirectRuntime
/-! Guards H90 address-local marker and tuple/environment regressions. Only
explicitly nonpayable local type nodes are accepted; payable/missing metadata,
parameters and state remain refused. Trusted model/checker observations are not
source/ABI/native adequacy or complete address-support proofs. -/
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst.Shared
private def addressNode (mutability : Option String) : Json :=
  let base := Json.mkObj [("nodeType",toJson "ElementaryTypeName"),("name",toJson "address")]
  match mutability with | some m => base.setObjVal! "stateMutability" (toJson m) | none => base
#guard match localValueTypeName (addressNode (some "nonpayable")) with
  | .ok (.prim .uint,.named "address") => true | _ => false
#guard [none,some "payable",some "view",some ""].all fun m =>
  match localValueTypeName (addressNode m) with
  | .error "compact verifier: unsupported type address" => true | _ => false
#guard !(typeName (addressNode (some "nonpayable"))).isOk
#guard match elabTyW ({ vars := [] } : Contract) (.named "address") with
  | .ok (.prim .uint,rows) => rows == addressRows | _ => false
/-- The builtin bridge must not turn a user declaration or missing identity into an environment read. -/
private def senderNode (identity : Option Int) (magic : String) : Json :=
  let base := Json.mkObj [("nodeType",toJson "Identifier"),("name",toJson "msg"),
    ("typeDescriptions",Json.mkObj [("typeString",toJson "msg"),("typeIdentifier",toJson magic)])]
  let base := match identity with | some i => base.setObjVal! "referencedDeclaration" (toJson i) | none => base
  Json.mkObj [("nodeType",toJson "MemberAccess"),("memberName",toJson "sender"),
    ("expression",base),("typeDescriptions",Json.mkObj [("typeString",toJson "address")])]
#guard match expression (senderNode (some (-15)) "t_magic_message") with
  | .ok (.env .msgSender) => true | _ => false
#guard [(none,"t_magic_message"),(some 42,"t_magic_message"),(some (-15),"t_struct$_Message_$1_storage_ptr")].all fun (identity,magic) =>
  match expression (senderNode identity magic) with
  | .ok (.field (.name "msg") "sender") => true | _ => false
#guard match expressionStep (fun _ => .error "base-first")
    ((senderNode (some (-15)) "t_magic_message").setObjVal! "memberName" Json.null) with
  | .error "base-first" => true | _ => false
private def checked {α : Type} : Except String α → IO α
  | .ok a => pure a | .error e => throw (IO.userError e)
#eval show IO Unit from do
  let packet ← checked (Json.parse (← IO.FS.readFile "tests/directruntime-20261104/shared-translator/artifacts/address/AddressLocals.ast.json"))
  let some source := (J.nodes packet).find? (fun j => J.str? j "name" == some "AddressLocals") |
    throw (IO.userError "address fixture missing")
  for (name,expected) in [("zero","proved"),("sender","proved"),("repeated","proved"),
      ("swap","proved"),("shadow","proved"),("wrong","refuted"),
      ("parameter","unsupported"),("payableLocal","unsupported")] do
    for box in [false,true] do
      let nodes := (J.arrD source "nodes").map fun n => if box && J.str? n "name" == some name then
        n.setObjVal! "documentation" (Json.mkObj [("nodeType",toJson "StructuredDocumentation"),("text",toJson "@custom:key box")]) else n
      let tagged := source.setObjVal! "nodes" (toJson nodes)
      let rows ← checked (Tools.DirectRuntime.check (Json.mkObj [("contract",tagged),("function",toJson name)]))
      let rows ← checked rows.getArr?
      unless rows.size == 1 do throw (IO.userError "address row count")
      let row := rows[0]!
      unless (row.getObjValAs? String "status").toOption == some expected &&
          (row.getObjValAs? String "tag").toOption == some (if box then "box" else "diamond") do
        throw (IO.userError s!"{name} box={box}: {row}")
      if expected == "unsupported" then
        unless (row.getObjValAs? String "reason").toOption == some "compact verifier: unsupported type address" do
          throw (IO.userError s!"address refusal changed {row}")
      IO.println s!"ADDRESS_LOCAL {name} box={box}: {expected}"
  let some state := (J.nodes packet).find? (fun j => J.str? j "name" == some "AddressStateRefusal") |
    throw (IO.userError "address state fixture missing")
  unless !(contract executableReader state).isOk do throw (IO.userError "address state silently admitted")
#print axioms localValueTypeName_of_address
