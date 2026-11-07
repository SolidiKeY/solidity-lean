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

#check localValueTypeName_of_address
#print axioms localValueTypeName_of_address
#check localTypeName_of_narrow
#print axioms localTypeName_of_narrow
#check localTypeName_of_fixedBytes
#print axioms localTypeName_of_fixedBytes
