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

#check environmentMember?
#print axioms environmentMember?
#check environmentMember?_guard
#print axioms environmentMember?_guard
#check localValueTypeName_of_address
#print axioms localValueTypeName_of_address
#check localTypeName_of_narrow
#print axioms localTypeName_of_narrow
#check localTypeName_of_fixedBytes
#print axioms localTypeName_of_fixedBytes
