import Solidity.Frontend.SolcJson.CallMetadata

/-! Universal structural guarantees of accepted call metadata. These do not
prove AST membership, compiler authentication or execution/frame adequacy. -/
namespace Solidity.Frontend.CallMetadata
open Lean (Json)

theorem checked_call_exact {p : Option Profile} {ds : List Json} {call : Json}
    (checked : Checked p ds call) : checked.info.call = call := by
  exact inspect_call_exact checked.accepted

theorem checked_static_declaration {p : Option Profile} {ds : List Json} {call : Json}
    (checked : Checked p ds call) (static : checked.info.isStatic = true) :
    (checked.info.declaration.getObjValAs? String "stateMutability").toOption = some "pure" ∨
    (checked.info.declaration.getObjValAs? String "stateMutability").toOption = some "view" := by
  exact checked.info.static_declaration static

theorem checked_static_target {p : Option Profile} {ds : List Json} {call : Json}
    (checked : Checked p ds call) (static : checked.info.isStatic = true) :
    staticTarget? checked.info.profile = some true :=
  checked.info.static_target static


/-- info: 'Solidity.Frontend.CallMetadata.checked_call_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_call_exact
/-- info: 'Solidity.Frontend.CallMetadata.checked_static_declaration' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_static_declaration
/-- info: 'Solidity.Frontend.CallMetadata.checked_static_target' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_static_target
end Solidity.Frontend.CallMetadata
