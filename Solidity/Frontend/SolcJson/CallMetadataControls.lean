import Solidity.Frontend.SolcJson.CallMetadata
import Solidity.Frontend.SolcJson.CallMetadataData

/-! Kernel controls from exact pinned-compiler ASTs and parsed provenance.
Spoof controls alter explicit test copies, never frozen fixture observations.
Structural metadata is not Source/native execution adequacy. -/
namespace Solidity.Frontend.CallMetadata.Controls
open Lean
open Data

def profile (fixture : Json) : Option Profile := (readProfile fixture).toOption

def summary (p : Option Profile) (ds : List Json) (node : Json) :
    Except Refusal (Bool × Nat × Int) := do
  let c ← check p ds node
  return (c.info.isStatic,c.info.site,c.info.declarationId)

theorem legacy_pure : summary (profile legacyFixture) legacyDeclarations legacyCall_id =
    .ok (true,35,8) := by rfl

theorem legacy_view : summary (profile legacyFixture) legacyDeclarations legacyCall_peek =
    .ok (true,52,15) := by rfl

theorem ordinary_mutating : summary (profile legacyFixture) legacyDeclarations legacyCall_put =
    .ok (false,69,22) := by rfl

theorem ir_pure : summary (profile viaIRFixture) viaIRDeclarations viaIRCall_id =
    .ok (true,35,8) := by rfl

theorem actual_certificate :
    (check (profile legacyFixture) legacyDeclarations legacyCall_id).isOk = true := by rfl

def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (fun e => e.1 != key))
  | _ => j

def callee : Json := ((legacyCall_id.getObjVal? "expression").toOption).getD .null

def spoofedName : Json := set legacyCall_id "expression" (set callee "memberName" (.str "put"))

theorem wrong_identity_refused : summary (profile legacyFixture) legacyDeclarations spoofedName =
    .error .name := by rfl

def spoofedPure : Json := set legacyCall_id "expression"
  (set (set callee "referencedDeclaration" (toJson (22 : Int))) "memberName" (.str "put"))

theorem purity_label_refused : summary (profile legacyFixture) legacyDeclarations spoofedPure =
    .error .mutability := by rfl

theorem duplicated_identity_refused : summary (profile legacyFixture)
    (legacyDeclarations ++ legacyDeclarations) legacyCall_id = .error .declaration := by rfl

theorem negative_site_refused : summary (profile legacyFixture) legacyDeclarations
    (set legacyCall_id "id" (toJson (-1 : Int))) = .error .site := by rfl

theorem wrong_arity_refused : summary (profile legacyFixture) legacyDeclarations
    (set legacyCall_id "arguments" (.arr #[])) = .error .arity := by rfl

theorem unvalidated_profile_refused : summary none legacyDeclarations legacyCall_id =
    .error .profile := by rfl

theorem no_static_fallback_from_spoof : keyword (profile legacyFixture)
    legacyDeclarations spoofedPure = "try" := by rfl


def withCalleeType (text : String) : Json := set legacyCall_id "expression"
  (set callee "typeDescriptions" (Json.mkObj [("typeString",.str text)]))

theorem nested_visibility_cannot_spoof_outer : summary (profile legacyFixture)
    legacyDeclarations (withCalleeType
      "function (function (uint256) pure external returns (uint256)) internal returns (uint256)") =
    .error .callShape := by rfl

theorem nested_mutability_cannot_spoof_outer : summary (profile legacyFixture)
    legacyDeclarations (withCalleeType
      "function (function (uint256) pure external returns (uint256)) external returns (uint256)") =
    .error .mutability := by rfl

theorem nested_outer_qualifiers :
    (outerQualifiers? "function (function (uint256) pure external returns (uint256)) view external returns (function () internal)").map
      (fun tokens => (tokens.contains "external",tokens.contains "view",tokens.contains "pure",tokens.contains "internal")) =
    some (true,true,false,false) := by rfl

theorem malformed_outer_type_refused : outerQualifiers? "function (uint256] pure external" = none := by rfl

theorem conflicting_nonpayable_refused : summary (profile legacyFixture)
    legacyDeclarations (set legacyCall_peek "expression"
      (set (((legacyCall_peek.getObjVal? "expression").toOption).getD .null) "typeDescriptions"
        (Json.mkObj [("typeString",.str "function (uint256) view nonpayable external returns (uint256)")]))) =
    .error .callShape := by rfl

theorem misplaced_qualifier_refused : outerQualifiers? "function view external (uint256)" = none := by rfl

theorem extra_group_refused : outerQualifiers? "function (uint256) view external ()" = none := by rfl

theorem trailing_qualifier_refused :
    outerQualifiers? "function (uint256) view external returns (uint256) payable" = none := by rfl


def namespaceReceiver : Json := set legacyCall_id "expression"
  (set callee "expression" (Json.mkObj [("nodeType",.str "Identifier"),
    ("name",.str "L"),("typeDescriptions",Json.mkObj [("typeString",.str "type(library L)")])]))

theorem library_namespace_not_static_call : summary (profile legacyFixture)
    legacyDeclarations namespaceReceiver = .error .receiver := by rfl

/-- info: 'Solidity.Frontend.CallMetadata.Controls.library_namespace_not_static_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms library_namespace_not_static_call

/-- info: 'Solidity.Frontend.CallMetadata.Controls.legacy_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms legacy_pure
/-- info: 'Solidity.Frontend.CallMetadata.Controls.legacy_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms legacy_view
/-- info: 'Solidity.Frontend.CallMetadata.Controls.ordinary_mutating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ordinary_mutating
/-- info: 'Solidity.Frontend.CallMetadata.Controls.ir_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ir_pure
/-- info: 'Solidity.Frontend.CallMetadata.Controls.actual_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms actual_certificate
/-- info: 'Solidity.Frontend.CallMetadata.Controls.wrong_identity_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_identity_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.purity_label_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms purity_label_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.duplicated_identity_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms duplicated_identity_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.negative_site_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms negative_site_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.wrong_arity_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_arity_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.unvalidated_profile_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unvalidated_profile_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.no_static_fallback_from_spoof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_static_fallback_from_spoof
/-- info: 'Solidity.Frontend.CallMetadata.Controls.nested_visibility_cannot_spoof_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_visibility_cannot_spoof_outer
/-- info: 'Solidity.Frontend.CallMetadata.Controls.nested_mutability_cannot_spoof_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_mutability_cannot_spoof_outer
/-- info: 'Solidity.Frontend.CallMetadata.Controls.nested_outer_qualifiers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms nested_outer_qualifiers
/-- info: 'Solidity.Frontend.CallMetadata.Controls.malformed_outer_type_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms malformed_outer_type_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.conflicting_nonpayable_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms conflicting_nonpayable_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.misplaced_qualifier_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms misplaced_qualifier_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.extra_group_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms extra_group_refused
/-- info: 'Solidity.Frontend.CallMetadata.Controls.trailing_qualifier_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms trailing_qualifier_refused
end Solidity.Frontend.CallMetadata.Controls
