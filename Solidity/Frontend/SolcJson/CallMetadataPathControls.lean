import Solidity.Frontend.SolcJson.CallMetadataPath
import Solidity.Frontend.SolcJson.CallMetadataData

namespace Solidity.Frontend.CallMetadata.PathControls
open Lean (Json)
open Data

def legacy_id : Located ((legacyFixture.getObjVal? "ast").toOption.getD Json.null) :=
  ⟨[.field "nodes", .index 2, .field "nodes", .index 1, .field "body", .field "statements", .index 0, .field "externalCall"], legacyCall_id, by rfl⟩

def legacy_peek : Located ((legacyFixture.getObjVal? "ast").toOption.getD Json.null) :=
  ⟨[.field "nodes", .index 2, .field "nodes", .index 2, .field "body", .field "statements", .index 0, .field "externalCall"], legacyCall_peek, by rfl⟩

def legacy_put : Located ((legacyFixture.getObjVal? "ast").toOption.getD Json.null) :=
  ⟨[.field "nodes", .index 2, .field "nodes", .index 3, .field "body", .field "statements", .index 0, .field "externalCall"], legacyCall_put, by rfl⟩

def viaIR_id : Located ((viaIRFixture.getObjVal? "ast").toOption.getD Json.null) :=
  ⟨[.field "nodes", .index 2, .field "nodes", .index 1, .field "body", .field "statements", .index 0, .field "externalCall"], viaIRCall_id, by rfl⟩

def viaIR_peek : Located ((viaIRFixture.getObjVal? "ast").toOption.getD Json.null) :=
  ⟨[.field "nodes", .index 2, .field "nodes", .index 2, .field "body", .field "statements", .index 0, .field "externalCall"], viaIRCall_peek, by rfl⟩

def viaIR_put : Located ((viaIRFixture.getObjVal? "ast").toOption.getD Json.null) :=
  ⟨[.field "nodes", .index 2, .field "nodes", .index 3, .field "body", .field "statements", .index 0, .field "externalCall"], viaIRCall_put, by rfl⟩

def legacyProfile : Profile :=
  (readProfile legacyFixture).toOption.get (by decide)

def pureDeclaration : Located legacyProfile.ast :=
  (locate legacyProfile.ast [.field "nodes", .index 1, .field "nodes", .index 0]).get (by decide)

def attachedPure : Attached legacyProfile :=
  ((attach legacyProfile [pureDeclaration] legacy_id).toOption).get (by decide)

def issuedPure : Attached legacyProfile :=
  ((attachPaths legacyProfile [pureDeclaration.path] legacy_id.path).toOption).get (by decide)

theorem issued_declaration_attached :
    ∃ path, walk legacyProfile.ast path = some issuedPure.checked.info.declaration :=
  issuedPure.declaration_at

def pureCallee : Located legacyProfile.ast :=
  (legacy_id.descend [.field "expression"]).get (by decide)

theorem descendant_callee_identity :
    pureCallee.node = (legacyCall_id.getObjVal? "expression").toOption.getD Json.null := by rfl

theorem descendant_original_path :
    pureCallee.path = legacy_id.path ++ [.field "expression"] := by rfl

theorem descendant_wrong_field_refused :
    (legacy_id.descend [.field "missing"]).isSome = false := by rfl

theorem descendant_wrong_kind_refused :
    (legacy_id.descend [.index 0]).isSome = false := by rfl

theorem fixture_location_identity :
    ((legacy_id.descend []).get (by decide)).node = legacy_id.node := by rfl

theorem fixture_checked_identity :
    issuedPure.checked.info = attachedPure.checked.info :=
  issuedPure.info_unique attachedPure (by rfl) (by rfl)

theorem distinct_fixture_call_paths : legacy_id.path ≠ legacy_put.path := by decide

theorem issued_pure_static : issuedPure.checked.info.isStatic = true := by rfl

theorem issued_pure_site : issuedPure.checked.info.site = 35 := by rfl

theorem absent_call_path_refused :
    attachPaths legacyProfile [pureDeclaration.path] [.field "missing"] = .error (.callPath [.field "missing"]) := by rfl

theorem absent_declaration_path_refused :
    attachPaths legacyProfile [[.field "missing"]] legacy_id.path = .error (.declarationPath [.field "missing"]) := by rfl

theorem wrong_call_node_refused :
    attachPaths legacyProfile [pureDeclaration.path] pureDeclaration.path = .error (.metadata .callShape) := by rfl

theorem duplicate_selected_path_refused :
    attachPaths legacyProfile [pureDeclaration.path, pureDeclaration.path] legacy_id.path = .error (.metadata .declaration) := by rfl

theorem attached_pure_static : attachedPure.checked.info.isStatic = true := by rfl

theorem mismatched_attached_declaration_refused :
    (attach legacyProfile [pureDeclaration] legacy_put).isOk = false := by rfl

theorem attached_pure_site : attachedPure.checked.info.site = 35 := by rfl

example : walk (Json.mkObj [("x", .arr #[.num 1])]) [.field "x", .index 0] = some (.num 1) := by rfl
example : walk (Json.mkObj [("x", .arr #[.num 1])]) [.field "y"] = none := by rfl
example : walk (.arr #[Json.null]) [.index 1] = none := by rfl
example : walk (.str "spoof") [.field "x"] = none := by rfl
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.attached_pure_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms attached_pure_static
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.attached_pure_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms attached_pure_site
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.mismatched_attached_declaration_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mismatched_attached_declaration_refused
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.issued_pure_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms issued_pure_static
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.issued_pure_site' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms issued_pure_site
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.absent_call_path_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms absent_call_path_refused
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.absent_declaration_path_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms absent_declaration_path_refused
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.wrong_call_node_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_call_node_refused
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.duplicate_selected_path_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms duplicate_selected_path_refused
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.descendant_callee_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms descendant_callee_identity
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.descendant_original_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms descendant_original_path
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.descendant_wrong_field_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms descendant_wrong_field_refused
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.descendant_wrong_kind_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms descendant_wrong_kind_refused
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.fixture_location_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixture_location_identity
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.fixture_checked_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixture_checked_identity
/-- info: 'Solidity.Frontend.CallMetadata.PathControls.distinct_fixture_call_paths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms distinct_fixture_call_paths
end Solidity.Frontend.CallMetadata.PathControls
