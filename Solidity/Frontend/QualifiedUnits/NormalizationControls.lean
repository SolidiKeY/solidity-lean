import Solidity.Frontend.QualifiedUnits.SignatureHiding
import Solidity.Frontend.QualifiedUnits.DifferentialControls

/-! H27 kernel controls over actual intrinsic Source declarations. Compiler
observations are recorded separately; these controls prove no external
Solidity adequacy claim. -/
namespace Solidity.Frontend.QualifiedUnits.NormalizationControls
open Solidity.Source Controls SignatureNormalization

theorem base_identity :
    (normalize SignatureGap.program [] ⟨"A",1⟩).map (fun s => s.owner.val) = some ⟨"A",1⟩ := by
  decide +kernel

theorem derived_identity :
    (normalize SignatureGap.program [] ⟨"A",3⟩).map (fun s => s.owner.val) = some ⟨"A",3⟩ := by
  decide +kernel

theorem inherited_distinct_parameters :
    sameParams SignatureGap.program [] ⟨"A",3⟩ ⟨"A",1⟩ = some false := by
  decide +kernel

theorem two_units_same_spelling :
    sameParams DifferentialControls.qualifiedOverloadInput [] ⟨"A.sol",1⟩ ⟨"B.sol",2⟩ = some false := by
  decide +kernel

def aliases : UnitSet := ⟨[
  ("A",unitOf [.importStar "L" "B",.importStar "R" "B",
    .contract false "D" .none .nil (.cons (SignatureGap.functionOf (.userType ⟨"L",["T"]⟩) 1)
      (.cons (SignatureGap.functionOf (.userType ⟨"R",["T"]⟩) 2) .nil))]),
  ("B",unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem aliases_same_parameters : sameParams aliases [] ⟨"A",1⟩ ⟨"A",2⟩ = some true := by
  decide +kernel

theorem aliases_distinct_declarations :
    (normalize aliases [] ⟨"A",1⟩).map (fun s => s.owner.val) ≠
      (normalize aliases [] ⟨"A",2⟩).map (fun s => s.owner.val) := by
  decide +kernel

theorem multihop_type_identity :
    (nominal hops [] "A" none .memory ⟨"N",["M","T"]⟩).bind TypeKey.nominalId? = some ⟨"C",0⟩ := by
  decide +kernel

theorem cyclic_alias_type_identity :
    (nominal cyclic [] "A" none .memory ⟨"N",["Back","N","T"]⟩).bind TypeKey.nominalId? = some ⟨"B",0⟩ := by
  decide +kernel

theorem diamond_type_identity :
    (nominal diamond [] "A" none .memory ⟨"T",[]⟩).bind TypeKey.nominalId? = some ⟨"C",0⟩ := by
  decide +kernel

theorem missing_type_refused : nominal aliases [] "A" none .memory ⟨"L",["Absent"]⟩ = none := by
  decide +kernel

def ambiguous : UnitSet := ⟨[
  ("A",unitOf [.importPath "B" none,.importPath "C" none]),
  ("B",unitOf [.topPart (.enum "T" "a" [])]),
  ("C",unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem ambiguous_type_refused : nominal ambiguous [] "A" none .memory ⟨"T",[]⟩ = none := by
  decide +kernel

def unresolved : UnitSet := ⟨[("A",unitOf [
  .contract false "D" .none .nil (.cons (SignatureGap.functionOf (.userType ⟨"Absent",[]⟩) 1)
    (.cons (SignatureGap.functionOf SignatureGap.uintTy 2) .nil))])]⟩

theorem unresolved_is_not_distinct : sameParams unresolved [] ⟨"A",1⟩ ⟨"A",2⟩ = none := by
  decide +kernel

theorem missing_declaration_refused : normalize aliases [] ⟨"A",99⟩ = none := by
  decide +kernel

theorem first_original_owner :
    (duplicateOwners.decl? ⟨"A",1⟩).bind (ownerScope duplicateOwners ⟨"A",1⟩) = some (some ⟨"A",0⟩) := by
  decide +kernel

theorem second_original_owner :
    (duplicateOwners.decl? ⟨"A",3⟩).bind (ownerScope duplicateOwners ⟨"A",3⟩) = some (some ⟨"A",2⟩) := by
  decide +kernel

theorem storage_memory_distinct :
    (types aliases [] "A" none .memory (.param (.elem .bytes) (some .storage) none) ≠
      types aliases [] "A" none .memory (.param (.elem .bytes) (some .memory) none)) := by
  decide +kernel

def locationFunction (loc : DataLoc) (vis : Visibility) : Syn (.part false) :=
  .function (.ident "f") (.cons (.param (.elem .bytes) (some loc) none) .nil)
    (some vis) (some .pure) .nil false none .nil .none

def locations (baseLoc derivedLoc : DataLoc) (baseVis derivedVis : Visibility) : UnitSet := ⟨[("A",unitOf [
  .contract false "B" .none .nil (.cons (locationFunction baseLoc baseVis) .nil),
  .contract false "D" .none (.cons (.inherit ⟨"B",[]⟩ .none) .nil)
    (.cons (locationFunction derivedLoc derivedVis) .nil)])]⟩

theorem external_calldata_public_memory_hides :
    SignatureHiding.hides (locations .calldata .memory .external .pub) [] ⟨"A",3⟩ ⟨"A",1⟩ = some true := by
  decide +kernel

theorem public_memory_calldata_distinct :
    SignatureHiding.hides (locations .memory .calldata .pub .pub) [] ⟨"A",3⟩ ⟨"A",1⟩ = some false := by
  decide +kernel

theorem internal_memory_calldata_distinct :
    SignatureHiding.hides (locations .memory .calldata .internal .internal) [] ⟨"A",3⟩ ⟨"A",1⟩ = some false := by
  decide +kernel

theorem internal_storage_memory_distinct :
    SignatureHiding.hides (locations .storage .memory .internal .internal) [] ⟨"A",3⟩ ⟨"A",1⟩ = some false := by
  decide +kernel

theorem hiding_unresolved_refused :
    SignatureHiding.hides unresolved [] ⟨"A",1⟩ ⟨"A",2⟩ = none := by
  decide +kernel

end Solidity.Frontend.QualifiedUnits.NormalizationControls
