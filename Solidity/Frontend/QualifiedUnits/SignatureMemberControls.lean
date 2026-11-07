import Solidity.Frontend.QualifiedUnits.SignatureMembers
import Solidity.Frontend.QualifiedUnits.NormalizationControls

/-! Kernel controls for executed collection, not an assumed owner order or
supplied collection result. External compiler comparison remains separate. -/
namespace Solidity.Frontend.QualifiedUnits.SignatureMemberControls
open Solidity.Source Controls SignatureGap NormalizationControls SignatureMembers

theorem inherited_overloads : collect program [] ⟨"A",2⟩ "f" = some [⟨"A",3⟩,⟨"A",1⟩] := by
  decide +kernel

theorem cross_unit_nominal_overloads : collect DifferentialControls.qualifiedOverloadInput [] ⟨"A.sol",0⟩ "f" =
    some [⟨"A.sol",1⟩,⟨"B.sol",2⟩] := by decide +kernel

theorem same_owner_duplicates_preserved : collect aliases [] ⟨"A",0⟩ "f" = some [⟨"A",1⟩,⟨"A",2⟩] := by
  decide +kernel

theorem external_location_override : collect (locations .calldata .memory .external .pub) [] ⟨"A",2⟩ "f" =
    some [⟨"A",3⟩] := by decide +kernel

theorem storage_memory_overloads : collect (locations .storage .memory .internal .internal) [] ⟨"A",2⟩ "f" =
    some [⟨"A",3⟩,⟨"A",1⟩] := by decide +kernel

theorem unresolved_first_owner_refused : collect unresolved [] ⟨"A",0⟩ "f" = none := by decide +kernel

theorem missing_root_refused : collect program [] ⟨"A",99⟩ "f" = none := by decide +kernel

theorem noncontainer_root_refused : collect program [] ⟨"A",1⟩ "f" = none := by decide +kernel

def missingBase : UnitSet := ⟨[("A",unitOf [.contract false "D" .none
  (.cons (.inherit ⟨"Missing",[]⟩ .none) .nil) (.cons (functionOf uintTy 1) .nil)])]⟩

theorem missing_base_refused : collect missingBase [] ⟨"A",0⟩ "f" = none := by decide +kernel

def cyclicBase : UnitSet := ⟨[("A",unitOf [.contract false "D" .none
  (.cons (.inherit ⟨"D",[]⟩ .none) .nil) (.cons (functionOf uintTy 1) .nil)])]⟩

theorem inheritance_cycle_refused : collect cyclicBase [] ⟨"A",0⟩ "f" = none := by decide +kernel

def overrideDiamond : UnitSet := ⟨[("A",unitOf [
  .contract false "B" .none .nil (.cons (functionOf uintTy 1) .nil),
  .contract false "L" .none (.cons (.inherit ⟨"B",[]⟩ .none) .nil) .nil,
  .contract false "R" .none (.cons (.inherit ⟨"B",[]⟩ .none) .nil) (.cons (functionOf uintTy 2) .nil),
  .contract false "D" .none (.cons (.inherit ⟨"L",[]⟩ .none) (.cons (.inherit ⟨"R",[]⟩ .none) .nil)) .nil])]⟩

theorem diamond_owner_order : order overrideDiamond [] ⟨"A",5⟩ =
    some [⟨"A",5⟩,⟨"A",3⟩,⟨"A",2⟩,⟨"A",0⟩] := by decide +kernel

theorem diamond_original_override : collect overrideDiamond [] ⟨"A",5⟩ "f" = some [⟨"A",4⟩] := by
  decide +kernel

def ambiguousBase : UnitSet := ⟨[
  ("A",unitOf [.importPath "B" none,.importPath "C" none,
    .contract false "D" .none (.cons (.inherit ⟨"Base",[]⟩ .none) .nil) (.cons (functionOf uintTy 1) .nil)]),
  ("B",unitOf [.contract false "Base" .none .nil .nil]),
  ("C",unitOf [.contract false "Base" .none .nil .nil])]⟩

theorem ambiguous_written_base_refused : collect ambiguousBase [] ⟨"A",0⟩ "f" = none := by decide +kernel

theorem empty_name_collection : collect program [] ⟨"A",2⟩ "Absent" = some [] := by decide +kernel

end Solidity.Frontend.QualifiedUnits.SignatureMemberControls
