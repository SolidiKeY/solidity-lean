import Solidity.Frontend.QualifiedUnits.Lookup

/-! Candidate-level kernel controls. These are not Solidity compiler tests. -/
namespace Solidity.Frontend.QualifiedUnits.Controls
open Solidity.Source

/-- Construct existing intrinsic unit syntax without changing its representation. -/
def unitOf (xs : List (Syn .top)) : Syn .unit :=
  .unit (xs.foldr Syn.cons Syn.nil)

def hops : UnitSet := ⟨[
  ("A", unitOf [.importStar "N" "B"]),
  ("B", unitOf [.importStar "M" "C"]),
  ("C", unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem multi_hop : lookup hops [] "A" ⟨"N", ["M", "T"]⟩ = [.decl ⟨"C", 0⟩] := by
  decide +kernel

theorem missing_symbol : lookup hops [] "A" ⟨"N", ["M", "Missing"]⟩ = [] := by
  decide +kernel

def cyclic : UnitSet := ⟨[
  ("A", unitOf [.importStar "N" "B"]),
  ("B", unitOf [.importStar "Back" "A", .topPart (.enum "T" "a" [])])]⟩

theorem cycle_path : lookup cyclic [] "A" ⟨"N", ["Back", "N", "T"]⟩ = [.decl ⟨"B", 0⟩] := by
  decide +kernel

def diamond : UnitSet := ⟨[
  ("A", unitOf [.importPath "B" none, .importPath "D" none]),
  ("B", unitOf [.importPath "C" none]),
  ("D", unitOf [.importPath "C" none]),
  ("C", unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem diamond_identity : lookup diamond [] "A" ⟨"T", []⟩ = [.decl ⟨"C", 0⟩] := by
  decide +kernel

def duplicateOwners : UnitSet := ⟨[("A", unitOf [
  .contract false "C" .none .nil (.cons (.enum "Left" "a" []) .nil),
  .contract false "C" .none .nil (.cons (.enum "Right" "a" []) .nil)])]⟩

theorem first_owner_left : step duplicateOwners [] (.decl ⟨"A", 0⟩) "Left" = [.decl ⟨"A", 1⟩] := by
  decide +kernel

theorem first_owner_not_right : step duplicateOwners [] (.decl ⟨"A", 0⟩) "Right" = [] := by
  decide +kernel

theorem second_owner_right : step duplicateOwners [] (.decl ⟨"A", 2⟩) "Right" = [.decl ⟨"A", 3⟩] := by
  decide +kernel

theorem second_owner_not_left : step duplicateOwners [] (.decl ⟨"A", 2⟩) "Left" = [] := by
  decide +kernel

end Solidity.Frontend.QualifiedUnits.Controls
