import Solidity.Frontend.QualifiedUnits.References
import Solidity.Frontend.QualifiedUnits.Controls

namespace Solidity.Frontend.QualifiedUnits.ReferenceControls
open Solidity.Source Controls

theorem member_chain : expressionPath (.member (.member (.ident "N") "M") "T") = some ⟨"N", ["M", "T"]⟩ := by
  simp only [expressionPath,expressionPathAny, Option.map, List.nil_append, List.cons_append]

theorem member_chain_references :
    references (.member (.member (.ident "N") "M") "T") =
      [⟨"N", ["M", "T"]⟩, ⟨"N", ["M"]⟩, ⟨"N", []⟩] := by
  simp only [references, expressionPath, expressionPathAny, Option.map, Option.toList, List.nil_append, List.cons_append]

theorem nonpath_receiver :
    references (.member (.call (.ident "f") (.positional .nil)) "field") = [⟨"f", []⟩] := by
  simp only [references, expressionPath, expressionPathAny, Option.map, Option.toList, List.nil_append, List.append_nil]

theorem mapping_key_path :
    references (.mapping (.path ⟨"N", ["T"]⟩) none (.elem .bool) none) = [⟨"N", ["T"]⟩] := by
  rfl

theorem mapping_key_elementary :
    references (.mapping (.elem .bool (by decide)) none (.elem .bool) none) = [] := by
  rfl

def symbolAlias : UnitSet := ⟨[
  ("A", unitOf [.importSymbols (.importAlias "M" (some "N")) .nil "B"]),
  ("B", unitOf [.importStar "M" "C"]),
  ("C", unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem symbol_namespace_alias : resolve symbolAlias [] "A" none [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C", 0⟩] := by
  rfl

def transitiveAll : UnitSet := ⟨[
  ("A", unitOf [.importStar "N" "B"]),
  ("B", unitOf [.importPath "C" none]),
  ("C", unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem transitive_all : resolve transitiveAll [] "A" none [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C", 0⟩] := by
  rfl

end Solidity.Frontend.QualifiedUnits.ReferenceControls
