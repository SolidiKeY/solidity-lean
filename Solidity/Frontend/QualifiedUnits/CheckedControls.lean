import Solidity.Frontend.QualifiedUnits.Checked
import Solidity.Frontend.QualifiedUnits.Controls

/-! Kernel controls for accepted lookup and refusal, using existing syntax. -/
namespace Solidity.Frontend.QualifiedUnits.CheckedControls
open Solidity.Source Controls

theorem accepted_hops : resolve hops [] "A" none [] ⟨"N", ["M", "T"]⟩ = .ok [.decl ⟨"C", 0⟩] := by
  rfl

theorem refused_missing : resolve hops [] "A" none [] ⟨"N", ["M", "Missing"]⟩ = .error .missing := by
  rfl

theorem local_shadow : resolve hops [] "A" none ["N"] ⟨"N", ["M", "T"]⟩ = .error (.localShadow 0) := by
  rfl

theorem cycle_accepted : resolve cyclic [] "A" none [] ⟨"N", ["Back", "N", "T"]⟩ = .ok [.decl ⟨"B", 0⟩] := by
  rfl

theorem diamond_accepted : resolve diamond [] "A" none [] ⟨"T", []⟩ = .ok [.decl ⟨"C", 0⟩] := by
  rfl

def inherited : UnitSet := ⟨[("A", unitOf [
  .contract false "B" .none .nil (.cons (.enum "S" "a" []) .nil),
  .contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none) .nil) .nil])]⟩

theorem inherited_type : resolve inherited [] "A" none [] ⟨"D", ["S"]⟩ = .ok [.decl ⟨"A", 1⟩] := by
  rfl

def privateBase : UnitSet := ⟨[
  ("A", unitOf [.importStar "N" "C",
    .contract false "B" .none .nil (.cons (.stateVar (.elem .bool) (some .priv) none none false "N" .none) .nil),
    .contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none) .nil) .nil]),
  ("C", unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem private_base_global_fallback :
    resolve privateBase [] "A" (some ⟨"A", 2⟩) [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C", 0⟩] := by
  rfl

theorem own_private_shadows :
    resolve privateBase [] "A" (some ⟨"A", 0⟩) [] ⟨"N", ["T"]⟩ = .error .missing := by
  rfl

def visibleBase : UnitSet := ⟨[
  ("A", unitOf [.importStar "N" "C",
    .contract false "B" .none .nil (.cons (.stateVar (.elem .bool) (some .internal) none none false "N" .none) .nil),
    .contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none) .nil) .nil]),
  ("C", unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem visible_base_shadows :
    resolve visibleBase [] "A" (some ⟨"A", 2⟩) [] ⟨"N", ["T"]⟩ = .error .missing := by
  rfl

def ambiguousBase : UnitSet := ⟨[
  ("A", unitOf [.importStar "N" "B", .importStar "N" "C",
    .contract false "D" .none (.cons (.inherit ⟨"N", ["Base"]⟩ .none) .nil) .nil]),
  ("B", unitOf [.contract false "Base" .none .nil (.cons (.enum "S" "a" []) .nil)]),
  ("C", unitOf [])]⟩

theorem ambiguous_base_not_followed : baseTargets ambiguousBase [] ⟨"A", 0⟩ = [] := by
  rfl

theorem ambiguous_base_member_refused :
    resolve ambiguousBase [] "A" none [] ⟨"D", ["S"]⟩ = .error .missing := by
  rfl

theorem ambiguous_namespace_refused :
    resolve ambiguousBase [] "A" none [] ⟨"N", ["Base", "S"]⟩ = .error .ambiguous := by
  rfl

def sameSpelling : UnitSet := ⟨[
  ("A", unitOf [.importStar "L" "B", .importStar "R" "C"]),
  ("B", unitOf [.topPart (.enum "T" "a" [])]),
  ("C", unitOf [.topPart (.enum "T" "a" [])])]⟩

theorem left_identity : resolve sameSpelling [] "A" none [] ⟨"L", ["T"]⟩ = .ok [.decl ⟨"B", 0⟩] := by
  rfl

theorem right_identity : resolve sameSpelling [] "A" none [] ⟨"R", ["T"]⟩ = .ok [.decl ⟨"C", 0⟩] := by
  rfl

theorem foreign_scope_refused : resolve sameSpelling [] "A" (some ⟨"B", 0⟩) [] ⟨"L", ["T"]⟩ = .error .invalidScope := by
  rfl

theorem missing_scope_refused : resolve sameSpelling [] "A" (some ⟨"A", 99⟩) [] ⟨"L", ["T"]⟩ = .error .invalidScope := by
  rfl

theorem noncontainer_scope_refused : resolve sameSpelling [] "B" (some ⟨"B", 0⟩) [] ⟨"T", []⟩ = .error .invalidScope := by
  rfl

end Solidity.Frontend.QualifiedUnits.CheckedControls
