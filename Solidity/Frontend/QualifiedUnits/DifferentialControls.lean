import Solidity.Frontend.QualifiedUnits.Checked
import Solidity.Frontend.QualifiedUnits.Controls
import Solidity.Frontend.QualifiedUnits.SignatureGap

/-! Resolution-relevant intrinsic transcriptions of compiler fixtures.
Unit names and original declaration positions match solc's source graphs.
Pragmas/comments and unrelated bodies are elided; this is a finite external
comparison, not a parser correspondence or Solidity-wide correctness proof. -/
namespace Solidity.Frontend.QualifiedUnits.DifferentialControls
open Solidity.Source Controls

def typeUse (p : IdPath) : Syn .top :=
  .contract false "Use" .none .nil
    (.cons (.stateVar (.userType p) none none none false "value" .none) .nil)

def enumUnit : Syn .unit := unitOf [.topPart (.enum "T" "a" [])]

def hopsInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "B.sol", typeUse ⟨"N", ["M", "T"]⟩]),
  ("B.sol", unitOf [.importStar "M" "C.sol"]), ("C.sol", enumUnit)]⟩

theorem multi_hop : resolve hopsInput [] "A.sol" none [] ⟨"N", ["M", "T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by rfl

def missingInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "B.sol", typeUse ⟨"N", ["M", "Missing"]⟩]),
  ("B.sol", unitOf [.importStar "M" "C.sol"]), ("C.sol", enumUnit)]⟩

theorem missing_symbol : resolve missingInput [] "A.sol" none [] ⟨"N", ["M", "Missing"]⟩ = .error .missing := by rfl

def ambiguousInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "B.sol", .importStar "N" "C.sol", typeUse ⟨"N", ["T"]⟩]),
  ("B.sol", enumUnit), ("C.sol", enumUnit)]⟩

theorem ambiguous_namespace : resolve ambiguousInput [] "A.sol" none [] ⟨"N", ["T"]⟩ = .error .ambiguous := by rfl

def spellingInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "L" "B.sol", .importStar "R" "C.sol",
    .contract false "Use" .none .nil (.cons (.stateVar (.userType ⟨"L", ["T"]⟩) none none none false "left" .none)
      (.cons (.stateVar (.userType ⟨"R", ["T"]⟩) none none none false "right" .none) .nil))]),
  ("B.sol", enumUnit), ("C.sol", enumUnit)]⟩

theorem left_identity : resolve spellingInput [] "A.sol" none [] ⟨"L", ["T"]⟩ = .ok [.decl ⟨"B.sol", 0⟩] := by rfl
theorem right_identity : resolve spellingInput [] "A.sol" none [] ⟨"R", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by rfl

def aliasInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importSymbols (.importAlias "M" (some "N")) .nil "B.sol", typeUse ⟨"N", ["T"]⟩]),
  ("B.sol", unitOf [.importStar "M" "C.sol"]), ("C.sol", enumUnit)]⟩

theorem symbol_namespace_alias : resolve aliasInput [] "A.sol" none [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by rfl

def allInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "B.sol", typeUse ⟨"N", ["T"]⟩]),
  ("B.sol", unitOf [.importPath "C.sol" none]), ("C.sol", enumUnit)]⟩

theorem transitive_all : resolve allInput [] "A.sol" none [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by rfl

def diamondInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importPath "B.sol" none, .importPath "D.sol" none, typeUse ⟨"T", []⟩]),
  ("B.sol", unitOf [.importPath "C.sol" none]), ("D.sol", unitOf [.importPath "C.sol" none]), ("C.sol", enumUnit)]⟩

theorem diamond_identity : resolve diamondInput [] "A.sol" none [] ⟨"T", []⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by rfl

def cycleInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "B.sol", typeUse ⟨"N", ["Back", "N", "T"]⟩]),
  ("B.sol", unitOf [.importStar "Back" "A.sol", .topPart (.enum "T" "a" [])])]⟩

theorem cyclic_namespace : resolve cycleInput [] "A.sol" none [] ⟨"N", ["Back", "N", "T"]⟩ = .ok [.decl ⟨"B.sol", 0⟩] := by rfl

def shadowInput (visibility : StateVis) : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "C.sol",
    .contract false "B" .none .nil (.cons (.stateVar (.elem .bool) (some visibility) none none false "N" .none) .nil),
    .contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none) .nil)
      (.cons (.stateVar (.userType ⟨"N", ["T"]⟩) none none none false "value" .none) .nil)]),
  ("C.sol", enumUnit)]⟩

theorem private_base_fallback : resolve (shadowInput .priv) [] "A.sol" (some ⟨"A.sol", 2⟩) [] ⟨"N", ["T"]⟩ = .ok [.decl ⟨"C.sol", 0⟩] := by rfl
theorem visible_base_shadow : resolve (shadowInput .internal) [] "A.sol" (some ⟨"A.sol", 2⟩) [] ⟨"N", ["T"]⟩ = .error .missing := by rfl

def localInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "C.sol",
    .contract false "Use" .none .nil (.cons
      (.function (.ident "f") .nil (some .external) none .nil false none .nil
        (.some (.block (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl (.elem .bool) none "N") .none)))
          (.cons (.stmtItem (.simpleStmt (.declVar (.varDecl (.userType ⟨"N", ["T"]⟩) none "value") .none))) .nil))))) .nil)]),
  ("C.sol", enumUnit)]⟩

/-- The fixture's first local is N, in the original Use container. -/
theorem local_shadow : resolve localInput [] "A.sol" (some ⟨"A.sol", 0⟩) ["N"] ⟨"N", ["T"]⟩ = .error (.localShadow 0) := by rfl

def baseDefinition : Syn .top := .contract false "Base" .none .nil
  (.cons (.struct "S" (.structMember (.elem (.int false 256 (by decide))) "value") .nil) .nil)

def inheritedInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "B.sol",
    .contract false "D" .none (.cons (.inherit ⟨"N", ["Base"]⟩ .none) .nil) .nil,
    typeUse ⟨"D", ["S"]⟩]), ("B.sol", unitOf [baseDefinition])]⟩

theorem qualified_base_identity : unitBase inheritedInput [] "A.sol" ⟨"N", ["Base"]⟩ = some ⟨"B.sol", 0⟩ := by rfl
theorem inherited_struct_identity : resolve inheritedInput [] "A.sol" none [] ⟨"D", ["S"]⟩ = .ok [.decl ⟨"B.sol", 1⟩] := by rfl

def ambiguousBaseInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "N" "B.sol", .importStar "N" "C.sol",
    .contract false "D" .none (.cons (.inherit ⟨"N", ["Base"]⟩ .none) .nil) .nil,
    typeUse ⟨"D", ["S"]⟩]), ("B.sol", unitOf [baseDefinition]), ("C.sol", unitOf [])]⟩

theorem ambiguous_base : resolve ambiguousBaseInput [] "A.sol" none [] ⟨"D", ["S"]⟩ = .error .missing := by rfl

theorem qualified_base_query : resolve inheritedInput [] "A.sol" none [] ⟨"N", ["Base"]⟩ = .ok [.decl ⟨"B.sol", 0⟩] := by rfl

def gFunction (argument : Syn .expr) : Syn (.part false) :=
  .function (.ident "g") .nil (some .external) (some .pure) .nil false none
    (.cons (.param SignatureGap.uintTy none none) .nil)
    (.some (.block (.cons (.stmtItem (.returnStmt (.some
      (.call (.ident "f") (.positional (.cons argument .nil)))))) .nil)))

def inheritedOverloadInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importSymbols (.importAlias "B" none) .nil "B.sol",
    .contract false "D" .none (.cons (.inherit ⟨"B", []⟩ .none) .nil)
      (.cons (SignatureGap.functionOf (.elem .bool) 2)
        (.cons (gFunction (.lit (.num (.dec 1 0 0)))) .nil))]),
  ("B.sol", unitOf [.contract false "B" .none .nil
    (.cons (SignatureGap.functionOf SignatureGap.uintTy 1) .nil)])]⟩

def qualifiedOverloadInput : UnitSet := ⟨[
  ("A.sol", unitOf [.importStar "L" "B.sol", .importStar "R" "C.sol",
    .contract false "D" .none (.cons (.inherit ⟨"L", ["B"]⟩ .none) .nil)
      (.cons (SignatureGap.functionOf (.userType ⟨"R", ["T"]⟩) 2)
        (.cons (gFunction (.member (.member (.ident "L") "T") "a")) .nil))]),
  ("B.sol", unitOf [.topPart (.enum "T" "a" []), .contract false "B" .none .nil
    (.cons (SignatureGap.functionOf (.userType ⟨"T", []⟩) 1) .nil)]),
  ("C.sol", enumUnit)]⟩

/-- Preserved counterexample: the compiler's B.f(uint) identity is absent. -/
theorem inherited_overload_query_gap : resolve inheritedOverloadInput [] "A.sol" (some ⟨"A.sol", 0⟩) [] ⟨"f", []⟩ = .ok [.decl ⟨"A.sol", 1⟩] := by rfl

/-- Preserved counterexample: distinct units' T types must not be conflated. -/
theorem qualified_overload_query_gap : resolve qualifiedOverloadInput [] "A.sol" (some ⟨"A.sol", 0⟩) [] ⟨"f", []⟩ = .ok [.decl ⟨"A.sol", 1⟩] := by rfl

end Solidity.Frontend.QualifiedUnits.DifferentialControls
