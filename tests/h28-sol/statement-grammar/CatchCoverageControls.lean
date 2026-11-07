import Solidity.Frontend.StatementGrammarH28.CatchCoverage
import Solidity.Source.Ctor

namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def catchTower (k : SCtx) : Nat → Syn (.stmt k)
  | 0 => .blockStmt (.block .nil)
  | n + 1 => .ifStmt (.lit (.bool true)) (catchTower k n) .none

def catchTowerWords : Nat → List Tok
  | 0 => braces []
  | n + 1 => [.kw .if_, .punct .lparen, .bool true, .punct .rparen] ++ catchTowerWords n

theorem catch_arbitrary_depth_relation (k : SCtx) (depth : Nat) :
    BooleanStatements (catchTower k depth) (catchTowerWords depth) depth := by
  induction depth with
  | zero => exact .loops (.block .nil)
  | succ depth ih => exact .ifNone ih

def catchWideBody (k : SCtx) (depth : Nat) : Nat → Syn (.list (.item k))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (catchTower k depth)) (catchWideBody k depth n)

def catchWideParts (depth : Nat) : Nat → List (List Tok)
  | 0 => []
  | n + 1 => catchTowerWords depth :: catchWideParts depth n

theorem catch_arbitrary_width_depth_bound (k : SCtx) (depth width : Nat) :
    BooleanListBound (catchWideBody k depth (width + 1))
      (catchWideParts depth (width + 1)) (depth + 7) := by
  induction width with
  | zero => exact .cons (catch_arbitrary_depth_relation k depth) .nil
  | succ width ih =>
    simpa only [Nat.max_self] using
      BooleanListBound.cons (catch_arbitrary_depth_relation k depth) ih

theorem catch_arbitrary_plain_parse (k : SCtx) (depth width extra : Nat) (s : St) :
    catchClause (extra + (depth + 7) + 2) k
      (plainCatchInput (catchWideParts depth (width + 1)).flatten s) =
      .ok (.catchPlain (.block (catchWideBody k depth (width + 1))), s) :=
  boolean_list_plain_catch_coverage (catch_arbitrary_width_depth_bound k depth width) extra s

theorem catch_arbitrary_signature_parse (k : SCtx) (depth width extra : Nat)
    (name paramName : Option String) (s : St) :
    catchClause (extra + (depth + 7) + 6) k
      (signatureCatchInput name paramName (catchWideParts depth (width + 1)).flatten s) =
      .ok (.catchSig name (.param (.elem .bool) .none paramName) .nil
        (.block (catchWideBody k depth (width + 1))), s) :=
  boolean_list_signature_catch_coverage
    (catch_arbitrary_width_depth_bound k depth width) extra name paramName s

def catchResultCheck (input : St) (ctor : Ctor) : Bool :=
  match catchClause 6 .body input with
  | .ok (c, s) => c.ctor == ctor && s.ts.isEmpty && s.ch.isEmpty
  | .error _ => false

def catchRefuses (fuel : Nat) (ts : List Tok) : Bool :=
  match catchClause fuel .body (locatedInput ts ⟨[], [], 0⟩) with
  | .error _ => true
  | .ok _ => false

theorem catch_both_constructor_controls :
    catchResultCheck (plainCatchInput [] ⟨[], [], 0⟩) .catchPlain = true ∧
    catchResultCheck (signatureCatchInput none none [] ⟨[], [], 0⟩) .catchSig = true := by
  decide +kernel

theorem catch_all_optional_name_variants :
    catchResultCheck (signatureCatchInput none none [] ⟨[], [], 0⟩) .catchSig = true ∧
    catchResultCheck (signatureCatchInput none (some "x") [] ⟨[], [], 0⟩) .catchSig = true ∧
    catchResultCheck (signatureCatchInput (some "Error") none [] ⟨[], [], 0⟩) .catchSig = true ∧
    catchResultCheck (signatureCatchInput (some "Panic") (some "x") [] ⟨[], [], 0⟩) .catchSig = true := by
  decide +kernel

theorem catch_following_keywords_preserved (k : SCtx) (s : St) :
    catchClause 2 k (plainCatchInput []
      (locatedInput [.kw .catch_, .kw .else_, .kw .unchecked] s)) =
      .ok (.catchPlain (.block .nil),
        locatedInput [.kw .catch_, .kw .else_, .kw .unchecked] s) :=
  boolean_list_plain_catch_coverage BooleanListBound.nil 0 _

theorem catch_empty_parameter_list_rejected :
    catchRefuses 6 [.kw .catch_, .punct .lparen, .punct .rparen,
      .punct .lbrace, .punct .rbrace] = true := by decide +kernel

theorem catch_wrong_header_and_missing_brace_rejected :
    catchRefuses 6 [.kw .else_, .punct .lbrace, .punct .rbrace] = true ∧
    catchRefuses 6 [.kw .catch_, .punct .lbrace] = true := by decide +kernel

theorem catch_zero_and_insufficient_fuel_rejected :
    catchRefuses 0 [.kw .catch_, .punct .lbrace, .punct .rbrace] = true ∧
    catchRefuses 1 [.kw .catch_, .punct .lbrace, .punct .rbrace] = true ∧
    catchRefuses 0 [.kw .catch_, .punct .lparen, .elem .bool, .punct .rparen,
      .punct .lbrace, .punct .rbrace] = true := by decide +kernel

theorem catch_fragment_both_constructors_inhabited :
    BooleanCatch (Syn.catchPlain (k := .body) (.block .nil)) (tk .catch_ ++ braces []) 2 ∧
    BooleanCatch (Syn.catchSig (k := .body) (some "Error")
      (.param (.elem .bool) .none (some "x")) .nil (.block .nil))
      (tk .catch_ ++ idt "Error" ++ parens ([.elem .bool] ++ idt "x") ++ braces []) 6 :=
  ⟨.plain .nil, .signature (some "Error") (some "x") .nil⟩

theorem catch_actual_derivation_controls :
    (Syn.catchPlain (k := .body) (.block .nil)).Derives (tk .catch_ ++ braces []) ∧
    (Syn.catchSig (k := .body) none (.param (.elem .bool) .none none) .nil
      (.block .nil)).Derives (tk .catch_ ++ parens [.elem .bool] ++ braces []) :=
  ⟨boolean_catch_derives (.plain .nil), boolean_catch_derives (.signature none none .nil)⟩

/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_arbitrary_depth_relation' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_arbitrary_depth_relation
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_arbitrary_width_depth_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms catch_arbitrary_width_depth_bound
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_arbitrary_plain_parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_arbitrary_plain_parse
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_arbitrary_signature_parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_arbitrary_signature_parse
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_both_constructor_controls' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_both_constructor_controls
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_all_optional_name_variants' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_all_optional_name_variants
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_following_keywords_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_following_keywords_preserved
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_empty_parameter_list_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_empty_parameter_list_rejected
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_wrong_header_and_missing_brace_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_wrong_header_and_missing_brace_rejected
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_zero_and_insufficient_fuel_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_zero_and_insufficient_fuel_rejected
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_fragment_both_constructors_inhabited' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_fragment_both_constructors_inhabited
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_actual_derivation_controls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_actual_derivation_controls
end Solidity.Frontend.StatementGrammarH28
