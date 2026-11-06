import Solidity.Frontend.StatementGrammarH28.TryCoverage

namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def tryTower (k : SCtx) : Nat → Syn (.stmt k)
  | 0 => .blockStmt (.block .nil)
  | n + 1 => .ifStmt (.lit (.bool true)) (tryTower k n) .none

def tryTowerWords : Nat → List Tok
  | 0 => braces []
  | n + 1 => [.kw .if_, .punct .lparen, .bool true, .punct .rparen] ++ tryTowerWords n

theorem try_depth_relation (k : SCtx) (depth : Nat) :
    BooleanStatements (tryTower k depth) (tryTowerWords depth) depth := by
  induction depth with
  | zero => exact .loops (.block .nil)
  | succ depth ih => exact .ifNone ih

def tryFirstCatch (k : SCtx) (depth : Nat) : Syn (.catchClause k) :=
  .catchPlain (.block (.cons (.stmtItem (tryTower k depth)) .nil))
def tryFirstWords (depth : Nat) : List Tok := tk .catch_ ++ braces (tryTowerWords depth)

theorem try_first_catch_relation (k : SCtx) (depth : Nat) :
    BooleanCatch (tryFirstCatch k depth) (tryFirstWords depth) (depth + 9) := by
  have body := BooleanListBound.cons (try_depth_relation k depth) BooleanListBound.nil
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using BooleanCatch.plain body

def tryTail (k : SCtx) : Nat → Syn (.list (.catchClause k))
  | 0 => .nil
  | n + 1 => .cons (.catchSig (some "Failure") (.param (.elem .bool) .none (some "x")) .nil
      (.block .nil)) (tryTail k n)
def tryTailParts : Nat → List (List Tok)
  | 0 => []
  | n + 1 => (tk .catch_ ++ idt "Failure" ++ parens ([.elem .bool] ++ idt "x") ++ braces []) ::
      tryTailParts n

theorem try_tail_relation (k : SCtx) (width : Nat) :
    BooleanCatchList (tryTail k (width + 1)) (tryTailParts (width + 1)) 6 := by
  induction width with
  | zero => exact .cons (.signature (some "Failure") (some "x") .nil) .nil
  | succ width ih => exact .cons (.signature (some "Failure") (some "x") .nil) ih

def recursiveTry (k : SCtx) (name : String) (depth width : Nat) : Syn (.stmt k) :=
  .tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil)
    (tryFirstCatch k depth) (tryTail k (width + 1))
def recursiveTryWords (name : String) (depth width : Nat) : List Tok :=
  [.kw .try_, .ident name, .punct .lparen, .punct .rparen, .punct .lbrace, .punct .rbrace] ++
    tryFirstWords depth ++ (tryTailParts (width + 1)).flatten

theorem try_recursive_fragment_relation (k : SCtx) (name : String) (depth width : Nat) :
    BooleanTry (recursiveTry k name depth width) (recursiveTryWords name depth width)
      (max (depth + 9) 6 + 10) :=
  .attempt name (try_first_catch_relation k depth) (try_tail_relation k width)

theorem try_arbitrary_width_depth_parse (k : SCtx) (name : String) (depth width extra : Nat)
    (s : St) (hs : NoFollowingCatch s) :
    stmt (extra + (max (depth + 9) 6 + 10)) k
      (locatedInput (recursiveTryWords name depth width) s) =
      .ok (recursiveTry k name depth width, s) :=
  boolean_try_fragment_coverage (try_recursive_fragment_relation k name depth width) extra s hs

theorem try_arbitrary_width_depth_yield (k : SCtx) (name : String) (depth width : Nat)
    (L : List Choice) :
    (recursiveTry k name depth width).yield L = some ([recursiveTryWords name depth width], L) :=
  boolean_try_fragment_yield (try_recursive_fragment_relation k name depth width) L

theorem try_signature_first_coverage (k : SCtx) (name : String) (clauseName paramName : Option String)
    (n : Nat) (s : St) (hs : NoFollowingCatch s) :
    stmt (n + 16) k (tryCallInput name
      (signatureCatchInput clauseName paramName [] s)) =
      .ok (.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil)
        (.catchSig clauseName (.param (.elem .bool) .none paramName) .nil (.block .nil)) .nil, s) := by
  have parsed := boolean_try_coverage (k := k) (BooleanCatch.signature clauseName paramName BooleanListBound.nil)
    BooleanCatchList.nil name n s hs
  simpa only [List.flatten_nil, List.append_nil, signatureCatchInput, blockInput,
    locatedInput_append] using parsed

theorem try_plain_only_coverage (k : SCtx) (name : String) (depth n : Nat)
    (s : St) (hs : NoFollowingCatch s) :
    stmt (n + max (depth + 9) 0 + 10) k (tryCallInput name (locatedInput (tryFirstWords depth) s)) =
      .ok (.tryStmt (.call (.ident name) (.positional .nil)) .nil (.block .nil)
        (tryFirstCatch k depth) .nil, s) := by
  have parsed := boolean_try_coverage (try_first_catch_relation k depth) BooleanCatchList.nil name n s hs
  simpa only [List.flatten_nil, List.append_nil] using parsed

theorem try_following_statement_preserved (k : SCtx) (name : String) (depth width extra : Nat) (s : St) :
    stmt (extra + (max (depth + 9) 6 + 10)) k (locatedInput (recursiveTryWords name depth width)
      (locatedInput [.kw .return_, .punct .semi] s)) =
      .ok (recursiveTry k name depth width, locatedInput [.kw .return_, .punct .semi] s) :=
  try_arbitrary_width_depth_parse k name depth width extra _
    (statement_no_following_catch (Syn.returnStmt (k := k) .none) [] []
      [[.kw .return_, .punct .semi]] rfl s)

def tryRefuses (fuel : Nat) (input : St) : Bool :=
  match stmt fuel .body input with
  | .error _ => true
  | .ok _ => false

theorem try_missing_catch_rejected :
    tryRefuses 20 (tryCallInput "f" ⟨[], [], 0⟩) = true := by decide +kernel

theorem try_missing_body_and_empty_parameters_rejected :
    tryRefuses 20 (locatedInput [.kw .try_, .ident "f", .punct .lparen, .punct .rparen,
      .kw .catch_, .punct .lbrace, .punct .rbrace] ⟨[], [], 0⟩) = true ∧
    tryRefuses 20 (tryCallInput "f" (locatedInput [.kw .catch_, .punct .lparen, .punct .rparen,
      .punct .lbrace, .punct .rbrace] ⟨[], [], 0⟩)) = true := by decide +kernel

theorem try_insufficient_fuel_rejected :
    tryRefuses 0 (tryCallInput "f" (plainCatchInput [] ⟨[], [], 0⟩)) = true ∧
    tryRefuses 1 (tryCallInput "f" (plainCatchInput [] ⟨[], [], 0⟩)) = true := by decide +kernel

theorem try_greedy_catch_suffix_consumed :
    stmt 20 .body (tryCallInput "f" (plainCatchInput [] (plainCatchInput [] ⟨[], [], 0⟩))) =
      .ok (.tryStmt (.call (.ident "f") (.positional .nil)) .nil (.block .nil)
        (.catchPlain (.block .nil)) (.cons (.catchPlain (.block .nil)) .nil), ⟨[], [], 0⟩) := by rfl

theorem try_fragment_inhabited_derivation :
    BooleanTry (recursiveTry .body "f" 1 0) (recursiveTryWords "f" 1 0) (max (1 + 9) 6 + 10) ∧
    (recursiveTry .body "f" 1 0).Derives (recursiveTryWords "f" 1 0) :=
  ⟨try_recursive_fragment_relation .body "f" 1 0,
   boolean_try_derives (try_recursive_fragment_relation .body "f" 1 0)⟩

/-- info: 'Solidity.Frontend.StatementGrammarH28.try_depth_relation' does not depend on any axioms -/
#guard_msgs in
#print axioms try_depth_relation
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_first_catch_relation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms try_first_catch_relation
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_tail_relation' does not depend on any axioms -/
#guard_msgs in
#print axioms try_tail_relation
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_recursive_fragment_relation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms try_recursive_fragment_relation
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_arbitrary_width_depth_parse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms try_arbitrary_width_depth_parse
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_arbitrary_width_depth_yield' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms try_arbitrary_width_depth_yield
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_signature_first_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms try_signature_first_coverage
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_plain_only_coverage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms try_plain_only_coverage
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_following_statement_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms try_following_statement_preserved
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_missing_catch_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms try_missing_catch_rejected
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_missing_body_and_empty_parameters_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms try_missing_body_and_empty_parameters_rejected
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_insufficient_fuel_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms try_insufficient_fuel_rejected
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_greedy_catch_suffix_consumed' does not depend on any axioms -/
#guard_msgs in
#print axioms try_greedy_catch_suffix_consumed
/-- info: 'Solidity.Frontend.StatementGrammarH28.try_fragment_inhabited_derivation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms try_fragment_inhabited_derivation
end Solidity.Frontend.StatementGrammarH28
