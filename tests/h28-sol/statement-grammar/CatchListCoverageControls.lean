import Solidity.Frontend.StatementGrammarH28.CatchListCoverage

namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def catchPairClauses (k : SCtx) : Nat → Syn (.list (.catchClause k))
  | 0 => .nil
  | n + 1 => .cons (.catchPlain (.block .nil))
      (.cons (.catchSig none (.param (.elem .bool) .none (some "x")) .nil (.block .nil))
        (catchPairClauses k n))

def plainClauseWords : List Tok := tk .catch_ ++ braces []
def sigClauseWords : List Tok := tk .catch_ ++ parens ([.elem .bool] ++ idt "x") ++ braces []
def catchPairParts : Nat → List (List Tok)
  | 0 => []
  | n + 1 => plainClauseWords :: sigClauseWords :: catchPairParts n

theorem catch_pairs_bound (k : SCtx) (width : Nat) :
    BooleanCatchList (catchPairClauses k (width + 1)) (catchPairParts (width + 1)) 6 := by
  induction width with
  | zero => exact .cons (.plain .nil) (.cons (.signature none (some "x") .nil) .nil)
  | succ width ih => exact .cons (.plain .nil) (.cons (.signature none (some "x") .nil) ih)

theorem catch_pairs_count (k : SCtx) (width : Nat) :
    g0ListLength (catchPairClauses k width) = 2 * width := by
  induction width with
  | zero => rfl
  | succ width ih =>
    change g0ListLength (catchPairClauses k width) + 1 + 1 = 2 * (width + 1)
    omega

theorem catch_pairs_many (k : SCtx) (width extra : Nat) (s : St) (hs : NoFollowingCatch s) :
    many (catchStep (extra + 6) k) (locatedInput (catchPairParts (width + 1)).flatten s) =
      .ok (g0ListValues (catchPairClauses k (width + 1)), s) :=
  boolean_catch_list_many (catch_pairs_bound k width) (extra + 6) (by omega) s hs

theorem catch_pairs_many_aux (k : SCtx) (width extra : Nat) (s : St) (hs : NoFollowingCatch s) :
    manyAux (catchStep 6 k) (extra + 2 * (width + 1) + 1)
      (locatedInput (catchPairParts (width + 1)).flatten s) =
      .ok (g0ListValues (catchPairClauses k (width + 1)), s) := by
  have parsed := boolean_catch_list_many_aux (catch_pairs_bound k width) 6 (by omega) extra s hs
  rw [catch_pairs_count] at parsed
  exact parsed

theorem catch_empty_many (fuel : Nat) (k : SCtx) (s : St) (hs : NoFollowingCatch s) :
    many (catchStep fuel k) s = .ok ([], s) :=
  boolean_catch_list_many BooleanCatchList.nil fuel (by omega) s hs

theorem catch_noncatch_suffixes (k : SCtx) (width : Nat) (s : St) :
    many (catchStep 6 k) (locatedInput (catchPairParts (width + 1)).flatten
      (locatedInput [.kw .else_, .kw .unchecked, .kw .return_] s)) =
      .ok (g0ListValues (catchPairClauses k (width + 1)),
        locatedInput [.kw .else_, .kw .unchecked, .kw .return_] s) :=
  catch_pairs_many k width 0 _ (by intro bad; cases bad)

theorem catch_greedy_suffix_consumed :
    many (catchStep 2 .body) (plainCatchInput [] (plainCatchInput [] ⟨[], [], 0⟩)) =
      .ok ([.catchPlain (.block .nil), .catchPlain (.block .nil)], ⟨[], [], 0⟩) := by
  rfl

theorem catch_greedy_suffix_not_frame :
    ¬ NoFollowingCatch (plainCatchInput [] ⟨[], [], 0⟩) := by
  intro bad
  exact bad rfl

def catchAuxRefuses (counter : Nat) : Bool :=
  match manyAux (catchStep 6 .body) counter (plainCatchInput [] ⟨[], [], 0⟩) with
  | .error _ => true
  | .ok _ => false

def catchManyRefuses (fuel : Nat) (ts : List Tok) : Bool :=
  match many (catchStep fuel .body) (locatedInput ts ⟨[], [], 0⟩) with
  | .error _ => true
  | .ok _ => false

theorem catch_many_counter_refusal :
    catchAuxRefuses 0 = true ∧ catchAuxRefuses 1 = true ∧ catchAuxRefuses 2 = false := by
  decide +kernel

theorem catch_many_malformed_clause_refusal :
    catchManyRefuses 6 [.kw .catch_, .punct .lparen, .punct .rparen] = true ∧
    catchManyRefuses 2 sigClauseWords = true := by decide +kernel

def generalAtomCatch : Syn (.catchClause .body) :=
  .catchSig (some "Error") (.param (.elem .string) (.some .memory) (some "reason")) .nil
    (.block (.cons (.stmtItem (.returnStmt (.some (.lit (.str [59]))))) .nil))

def generalCatchHeadCheck : Bool :=
  match generalAtomCatch.yield [.frags [1]] with
  | some (parts, []) => parts.flatten.head? == some (.kw .catch_) && !parts.flatten.isEmpty
  | _ => false

theorem catch_general_atom_yield : generalCatchHeadCheck = true := by decide +kernel

theorem catch_list_relation_inhabited :
    BooleanCatchList (Syn.nil (c := .catchClause .body)) [] 0 ∧
    BooleanCatchList (catchPairClauses .body 1) (catchPairParts 1) 6 :=
  ⟨.nil, catch_pairs_bound .body 0⟩

theorem catch_following_statement_frame (k : SCtx) (s : St) :
    NoFollowingCatch (locatedInput [.kw .return_, .punct .semi] s) :=
  statement_no_following_catch (Syn.returnStmt (k := k) .none) [] []
    [[.kw .return_, .punct .semi]] rfl s

/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_pairs_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_pairs_bound
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_pairs_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_pairs_count
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_pairs_many' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_pairs_many
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_pairs_many_aux' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_pairs_many_aux
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_empty_many' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_empty_many
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_noncatch_suffixes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_noncatch_suffixes
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_greedy_suffix_consumed' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_greedy_suffix_consumed
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_greedy_suffix_not_frame' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_greedy_suffix_not_frame
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_many_counter_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_many_counter_refusal
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_many_malformed_clause_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_many_malformed_clause_refusal
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_general_atom_yield' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_general_atom_yield
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_list_relation_inhabited' does not depend on any axioms -/
#guard_msgs in
#print axioms catch_list_relation_inhabited
/-- info: 'Solidity.Frontend.StatementGrammarH28.catch_following_statement_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms catch_following_statement_frame
end Solidity.Frontend.StatementGrammarH28
