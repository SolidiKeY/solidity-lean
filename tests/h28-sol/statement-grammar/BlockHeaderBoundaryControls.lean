import Solidity.Frontend.StatementGrammarH28.BlockHeaderBoundary
import Solidity.Source.Ctor

namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def headerStatements : List (Syn (.stmt ⟨true,false⟩)) :=
  [.blockStmt (.block .nil), .simpleStmt (.exprStmt (.ident "x")),
   .ifStmt (.ident "c") (.returnStmt .none) (.some (.returnStmt .none)),
   .forStmt .none .none .none (.blockStmt (.block .nil)),
   .whileStmt (.ident "c") .breakStmt, .doWhile .continueStmt (.ident "c"),
   .continueStmt, .breakStmt,
   .tryStmt (.call (.ident "f") (.positional .nil)) .nil (.block .nil)
     (.catchPlain (.block .nil)) .nil,
   .returnStmt (.some (.ident "x")), .emit (.ident "E") (.positional .nil),
   .revert (.ident "E") (.positional .nil), .assembly false [] .nil]

def headerWitnessCheck {k : SCtx} (b : Syn (.block k)) (L : List Choice) : Bool :=
  b.prec && match b.yield L with
  | some (parts, []) =>
    let words := parts.flatten
    let suffix : St := ⟨[atToken (.kw .return_) 13 15], [], 91⟩
    !namedArgStart (words.drop 1 ++ [.ident "gas", .punct .colon]) &&
      match postLoop 1 (.ident "left") (locatedInput words suffix) with
      | .ok (out, s) => out.toks [] == some [.ident "left"] &&
          s.ts.map (fun t => t.tok) == words ++ [.kw .return_] && s.ch.isEmpty && s.eof == 91
      | .error _ => false
  | _ => false

theorem header_all_statement_constructor_inventory :
    headerStatements.map Syn.ctor =
      [.blockStmt, .simpleStmt, .ifStmt, .forStmt, .whileStmt, .doWhile,
       .continueStmt, .breakStmt, .tryStmt, .returnStmt, .emit, .revert, .assembly] := rfl

theorem header_all_statement_constructors_checked :
    headerStatements.length = 13 ∧
    headerStatements.all (fun s => headerWitnessCheck (.block (.cons (.stmtItem s) .nil)) []) = true := by
  decide +kernel

theorem header_both_item_forms_checked :
    headerWitnessCheck (Syn.block (k := .body) (.cons (.stmtItem (.returnStmt .none)) .nil)) [] = true ∧
    headerWitnessCheck (Syn.block (k := .body) (.cons (.uncheckedItem (.block .nil)) .nil)) [] = true := by
  decide +kernel

def simpleHeaderStatements : List (Syn (.stmt .body)) :=
  [.simpleStmt (.exprStmt (.cond (.ident "a") (.ident "b") (.ident "c"))),
   .simpleStmt (.declVar (.varDecl (.userType ⟨"T", []⟩) .none "x") (.some (.ident "v"))),
   .simpleStmt (.declTuple 1 (.varDecl (.elem .bool) .none "x") (.cons .none .nil) (.ident "v"))]

theorem header_all_simple_alternatives_checked :
    simpleHeaderStatements.length = 3 ∧
    simpleHeaderStatements.all (fun s => headerWitnessCheck (.block (.cons (.stmtItem s) .nil)) []) = true := by
  decide +kernel

def headerLayoutBlock : Syn (.block .body) :=
  .block (.cons (.stmtItem (.simpleStmt (.declVar
    (.varDecl (.fnType .nil (.some .internal) (.some .view) .nil) .none "fp") .none)))
    (.cons (.stmtItem (.simpleStmt (.exprStmt (.lit (.str [103,97,115,58]))))) .nil))

theorem header_actual_attribute_fragment_layout_checked :
    headerWitnessCheck headerLayoutBlock [.attrs [.mutab,.vis], .frags [1,3]] = true ∧
    headerWitnessCheck headerLayoutBlock [] = false := by decide +kernel

theorem header_literal_payload_is_atomic :
    headerWitnessCheck (Syn.block (k := .body)
      (.cons (.stmtItem (.simpleStmt (.exprStmt (.lit (.str [103,97,115,58]))))) .nil))
      [.frags [1,3]] = true := by decide +kernel

def headerRepeat (k : SCtx) : Nat → Syn (.list (.item k))
  | 0 => .nil
  | n + 1 => .cons (.stmtItem (.simpleStmt (.exprStmt (.ident "x")))) (headerRepeat k n)

theorem header_repeat_all (k : SCtx) (width : Nat) : (headerRepeat k width).all Syn.precNode = true := by
  induction width with
  | zero => rfl
  | succ width ih =>
    change (headerRepeat k width).all Syn.precNode = true
    exact ih

theorem header_repeat_prec (k : SCtx) (width : Nat) : (Syn.block (headerRepeat k width)).prec = true := by
  change (headerRepeat k width).all Syn.precNode = true
  exact header_repeat_all k width

theorem header_repeat_yield (k : SCtx) (width : Nat) (L : List Choice) :
    (headerRepeat k width).yield L = some (List.replicate width [.ident "x", .punct .semi], L) := by
  induction width with
  | zero => rfl
  | succ width ih =>
    exact list_yield_cons_of (.stmtItem (.simpleStmt (.exprStmt (.ident "x"))))
      (headerRepeat k width) L L L [[.ident "x", .punct .semi]] _ rfl ih

theorem header_arbitrary_width_postLoop (k : SCtx) (width n : Nat) (e : Syn .expr) (s : St) :
    postLoop (n + 1) e (blockInput (List.replicate width [.ident "x", .punct .semi]).flatten s) =
      .ok (e, blockInput (List.replicate width [.ident "x", .punct .semi]).flatten s) := by
  have yielded := block_yield_of_items (headerRepeat k width) [] [] _ (header_repeat_yield k width [])
  have parsed := postLoop_yielded_block (Syn.block (headerRepeat k width))
    (header_repeat_prec k width) [] [] _ yielded n e s
  simpa only [blockInput, List.flatten_cons, List.flatten_nil, List.append_nil] using parsed

def headerNested (k : SCtx) : Nat → Syn (.block k)
  | 0 => .block .nil
  | n + 1 => .block (.cons (.stmtItem (.blockStmt (headerNested k n))) .nil)

theorem header_arbitrary_depth_prec (k : SCtx) (depth : Nat) : (headerNested k depth).prec = true := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    have inside : (headerNested k depth).all Syn.precNode = true := by
      change ((headerNested k depth).precNode && (headerNested k depth).all Syn.precNode) = true at ih
      simp only [Bool.and_eq_true] at ih
      exact ih.2
    change ((headerNested k depth).all Syn.precNode && true) = true
    rw [inside]
    rfl

def optionWords : List Tok :=
  [.punct .lbrace, .ident "gas", .punct .colon, .bool true, .punct .rbrace,
   .punct .lparen, .punct .rparen]

theorem header_actual_call_options_consumed :
    postLoop 12 (.ident "left") (locatedInput optionWords ⟨[atToken (.punct .semi) 77 78], [], 99⟩) =
      .ok (.call (.callOptions (.ident "left") (.namedArg "gas" (.lit (.bool true))) .nil)
        (.positional .nil), ⟨[atToken (.punct .semi) 77 78], [], 99⟩) := by rfl

theorem header_named_pair_negative :
    namedArgStart [.ident "gas", .punct .colon, .bool true] = true ∧
    ¬ NoNamedFrame [.ident "gas"] := by
  refine ⟨rfl, ?_⟩
  intro bad
  have impossible := bad [.punct .colon]
  cases impossible

theorem header_empty_block_closing_brace :
    namedArgStart ((braces []).drop 1 ++ [.ident "gas", .punct .colon]) = false ∧
    headerWitnessCheck (Syn.block (k := .body) .nil) [] = true := by decide +kernel

def headerZeroFuelRefuses : Bool :=
  match postLoop 0 (.ident "left") (blockInput [] ⟨[], [], 0⟩) with
  | .error _ => true
  | .ok _ => false

theorem header_zero_fuel_rejected : headerZeroFuelRefuses = true := by decide +kernel

theorem header_invalid_revert_contract :
    (Syn.revert (k := .body) (.lit (.bool true)) (.positional .nil)).precNode = false := rfl

theorem header_colon_suffix_nonident_stop (n : Nat) (e : Syn .expr) (s : St) :
    postLoop (n + 1) e (blockInput [] (locatedInput [.punct .colon] s)) =
      .ok (e, blockInput [] (locatedInput [.punct .colon] s)) := by rfl

/-- info: 'Solidity.Frontend.StatementGrammarH28.header_all_statement_constructor_inventory' does not depend on any axioms -/
#guard_msgs in
#print axioms header_all_statement_constructor_inventory
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_all_statement_constructors_checked' does not depend on any axioms -/
#guard_msgs in
#print axioms header_all_statement_constructors_checked
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_both_item_forms_checked' does not depend on any axioms -/
#guard_msgs in
#print axioms header_both_item_forms_checked
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_all_simple_alternatives_checked' does not depend on any axioms -/
#guard_msgs in
#print axioms header_all_simple_alternatives_checked
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_actual_attribute_fragment_layout_checked' does not depend on any axioms -/
#guard_msgs in
#print axioms header_actual_attribute_fragment_layout_checked
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_literal_payload_is_atomic' does not depend on any axioms -/
#guard_msgs in
#print axioms header_literal_payload_is_atomic
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_repeat_all' does not depend on any axioms -/
#guard_msgs in
#print axioms header_repeat_all
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_repeat_prec' does not depend on any axioms -/
#guard_msgs in
#print axioms header_repeat_prec
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_repeat_yield' does not depend on any axioms -/
#guard_msgs in
#print axioms header_repeat_yield
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_arbitrary_width_postLoop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms header_arbitrary_width_postLoop
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_arbitrary_depth_prec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms header_arbitrary_depth_prec
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_actual_call_options_consumed' does not depend on any axioms -/
#guard_msgs in
#print axioms header_actual_call_options_consumed
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_named_pair_negative' does not depend on any axioms -/
#guard_msgs in
#print axioms header_named_pair_negative
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_empty_block_closing_brace' does not depend on any axioms -/
#guard_msgs in
#print axioms header_empty_block_closing_brace
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_zero_fuel_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms header_zero_fuel_rejected
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_invalid_revert_contract' does not depend on any axioms -/
#guard_msgs in
#print axioms header_invalid_revert_contract
/-- info: 'Solidity.Frontend.StatementGrammarH28.header_colon_suffix_nonident_stop' does not depend on any axioms -/
#guard_msgs in
#print axioms header_colon_suffix_nonident_stop

end Solidity.Frontend.StatementGrammarH28
