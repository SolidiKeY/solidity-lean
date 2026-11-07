import Solidity.Frontend.StatementGrammarH28.SyntaxControlFree
import Solidity.Source.Ctor

/-! All42 atom constructors have actual inhabited successful nonempty yields;
continuation spellings inside identifiers/literals are data, actual keyword
tokens are rejected. List/option closure and real layout refusals retained. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def controlWitnessCheck {c : Cat} (w : Syn c × List Choice) : Bool :=
  match w.1.yield w.2 with
  | some (parts, []) => !parts.flatten.isEmpty &&
      parts.flatten.all (fun tok => !boundaryToken tok)
  | _ => false

def controlX : Syn .expr := .ident "x"
def controlY : Syn .expr := .ident "y"
def controlZ : Syn .expr := .ident "z"

def exprControlWitnesses : List (Syn .expr × List Choice) :=
  [(.index controlX (.some controlY), []),
   (.slice controlX (.some controlY) (.some controlZ), []),
   (.member controlX "f", []),
   (.callOptions controlX (.namedArg "gas" controlY) .nil, []),
   (.call controlX (.positional (.cons controlY .nil)), []),
   (.payableConv (.positional (.cons controlY .nil)), []),
   (.metaType (.userType ⟨"T", []⟩), []),
   (.unaryPrefix .neg controlX, []),
   (.unarySuffix .inc controlX, []),
   (.exp controlX controlY, []),
   (.mulDivMod .mul controlX controlY, []),
   (.addSub .add controlX controlY, []),
   (.shift .shl controlX controlY, []),
   (.bitAnd controlX controlY, []),
   (.bitXor controlX controlY, []),
   (.bitOr controlX controlY, []),
   (.order .lt controlX controlY, []),
   (.equality .eq controlX controlY, []),
   (.and controlX controlY, []),
   (.or controlX controlY, []),
   (.cond controlX controlY controlZ, []),
   (.assign .assign controlX controlY, []),
   (.new (.array (.elem .bool) .none), []),
   (.tuple (.some controlX) (.cons (.some controlY) .nil), []),
   (.inlineArray controlX (.cons controlY .nil), []),
   (.ident "x", []),
   (.lit (.bool true), []),
   (.litUnit (.dec 1 0 0) .wei, []),
   (.elemType .bool (by intro h; cases h), [])]

def typeControlWitnesses : List (Syn .typeName × List Choice) :=
  [(.elem .addressPayable, []),
   (.fnType .nil (.some .internal) (.some .view) .nil, [.attrs [.vis, .mutab]]),
   (.mapping (.elem .bool (by intro h; cases h)) (.some "key") (.elem .bool) (.some "value"), []),
   (.userType ⟨"T", ["U"]⟩, []),
   (.array (.elem .bool) (.some controlX), [])]

def argsControlWitnesses : List (Syn .callArgs × List Choice) :=
  [(.positional (.cons controlX .nil), []), (.named (.cons (.namedArg "x" controlY) .nil), [])]

def namedControlWitnesses : List (Syn .namedArg × List Choice) := [(.namedArg "x" controlY, [])]
def paramControlWitnesses : List (Syn .param × List Choice) :=
  [(.param (.elem .bool) .none (.some "x"), [])]
def varControlWitnesses : List (Syn .varDecl × List Choice) :=
  [(.varDecl (.elem .bool) .none "x", [])]
def simpleControlWitnesses : List (Syn .simple × List Choice) :=
  [(.declVar (.varDecl (.elem .bool) .none "x") .none, []),
   (.declTuple 1 (.varDecl (.elem .bool) .none "x") (.cons .none .nil) controlY, []),
   (.exprStmt controlX, [])]

def literalControlWitnesses : List (Syn .expr × List Choice) :=
  [(.lit (.bool true), []), (.lit (.num (.dec 1 0 0)), []),
   (.lit (.str []), [.frags [0]]), (.lit (.hexStr [125]), [.frags [1]]),
   (.lit (.unicodeStr [123, 125]), [.frags [1, 1]])]

theorem all_control_constructor_witnesses_checked :
    exprControlWitnesses.all controlWitnessCheck = true ∧
    typeControlWitnesses.all controlWitnessCheck = true ∧
    argsControlWitnesses.all controlWitnessCheck = true ∧
    namedControlWitnesses.all controlWitnessCheck = true ∧
    paramControlWitnesses.all controlWitnessCheck = true ∧
    varControlWitnesses.all controlWitnessCheck = true ∧
    simpleControlWitnesses.all controlWitnessCheck = true ∧
    literalControlWitnesses.all controlWitnessCheck = true := by decide +kernel

theorem control_literal_payload_is_atomic :
    (Syn.lit (.str [59, 59])).yield [.frags [1, 1]] =
      some ([[.str [59], .str [59]]], []) := by decide +kernel

theorem no_continuation_token (k : Kw) (hb : boundaryToken (.kw k) = true) :
    ¬ ControlFree [.kw k] := by
  intro h
  exact controlFree_no_boundary h (.kw k) hb (.head _)

theorem all_continuation_tokens_rejected :
    ¬ ControlFree [.kw .else_] ∧ ¬ ControlFree [.kw .catch_] ∧ ¬ ControlFree [.kw .unchecked] :=
  ⟨no_continuation_token _ rfl, no_continuation_token _ rfl, no_continuation_token _ rfl⟩

theorem semicolon_is_not_control_keyword : ControlFree [.punct .semi] :=
  controlFree_punct .semi

theorem control_empty_fragment_choice_refused :
    (Syn.lit (.str [])).yield [.frags []] = none := by decide +kernel

theorem control_wrong_layout_choice_refused :
    (Syn.lit (.str [59])).yield [.attrs []] = none := by decide +kernel

theorem control_list_option_yield_controls :
    (Syn.nil : Syn (.list .expr)).yield [] = some ([], []) ∧
    (Syn.cons (.ident "x") .nil).yield [] = some ([[.ident "x"]], []) ∧
    (Syn.none : Syn (.opt .expr)).yield [] = some ([], []) ∧
    (Syn.some (.ident "x")).yield [] = some ([[.ident "x"]], []) := by decide +kernel

theorem exprControlWitnesses_inventory :
    exprControlWitnesses.map (fun w => w.1.ctor) =
      [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order, .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit, .elemType] := rfl

theorem typeControlWitnesses_inventory :
    typeControlWitnesses.map (fun w => w.1.ctor) =
      [.elem, .fnType, .mapping, .userType, .array] := rfl

theorem argsControlWitnesses_inventory :
    argsControlWitnesses.map (fun w => w.1.ctor) =
      [.positional, .named] := rfl

theorem namedControlWitnesses_inventory :
    namedControlWitnesses.map (fun w => w.1.ctor) =
      [.namedArg] := rfl

theorem paramControlWitnesses_inventory :
    paramControlWitnesses.map (fun w => w.1.ctor) =
      [.param] := rfl

theorem varControlWitnesses_inventory :
    varControlWitnesses.map (fun w => w.1.ctor) =
      [.varDecl] := rfl

theorem simpleControlWitnesses_inventory :
    simpleControlWitnesses.map (fun w => w.1.ctor) =
      [.declVar, .declTuple, .exprStmt] := rfl

theorem control_constructor_count :
    exprControlWitnesses.length + typeControlWitnesses.length + argsControlWitnesses.length + namedControlWitnesses.length + paramControlWitnesses.length + varControlWitnesses.length + simpleControlWitnesses.length = 42 := rfl

def keywordPayloadWitnesses : List (Syn .expr × List Choice) :=
  [(.lit (.str [101,108,115,101]), [.frags [4]]),
   (.lit (.str [99,97,116,99,104]), [.frags [2,3]]),
   (.lit (.unicodeStr [117,110,99,104,101,99,107,101,100]), [.frags [9]])]

theorem keyword_payloads_are_atomic : keywordPayloadWitnesses.all controlWitnessCheck = true := by
  decide +kernel

theorem keyword_spelling_identifiers_are_data :
    ControlFree (idt "else" ++ idt "catch" ++ idt "unchecked") :=
  .append (.append (controlFree_id _) (controlFree_id _)) (controlFree_id _)

theorem both_function_attribute_orders :
    controlWitnessCheck ((Syn.fnType .nil (.some .internal) (.some .view) .nil), [.attrs [.vis, .mutab]]) = true ∧
    controlWitnessCheck ((Syn.fnType .nil (.some .internal) (.some .view) .nil), [.attrs [.mutab, .vis]]) = true := by
  decide +kernel

def actualIfElseWords : List Tok :=
  [.kw .if_, .punct .lparen, .bool true, .punct .rparen,
   .punct .lbrace, .punct .rbrace, .kw .else_, .punct .lbrace, .punct .rbrace]

theorem actual_if_else_yield :
    (Syn.ifStmt (k := .body) (.lit (.bool true)) (.blockStmt (.block .nil))
      (.some (.blockStmt (.block .nil)))).toks [] = some actualIfElseWords := by rfl

theorem actual_if_else_is_not_atomic : ¬ ControlFree actualIfElseWords := by
  intro h
  exact controlFree_no_boundary h (.kw .else_) rfl (by decide)

theorem arbitrary_expression_continuations_absent (e : Syn .expr) (L M : List Choice)
    (parts : List (List Tok)) (hy : e.yield L = some (parts, M)) :
    Tok.kw .else_ ∉ parts.flatten ∧ Tok.kw .catch_ ∉ parts.flatten ∧
      Tok.kw .unchecked ∉ parts.flatten :=
  ⟨syntax_yield_no_continuations e rfl L M parts hy _ rfl,
   syntax_yield_no_continuations e rfl L M parts hy _ rfl,
   syntax_yield_no_continuations e rfl L M parts hy _ rfl⟩

theorem other_atom_clause_controls :
    controlWitnessCheck ((Syn.mapping (.path ⟨"catch", ["unchecked"]⟩) .none (.elem .bool) .none), []) = true ∧
    controlWitnessCheck ((Syn.array (.elem .bool) .none), []) = true ∧
    controlWitnessCheck ((Syn.positional .nil), []) = true ∧
    controlWitnessCheck ((Syn.named .nil), []) = true ∧
    controlWitnessCheck ((Syn.tuple .none .nil), []) = true ∧
    controlWitnessCheck ((Syn.param (.elem .bool) (.some .memory) (.some "else")), []) = true ∧
    controlWitnessCheck ((Syn.varDecl (.elem .bool) (.some .calldata) "unchecked"), []) = true ∧
    controlWitnessCheck ((Syn.declVar (.varDecl (.elem .bool) .none "x") (.some (.ident "y"))), []) = true := by
  decide +kernel

#print axioms other_atom_clause_controls

#print axioms keyword_payloads_are_atomic
#print axioms keyword_spelling_identifiers_are_data
#print axioms both_function_attribute_orders
#print axioms actual_if_else_yield
#print axioms actual_if_else_is_not_atomic
#print axioms arbitrary_expression_continuations_absent

#print axioms all_control_constructor_witnesses_checked
#print axioms control_constructor_count
#print axioms exprControlWitnesses_inventory
#print axioms typeControlWitnesses_inventory
#print axioms argsControlWitnesses_inventory
#print axioms namedControlWitnesses_inventory
#print axioms paramControlWitnesses_inventory
#print axioms varControlWitnesses_inventory
#print axioms simpleControlWitnesses_inventory
#print axioms control_literal_payload_is_atomic
#print axioms no_continuation_token
#print axioms all_continuation_tokens_rejected
#print axioms semicolon_is_not_control_keyword
#print axioms control_empty_fragment_choice_refused
#print axioms control_wrong_layout_choice_refused
#print axioms control_list_option_yield_controls
end Solidity.Frontend.StatementGrammarH28
