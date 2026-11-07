import Solidity.Frontend.StatementGrammarH28.SyntaxParenBalance
import Solidity.Source.Ctor

/-! Intrinsically indexed witnesses for every constructor in the79-case
statement dependency closure. This Sigma retains each existing Syn category;
it is test packaging, not an alternate AST. Kernel yields are not solc claims. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

abbrev ParenWitness := Σ c : Cat, Syn c × List Choice

def parenWitnessCheck (w : ParenWitness) : Bool :=
  match w.2.1.yield w.2.2 with
  | some (parts, []) => ParenBalanceCat w.1 &&
      (parenCloseSuffix 0 (parts.flatten ++ [.punct .rparen]) == some [])
  | _ => false

def parenWitnessNonempty (w : ParenWitness) : Bool :=
  match w.2.1.yield w.2.2 with
  | some (parts, []) => !parts.flatten.isEmpty
  | _ => false

def parenX : Syn .expr := .ident "x"
def parenY : Syn .expr := .ident "y"
def parenZ : Syn .expr := .ident "z"

def exprParenWitnesses : List (Syn .expr × List Choice) :=
  [(.index parenX (.some parenY), []),
   (.slice parenX (.some parenY) (.some parenZ), []),
   (.member parenX "f", []),
   (.callOptions parenX (.namedArg "gas" parenY) .nil, []),
   (.call parenX (.positional (.cons parenY .nil)), []),
   (.payableConv (.positional (.cons parenY .nil)), []),
   (.metaType (.userType ⟨"T", []⟩), []),
   (.unaryPrefix .neg parenX, []),
   (.unarySuffix .inc parenX, []),
   (.exp parenX parenY, []),
   (.mulDivMod .mul parenX parenY, []),
   (.addSub .add parenX parenY, []),
   (.shift .shl parenX parenY, []),
   (.bitAnd parenX parenY, []),
   (.bitXor parenX parenY, []),
   (.bitOr parenX parenY, []),
   (.order .lt parenX parenY, []),
   (.equality .eq parenX parenY, []),
   (.and parenX parenY, []),
   (.or parenX parenY, []),
   (.cond parenX parenY parenZ, []),
   (.assign .assign parenX parenY, []),
   (.new (.array (.elem .bool) .none), []),
   (.tuple (.some parenX) (.cons (.some parenY) .nil), []),
   (.inlineArray parenX (.cons parenY .nil), []),
   (.ident "x", []),
   (.lit (.bool true), []),
   (.litUnit (.dec 1 0 0) .wei, []),
   (.elemType .bool (by intro h; cases h), [])]

def typeParenWitnesses : List (Syn .typeName × List Choice) :=
  [(.elem .addressPayable, []),
   (.fnType .nil (.some .internal) (.some .view) .nil, [.attrs [.vis, .mutab]]),
   (.mapping (.elem .bool (by intro h; cases h)) (.some "key") (.elem .bool) (.some "value"), []),
   (.userType ⟨"T", ["U"]⟩, []),
   (.array (.elem .bool) (.some parenX), [])]

def argsParenWitnesses : List (Syn .callArgs × List Choice) :=
  [(.positional (.cons parenX .nil), []), (.named (.cons (.namedArg "x" parenY) .nil), [])]

def namedParenWitnesses : List (Syn .namedArg × List Choice) := [(.namedArg "x" parenY, [])]
def paramParenWitnesses : List (Syn .param × List Choice) :=
  [(.param (.elem .bool) .none (.some "x"), [])]
def varParenWitnesses : List (Syn .varDecl × List Choice) :=
  [(.varDecl (.elem .bool) .none "x", [])]
def simpleParenWitnesses : List (Syn .simple × List Choice) :=
  [(.declVar (.varDecl (.elem .bool) .none "x") .none, []),
   (.declTuple 1 (.varDecl (.elem .bool) .none "x") (.cons .none .nil) parenY, []),
   (.exprStmt parenX, [])]

def literalParenWitnesses : List (Syn .expr × List Choice) :=
  [(.lit (.bool true), []), (.lit (.num (.dec 1 0 0)), []),
   (.lit (.str []), [.frags [0]]), (.lit (.hexStr [125]), [.frags [1]]),
   (.lit (.unicodeStr [123, 125]), [.frags [1, 1]])]

def parenStatementWitnesses : List (Syn (.stmt ⟨true, false⟩) × Tok) :=
  [(.simpleStmt (.exprStmt (.ident "unchecked")), .ident "unchecked"),
   (.blockStmt (.block .nil), .punct .lbrace),
   (.ifStmt (.ident "p") (.returnStmt .none) .none, .kw .if_),
   (.forStmt .none .none .none (.breakStmt), .kw .for_),
   (.whileStmt (.ident "p") (.continueStmt), .kw .while_),
   (.doWhile (.breakStmt) (.ident "p"), .kw .do_),
   (.continueStmt, .kw .continue_),
   (.breakStmt, .kw .break_),
   (.tryStmt (.ident "g") .nil (.block .nil) (.catchPlain (.block .nil)) .nil, .kw .try_),
   (.returnStmt .none, .kw .return_),
   (.emit (.ident "E") (.positional .nil), .kw .emit),
   (.revert (.ident "Err") (.positional .nil), .ident "revert"),
   (.assembly false [] .nil, .kw .assembly)]


def atomParenWitnesses : List ParenWitness :=
  exprParenWitnesses.map (fun w => ⟨.expr, w⟩) ++
  typeParenWitnesses.map (fun w => ⟨.typeName, w⟩) ++
  argsParenWitnesses.map (fun w => ⟨.callArgs, w⟩) ++
  namedParenWitnesses.map (fun w => ⟨.namedArg, w⟩) ++
  paramParenWitnesses.map (fun w => ⟨.param, w⟩) ++
  varParenWitnesses.map (fun w => ⟨.varDecl, w⟩) ++
  simpleParenWitnesses.map (fun w => ⟨.simple, w⟩)

def statementParenWitnesses : List ParenWitness :=
  parenStatementWitnesses.map (fun w => ⟨.stmt ⟨true, false⟩, w.1, []⟩)

def otherParenWitnesses : List ParenWitness :=
  [⟨.list .expr, .nil, []⟩,
   ⟨.list .expr, .cons (.ident "x") .nil, []⟩,
   ⟨.opt .expr, .none, []⟩,
   ⟨.opt .expr, .some (.ident "x"), []⟩,
   ⟨.block ⟨true,false⟩, .block .nil, []⟩,
   ⟨.item ⟨true,false⟩, .stmtItem (.returnStmt .none), []⟩,
   ⟨.item ⟨true,false⟩, .uncheckedItem (.block .nil), []⟩,
   ⟨.catchClause ⟨true,false⟩, .catchPlain (.block .nil), []⟩,
   ⟨.catchClause ⟨true,false⟩,
     .catchSig (.some "Error") (.param (.elem .bool) .none .none) .nil (.block .nil), []⟩,
   ⟨.yulStmt, .yulBlock .nil, []⟩,
   ⟨.yulStmt, .yulLet "x" ["y"] (.some (.yulLit (.dec 1))), []⟩,
   ⟨.yulStmt, .yulAssign ["x"] [["y"]] (.yulLit (.dec 1)), []⟩,
   ⟨.yulStmt, .yulExprStmt (.yulCall "f" .nil), []⟩,
   ⟨.yulStmt, .yulIf (.yulLit (.bool true)) .nil, []⟩,
   ⟨.yulStmt, .yulFor .nil (.yulLit (.bool true)) .nil .nil, []⟩,
   ⟨.yulStmt, .yulSwitch (.yulPath "x" [])
     (.cons (.yulCase (.dec 0) .nil) .nil) (.some .nil), []⟩,
   ⟨.yulCase, .yulCase (.dec 0) .nil, []⟩,
   ⟨.yulStmt, .yulLeave, []⟩, ⟨.yulStmt, .yulBreak, []⟩,
   ⟨.yulStmt, .yulContinue, []⟩,
   ⟨.yulStmt, .yulFun "f" ["x"] ["r"] .nil, []⟩,
   ⟨.yulExpr, .yulPath "x" ["y"], []⟩,
   ⟨.yulExpr, .yulCall "f" (.cons (.yulLit (.dec 1)) .nil), []⟩,
   ⟨.yulExpr, .yulLit (.dec 1), []⟩]

def allParenWitnesses : List ParenWitness :=
  atomParenWitnesses ++ statementParenWitnesses ++ otherParenWitnesses

theorem all_atom_parenthesis_controls : atomParenWitnesses.all parenWitnessCheck = true := by
  decide +kernel

theorem all_statement_parenthesis_controls :
    statementParenWitnesses.all parenWitnessCheck = true := by decide +kernel

theorem all_other_parenthesis_controls : otherParenWitnesses.all parenWitnessCheck = true := by
  decide +kernel

theorem all_seventy_nine_parenthesis_controls :
    allParenWitnesses.all parenWitnessCheck = true := by
  simp only [allParenWitnesses, List.all_append, all_atom_parenthesis_controls,
    all_statement_parenthesis_controls, all_other_parenthesis_controls, Bool.and_self]

def parenthesisConstructorInventory : List Ctor :=
  [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order, .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit, .elemType, .elem, .fnType, .mapping, .userType, .array, .positional, .named, .namedArg, .param, .varDecl, .declVar, .declTuple, .exprStmt, .simpleStmt, .blockStmt, .ifStmt, .forStmt, .whileStmt, .doWhile, .continueStmt, .breakStmt, .tryStmt, .returnStmt, .emit, .revert, .assembly, .nil, .cons, .none, .some, .block, .stmtItem, .uncheckedItem, .catchPlain, .catchSig, .yulBlock, .yulLet, .yulAssign, .yulExprStmt, .yulIf, .yulFor, .yulSwitch, .yulCase, .yulLeave, .yulBreak, .yulContinue, .yulFun, .yulPath, .yulCall, .yulLit]

theorem actual_seventy_nine_constructor_inventory :
    allParenWitnesses.map (fun w => w.2.1.ctor) = parenthesisConstructorInventory := by
  decide +kernel

theorem seventy_nine_distinct_constructors :
    parenthesisConstructorInventory.length = 79 ∧
    parenthesisConstructorInventory.eraseDups.length = 79 := by decide +kernel

theorem inhabited_nonempty_controls :
    (allParenWitnesses.filter parenWitnessNonempty).length = 77 := by decide +kernel

theorem all_five_literal_parenthesis_variants :
    (literalParenWitnesses.map (fun w => (⟨.expr, w⟩ : ParenWitness))).all
      parenWitnessCheck = true := by decide +kernel

theorem literal_parentheses_are_payload :
    (Syn.lit (.str [41,40,41])).yield [.frags [1,2]] =
      some ([[.str [41], .str [40,41]]], []) ∧
    parenHeaderSuffix (parens [.str [41], .str [40,41]] ++ [.ident "tail"]) =
      some [.ident "tail"] := by decide +kernel

theorem no_standalone_open_parenthesis : ¬ ParenBalanced [.punct .lparen] := by
  intro h
  have frame := parenBalanced_scan_frame h 0 [.punct .rparen]
  cases frame

theorem no_standalone_close_parenthesis : ¬ ParenBalanced [.punct .rparen] := by
  intro h
  have frame := parenBalanced_scan_frame h 0 []
  cases frame

theorem malformed_header_controls :
    parenHeaderSuffix [] = none ∧
    parenHeaderSuffix [.punct .rparen] = none ∧
    parenHeaderSuffix [.punct .lparen] = none ∧
    parenHeaderSuffix [.punct .lparen, .punct .rparen, .punct .rparen] =
      some [.punct .rparen] := by decide +kernel

theorem universal_actual_header_suffix {c : Cat} (s : Syn c)
    (hc : ParenBalanceCat c = true) (L M : List Choice) (parts : List (List Tok))
    (tail : List Tok) (hy : s.yield L = some (parts, M)) :
    parenHeaderSuffix (parens parts.flatten ++ tail) = some tail :=
  syntax_parenthesis_header_suffix s hc L M parts tail hy

theorem arbitrary_expression_header_split (e f : Syn .expr)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (he : e.yield L = some (xs,M)) (hf : f.yield N = some (ys,P))
    (tokens : parens xs.flatten ++ rest = parens ys.flatten ++ tail) :
    xs.flatten = ys.flatten ∧ rest = tail :=
  expression_parenthesis_header_split e f L M N P xs ys rest tail he hf tokens

def assemblyParenPayload : Syn (.stmt .body) :=
  .assembly true ["(", ")"]
    (.cons (.yulExprStmt (.yulCall "f" (.cons (.yulLit (.str [41,40])) .nil))) .nil)

theorem assembly_flags_and_yul_parentheses :
    parenWitnessCheck ⟨.stmt .body, assemblyParenPayload, []⟩ = true := by decide +kernel

def nestedArrayParenType : Syn .typeName :=
  .array (.elem .bool) (.some (.lit (.num (.dec 1 0 0))))

def nestedFunctionParenType : Syn .typeName :=
  .fnType
    (.cons (.param nestedArrayParenType (.some .memory) (.some "x")) .nil)
    (.some .external) (.some .pure)
    (.cons (.param (.elem .bool) .none .none) .nil)

theorem function_type_attributes_and_returns_parentheses :
    parenWitnessCheck ⟨.typeName, nestedFunctionParenType, [.attrs [.mutab, .vis]]⟩ = true := by
  decide +kernel

#print axioms all_atom_parenthesis_controls
#print axioms all_statement_parenthesis_controls
#print axioms all_other_parenthesis_controls
#print axioms all_seventy_nine_parenthesis_controls
#print axioms actual_seventy_nine_constructor_inventory
#print axioms seventy_nine_distinct_constructors
#print axioms inhabited_nonempty_controls
#print axioms all_five_literal_parenthesis_variants
#print axioms literal_parentheses_are_payload
#print axioms no_standalone_open_parenthesis
#print axioms no_standalone_close_parenthesis
#print axioms malformed_header_controls
#print axioms universal_actual_header_suffix
#print axioms arbitrary_expression_header_split
#print axioms assembly_flags_and_yul_parentheses
#print axioms function_type_attributes_and_returns_parentheses
end Solidity.Frontend.StatementGrammarH28
