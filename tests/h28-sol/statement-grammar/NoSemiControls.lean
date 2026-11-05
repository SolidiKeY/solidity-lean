import Solidity.Frontend.StatementGrammarH28.FramedStatementList
import Solidity.Source.Ctor

/-! All 42 atomic constructors have actual successful nonempty semicolon-free
yield controls; literal payload bytes containing semicolons remain tokens. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def semiWitnessCheck {c : Cat} (w : Syn c × List Choice) : Bool :=
  match w.1.yield w.2 with
  | some (parts, []) => !parts.flatten.isEmpty &&
      parts.flatten.all (fun tok => tok != .punct .semi)
  | _ => false

def semiX : Syn .expr := .ident "x"
def semiY : Syn .expr := .ident "y"
def semiZ : Syn .expr := .ident "z"

def exprSemiWitnesses : List (Syn .expr × List Choice) :=
  [(.index semiX (.some semiY), []),
   (.slice semiX (.some semiY) (.some semiZ), []),
   (.member semiX "f", []),
   (.callOptions semiX (.namedArg "gas" semiY) .nil, []),
   (.call semiX (.positional (.cons semiY .nil)), []),
   (.payableConv (.positional (.cons semiY .nil)), []),
   (.metaType (.userType ⟨"T", []⟩), []),
   (.unaryPrefix .neg semiX, []),
   (.unarySuffix .inc semiX, []),
   (.exp semiX semiY, []),
   (.mulDivMod .mul semiX semiY, []),
   (.addSub .add semiX semiY, []),
   (.shift .shl semiX semiY, []),
   (.bitAnd semiX semiY, []),
   (.bitXor semiX semiY, []),
   (.bitOr semiX semiY, []),
   (.order .lt semiX semiY, []),
   (.equality .eq semiX semiY, []),
   (.and semiX semiY, []),
   (.or semiX semiY, []),
   (.cond semiX semiY semiZ, []),
   (.assign .assign semiX semiY, []),
   (.new (.array (.elem .bool) .none), []),
   (.tuple (.some semiX) (.cons (.some semiY) .nil), []),
   (.inlineArray semiX (.cons semiY .nil), []),
   (.ident "x", []),
   (.lit (.bool true), []),
   (.litUnit (.dec 1 0 0) .wei, []),
   (.elemType .bool (by intro h; cases h), [])]

def typeSemiWitnesses : List (Syn .typeName × List Choice) :=
  [(.elem .addressPayable, []),
   (.fnType .nil (.some .internal) (.some .view) .nil, [.attrs [.vis, .mutab]]),
   (.mapping (.elem .bool (by intro h; cases h)) (.some "key") (.elem .bool) (.some "value"), []),
   (.userType ⟨"T", ["U"]⟩, []),
   (.array (.elem .bool) (.some semiX), [])]

def argsSemiWitnesses : List (Syn .callArgs × List Choice) :=
  [(.positional (.cons semiX .nil), []), (.named (.cons (.namedArg "x" semiY) .nil), [])]

def namedSemiWitnesses : List (Syn .namedArg × List Choice) := [(.namedArg "x" semiY, [])]
def paramSemiWitnesses : List (Syn .param × List Choice) :=
  [(.param (.elem .bool) .none (.some "x"), [])]
def varSemiWitnesses : List (Syn .varDecl × List Choice) :=
  [(.varDecl (.elem .bool) .none "x", [])]
def simpleSemiWitnesses : List (Syn .simple × List Choice) :=
  [(.declVar (.varDecl (.elem .bool) .none "x") .none, []),
   (.declTuple 1 (.varDecl (.elem .bool) .none "x") (.cons .none .nil) semiY, []),
   (.exprStmt semiX, [])]

def literalSemiWitnesses : List (Syn .expr × List Choice) :=
  [(.lit (.bool true), []), (.lit (.num (.dec 1 0 0)), []),
   (.lit (.str []), [.frags [0]]), (.lit (.hexStr [125]), [.frags [1]]),
   (.lit (.unicodeStr [123, 125]), [.frags [1, 1]])]

theorem all_semi_constructor_witnesses_checked :
    exprSemiWitnesses.all semiWitnessCheck = true ∧
    typeSemiWitnesses.all semiWitnessCheck = true ∧
    argsSemiWitnesses.all semiWitnessCheck = true ∧
    namedSemiWitnesses.all semiWitnessCheck = true ∧
    paramSemiWitnesses.all semiWitnessCheck = true ∧
    varSemiWitnesses.all semiWitnessCheck = true ∧
    simpleSemiWitnesses.all semiWitnessCheck = true ∧
    literalSemiWitnesses.all semiWitnessCheck = true := by decide +kernel

theorem semicolon_payload_is_atomic :
    (Syn.lit (.str [59, 59])).yield [.frags [1, 1]] =
      some ([[.str [59], .str [59]]], []) := by decide +kernel

theorem no_semicolon_token : ¬ SemiFree [.punct .semi] := by
  intro h
  have scan := semiFree_scan_frame h []
  cases scan

theorem empty_fragment_choice_refused :
    (Syn.lit (.str [])).yield [.frags []] = none := by decide +kernel

theorem wrong_layout_choice_refused :
    (Syn.lit (.str [59])).yield [.attrs []] = none := by decide +kernel

theorem list_option_yield_controls :
    (Syn.nil : Syn (.list .expr)).yield [] = some ([], []) ∧
    (Syn.cons (.ident "x") .nil).yield [] = some ([[.ident "x"]], []) ∧
    (Syn.none : Syn (.opt .expr)).yield [] = some ([], []) ∧
    (Syn.some (.ident "x")).yield [] = some ([[.ident "x"]], []) := by decide +kernel

theorem exprSemiWitnesses_inventory :
    exprSemiWitnesses.map (fun w => w.1.ctor) =
      [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order, .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit, .elemType] := rfl

theorem typeSemiWitnesses_inventory :
    typeSemiWitnesses.map (fun w => w.1.ctor) =
      [.elem, .fnType, .mapping, .userType, .array] := rfl

theorem argsSemiWitnesses_inventory :
    argsSemiWitnesses.map (fun w => w.1.ctor) =
      [.positional, .named] := rfl

theorem namedSemiWitnesses_inventory :
    namedSemiWitnesses.map (fun w => w.1.ctor) =
      [.namedArg] := rfl

theorem paramSemiWitnesses_inventory :
    paramSemiWitnesses.map (fun w => w.1.ctor) =
      [.param] := rfl

theorem varSemiWitnesses_inventory :
    varSemiWitnesses.map (fun w => w.1.ctor) =
      [.varDecl] := rfl

theorem simpleSemiWitnesses_inventory :
    simpleSemiWitnesses.map (fun w => w.1.ctor) =
      [.declVar, .declTuple, .exprStmt] := rfl

theorem semi_constructor_count :
    exprSemiWitnesses.length + typeSemiWitnesses.length + argsSemiWitnesses.length + namedSemiWitnesses.length + paramSemiWitnesses.length + varSemiWitnesses.length + simpleSemiWitnesses.length = 42 := rfl

#print axioms all_semi_constructor_witnesses_checked
#print axioms semi_constructor_count
#print axioms exprSemiWitnesses_inventory
#print axioms typeSemiWitnesses_inventory
#print axioms argsSemiWitnesses_inventory
#print axioms namedSemiWitnesses_inventory
#print axioms paramSemiWitnesses_inventory
#print axioms varSemiWitnesses_inventory
#print axioms simpleSemiWitnesses_inventory
#print axioms semicolon_payload_is_atomic
#print axioms no_semicolon_token
#print axioms empty_fragment_choice_refused
#print axioms wrong_layout_choice_refused
#print axioms list_option_yield_controls
end Solidity.Frontend.StatementGrammarH28
