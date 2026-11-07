import Solidity.Frontend.StatementGrammarH28.FramedItemList
import Solidity.Source.Ctor

/-! Actual successful yield controls for all42 atom constructors, five literal
variants and all13 statement roots. Keywords and identifier payloads differ. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def boundaryWitnessCheck {c : Cat} (w : Syn c × List Choice) : Bool :=
  match w.1.yield w.2 with
  | some (parts, []) => match parts.flatten.head? with
      | some tok => !boundaryToken tok
      | none => false
  | _ => false

def boundaryX : Syn .expr := .ident "x"
def boundaryY : Syn .expr := .ident "y"
def boundaryZ : Syn .expr := .ident "z"

def exprBoundaryWitnesses : List (Syn .expr × List Choice) :=
  [(.index boundaryX (.some boundaryY), []),
   (.slice boundaryX (.some boundaryY) (.some boundaryZ), []),
   (.member boundaryX "f", []),
   (.callOptions boundaryX (.namedArg "gas" boundaryY) .nil, []),
   (.call boundaryX (.positional (.cons boundaryY .nil)), []),
   (.payableConv (.positional (.cons boundaryY .nil)), []),
   (.metaType (.userType ⟨"T", []⟩), []),
   (.unaryPrefix .neg boundaryX, []),
   (.unarySuffix .inc boundaryX, []),
   (.exp boundaryX boundaryY, []),
   (.mulDivMod .mul boundaryX boundaryY, []),
   (.addSub .add boundaryX boundaryY, []),
   (.shift .shl boundaryX boundaryY, []),
   (.bitAnd boundaryX boundaryY, []),
   (.bitXor boundaryX boundaryY, []),
   (.bitOr boundaryX boundaryY, []),
   (.order .lt boundaryX boundaryY, []),
   (.equality .eq boundaryX boundaryY, []),
   (.and boundaryX boundaryY, []),
   (.or boundaryX boundaryY, []),
   (.cond boundaryX boundaryY boundaryZ, []),
   (.assign .assign boundaryX boundaryY, []),
   (.new (.array (.elem .bool) .none), []),
   (.tuple (.some boundaryX) (.cons (.some boundaryY) .nil), []),
   (.inlineArray boundaryX (.cons boundaryY .nil), []),
   (.ident "x", []),
   (.lit (.bool true), []),
   (.litUnit (.dec 1 0 0) .wei, []),
   (.elemType .bool (by intro h; cases h), [])]

def typeBoundaryWitnesses : List (Syn .typeName × List Choice) :=
  [(.elem .addressPayable, []),
   (.fnType .nil (.some .internal) (.some .view) .nil, [.attrs [.vis, .mutab]]),
   (.mapping (.elem .bool (by intro h; cases h)) (.some "key") (.elem .bool) (.some "value"), []),
   (.userType ⟨"T", ["U"]⟩, []),
   (.array (.elem .bool) (.some boundaryX), [])]

def argsBoundaryWitnesses : List (Syn .callArgs × List Choice) :=
  [(.positional (.cons boundaryX .nil), []), (.named (.cons (.namedArg "x" boundaryY) .nil), [])]

def namedBoundaryWitnesses : List (Syn .namedArg × List Choice) := [(.namedArg "x" boundaryY, [])]
def paramBoundaryWitnesses : List (Syn .param × List Choice) :=
  [(.param (.elem .bool) .none (.some "x"), [])]
def varBoundaryWitnesses : List (Syn .varDecl × List Choice) :=
  [(.varDecl (.elem .bool) .none "x", [])]
def simpleBoundaryWitnesses : List (Syn .simple × List Choice) :=
  [(.declVar (.varDecl (.elem .bool) .none "x") .none, []),
   (.declTuple 1 (.varDecl (.elem .bool) .none "x") (.cons .none .nil) boundaryY, []),
   (.exprStmt boundaryX, [])]

def literalBoundaryWitnesses : List (Syn .expr × List Choice) :=
  [(.lit (.bool true), []), (.lit (.num (.dec 1 0 0)), []),
   (.lit (.str []), [.frags [0]]), (.lit (.hexStr [125]), [.frags [1]]),
   (.lit (.unicodeStr [123, 125]), [.frags [1, 1]])]

theorem all_boundary_constructor_witnesses_checked :
    exprBoundaryWitnesses.all boundaryWitnessCheck = true ∧
    typeBoundaryWitnesses.all boundaryWitnessCheck = true ∧
    argsBoundaryWitnesses.all boundaryWitnessCheck = true ∧
    namedBoundaryWitnesses.all boundaryWitnessCheck = true ∧
    paramBoundaryWitnesses.all boundaryWitnessCheck = true ∧
    varBoundaryWitnesses.all boundaryWitnessCheck = true ∧
    simpleBoundaryWitnesses.all boundaryWitnessCheck = true ∧
    literalBoundaryWitnesses.all boundaryWitnessCheck = true := by decide +kernel

theorem boundary_keyword_identifier_controls :
    boundaryToken (.kw .else_) = true ∧ boundaryToken (.kw .catch_) = true ∧
    boundaryToken (.kw .unchecked) = true ∧
    boundaryToken (.ident "else") = false ∧ boundaryToken (.ident "catch") = false ∧
    boundaryToken (.ident "unchecked") = false ∧ boundaryToken (.str [101,108,115,101]) = false := by
  decide +kernel

theorem exprBoundaryWitnesses_inventory :
    exprBoundaryWitnesses.map (fun w => w.1.ctor) =
      [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order, .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit, .elemType] := rfl

theorem typeBoundaryWitnesses_inventory :
    typeBoundaryWitnesses.map (fun w => w.1.ctor) =
      [.elem, .fnType, .mapping, .userType, .array] := rfl

theorem argsBoundaryWitnesses_inventory :
    argsBoundaryWitnesses.map (fun w => w.1.ctor) =
      [.positional, .named] := rfl

theorem namedBoundaryWitnesses_inventory :
    namedBoundaryWitnesses.map (fun w => w.1.ctor) =
      [.namedArg] := rfl

theorem paramBoundaryWitnesses_inventory :
    paramBoundaryWitnesses.map (fun w => w.1.ctor) =
      [.param] := rfl

theorem varBoundaryWitnesses_inventory :
    varBoundaryWitnesses.map (fun w => w.1.ctor) =
      [.varDecl] := rfl

theorem simpleBoundaryWitnesses_inventory :
    simpleBoundaryWitnesses.map (fun w => w.1.ctor) =
      [.declVar, .declTuple, .exprStmt] := rfl

theorem boundary_constructor_count :
    exprBoundaryWitnesses.length + typeBoundaryWitnesses.length + argsBoundaryWitnesses.length + namedBoundaryWitnesses.length + paramBoundaryWitnesses.length + varBoundaryWitnesses.length + simpleBoundaryWitnesses.length = 42 := rfl

def continuationRootControls : List (Syn (.stmt ⟨true, false⟩) × Tok) :=
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

def continuationRootCheck (w : Syn (.stmt ⟨true, false⟩) × Tok) : Bool :=
  match w.1.yield [] with
  | some (parts, []) => parts.flatten.head? == some w.2 && !boundaryToken w.2
  | _ => false

theorem all_thirteen_continuation_roots_checked :
    continuationRootControls.length = 13 ∧
    continuationRootControls.all continuationRootCheck = true := by decide +kernel

theorem actual_thirteen_roots_inventory :
    continuationRootControls.map (fun w => root w.1) =
      [.simple, .block, .conditional, .forLoop, .whileLoop, .doLoop, .continueLoop,
       .breakLoop, .tryCatch, .returnValue, .emitEvent, .revertError, .assembly] := rfl

theorem arbitrary_statement_else_catch_unchecked_refusal {k : SCtx} (s : Syn (.stmt k))
    (L M : List Choice) (parts : List (List Tok)) (tail : List Tok)
    (hy : s.yield L = some (parts, M)) :
    (parts.flatten ++ tail).head? ≠ some (.kw .else_) ∧
    (parts.flatten ++ tail).head? ≠ some (.kw .catch_) ∧
    (parts.flatten ++ tail).head? ≠ some (.kw .unchecked) :=
  ⟨statement_boundary_prefix_refusal s L M parts tail _ hy rfl,
   statement_boundary_prefix_refusal s L M parts tail _ hy rfl,
   statement_boundary_prefix_refusal s L M parts tail _ hy rfl⟩

theorem invalid_empty_fragments_still_refused :
    (Syn.lit (.str [])).yield [.frags []] = none := by decide +kernel

#print axioms all_boundary_constructor_witnesses_checked
#print axioms boundary_keyword_identifier_controls
#print axioms exprBoundaryWitnesses_inventory
#print axioms typeBoundaryWitnesses_inventory
#print axioms argsBoundaryWitnesses_inventory
#print axioms namedBoundaryWitnesses_inventory
#print axioms paramBoundaryWitnesses_inventory
#print axioms varBoundaryWitnesses_inventory
#print axioms simpleBoundaryWitnesses_inventory
#print axioms boundary_constructor_count
#print axioms all_thirteen_continuation_roots_checked
#print axioms actual_thirteen_roots_inventory
#print axioms arbitrary_statement_else_catch_unchecked_refusal
#print axioms invalid_empty_fragments_still_refused
end Solidity.Frontend.StatementGrammarH28
