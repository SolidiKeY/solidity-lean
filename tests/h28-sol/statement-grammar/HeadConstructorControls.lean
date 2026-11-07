import Solidity.Frontend.StatementGrammarH28.RootHead
import Solidity.Source.Ctor

/-! Constructor-complete nonempty actual printer controls for the seven
nontrivial HeadInvariant categories. These are kernel yield checks, not solc
semantic acceptance or expression uniqueness claims. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def headWitnessCheck {c : Cat} (w : Syn c × List Choice) : Bool :=
  match w.1.yield w.2 with
  | some (parts, []) => match parts.flatten.head? with
      | some tok => !hardStatementToken tok
      | none => false
  | _ => false

def headX : Syn .expr := .ident "x"
def headY : Syn .expr := .ident "y"
def headZ : Syn .expr := .ident "z"

def exprHeadWitnesses : List (Syn .expr × List Choice) :=
  [(.index headX (.some headY), []),
   (.slice headX (.some headY) (.some headZ), []),
   (.member headX "f", []),
   (.callOptions headX (.namedArg "gas" headY) .nil, []),
   (.call headX (.positional (.cons headY .nil)), []),
   (.payableConv (.positional (.cons headY .nil)), []),
   (.metaType (.userType ⟨"T", []⟩), []),
   (.unaryPrefix .neg headX, []),
   (.unarySuffix .inc headX, []),
   (.exp headX headY, []),
   (.mulDivMod .mul headX headY, []),
   (.addSub .add headX headY, []),
   (.shift .shl headX headY, []),
   (.bitAnd headX headY, []),
   (.bitXor headX headY, []),
   (.bitOr headX headY, []),
   (.order .lt headX headY, []),
   (.equality .eq headX headY, []),
   (.and headX headY, []),
   (.or headX headY, []),
   (.cond headX headY headZ, []),
   (.assign .assign headX headY, []),
   (.new (.array (.elem .bool) .none), []),
   (.tuple (.some headX) (.cons (.some headY) .nil), []),
   (.inlineArray headX (.cons headY .nil), []),
   (.ident "x", []),
   (.lit (.bool true), []),
   (.litUnit (.dec 1 0 0) .wei, []),
   (.elemType .bool (by intro h; cases h), [])]

def typeHeadWitnesses : List (Syn .typeName × List Choice) :=
  [(.elem .addressPayable, []),
   (.fnType .nil (.some .internal) (.some .view) .nil, [.attrs [.vis, .mutab]]),
   (.mapping (.elem .bool (by intro h; cases h)) (.some "key") (.elem .bool) (.some "value"), []),
   (.userType ⟨"T", ["U"]⟩, []),
   (.array (.elem .bool) (.some headX), [])]

def argsHeadWitnesses : List (Syn .callArgs × List Choice) :=
  [(.positional (.cons headX .nil), []), (.named (.cons (.namedArg "x" headY) .nil), [])]

def namedHeadWitnesses : List (Syn .namedArg × List Choice) := [(.namedArg "x" headY, [])]
def paramHeadWitnesses : List (Syn .param × List Choice) :=
  [(.param (.elem .bool) .none (.some "x"), [])]
def varHeadWitnesses : List (Syn .varDecl × List Choice) :=
  [(.varDecl (.elem .bool) .none "x", [])]
def simpleHeadWitnesses : List (Syn .simple × List Choice) :=
  [(.declVar (.varDecl (.elem .bool) .none "x") .none, []),
   (.declTuple 1 (.varDecl (.elem .bool) .none "x") (.cons .none .nil) headY, []),
   (.exprStmt headX, [])]

def literalHeadWitnesses : List (Syn .expr × List Choice) :=
  [(.lit (.bool true), []), (.lit (.num (.dec 1 0 0)), []),
   (.lit (.str []), [.frags [0]]), (.lit (.hexStr [125]), [.frags [1]]),
   (.lit (.unicodeStr [123, 125]), [.frags [1, 1]])]

theorem all_head_constructor_witnesses_checked :
    exprHeadWitnesses.all headWitnessCheck = true ∧
    typeHeadWitnesses.all headWitnessCheck = true ∧
    argsHeadWitnesses.all headWitnessCheck = true ∧
    namedHeadWitnesses.all headWitnessCheck = true ∧
    paramHeadWitnesses.all headWitnessCheck = true ∧
    varHeadWitnesses.all headWitnessCheck = true ∧
    simpleHeadWitnesses.all headWitnessCheck = true ∧
    literalHeadWitnesses.all headWitnessCheck = true := by decide +kernel

theorem exprHeadWitnesses_inventory :
    exprHeadWitnesses.map (fun w => w.1.ctor) =
      [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order, .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit, .elemType] := rfl

theorem typeHeadWitnesses_inventory :
    typeHeadWitnesses.map (fun w => w.1.ctor) =
      [.elem, .fnType, .mapping, .userType, .array] := rfl

theorem argsHeadWitnesses_inventory :
    argsHeadWitnesses.map (fun w => w.1.ctor) =
      [.positional, .named] := rfl

theorem namedHeadWitnesses_inventory :
    namedHeadWitnesses.map (fun w => w.1.ctor) =
      [.namedArg] := rfl

theorem paramHeadWitnesses_inventory :
    paramHeadWitnesses.map (fun w => w.1.ctor) =
      [.param] := rfl

theorem varHeadWitnesses_inventory :
    varHeadWitnesses.map (fun w => w.1.ctor) =
      [.varDecl] := rfl

theorem simpleHeadWitnesses_inventory :
    simpleHeadWitnesses.map (fun w => w.1.ctor) =
      [.declVar, .declTuple, .exprStmt] := rfl

theorem head_constructor_count :
    exprHeadWitnesses.length + typeHeadWitnesses.length + argsHeadWitnesses.length + namedHeadWitnesses.length + paramHeadWitnesses.length + varHeadWitnesses.length + simpleHeadWitnesses.length = 42 := rfl

#print axioms all_head_constructor_witnesses_checked
#print axioms head_constructor_count
#print axioms exprHeadWitnesses_inventory
#print axioms typeHeadWitnesses_inventory
#print axioms argsHeadWitnesses_inventory
#print axioms namedHeadWitnesses_inventory
#print axioms paramHeadWitnesses_inventory
#print axioms varHeadWitnesses_inventory
#print axioms simpleHeadWitnesses_inventory
end Solidity.Frontend.StatementGrammarH28
