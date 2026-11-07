import Solidity.Frontend.StatementGrammarH28.RootContract
import Solidity.Source.Ctor

/-! The same existing typed constructor witnesses as checkpoint O, checked
against stronger two-token/parenthesis properties. These are fixture data,
not duplicated parser/producer implementations. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def pairWitnessCheck {c : Cat} (w : Syn c × List Choice) : Bool :=
  match w.1.yield w.2 with
  | some (parts, []) => !parts.flatten.isEmpty && !badAtomPair parts.flatten
  | _ => false

def parenWitnessCheck (w : Syn .callArgs × List Choice) : Bool :=
  match w.1.yield w.2 with
  | some (parts, []) => parts.flatten.head? == some (Tok.punct .lparen)
  | _ => false

def pairX : Syn .expr := .ident "x"
def pairY : Syn .expr := .ident "y"
def pairZ : Syn .expr := .ident "z"

def pairExprWitnesses : List (Syn .expr × List Choice) :=
  [(.index pairX (.some pairY), []),
   (.slice pairX (.some pairY) (.some pairZ), []),
   (.member pairX "f", []),
   (.callOptions pairX (.namedArg "gas" pairY) .nil, []),
   (.call pairX (.positional (.cons pairY .nil)), []),
   (.payableConv (.positional (.cons pairY .nil)), []),
   (.metaType (.userType ⟨"T", []⟩), []),
   (.unaryPrefix .neg pairX, []),
   (.unarySuffix .inc pairX, []),
   (.exp pairX pairY, []),
   (.mulDivMod .mul pairX pairY, []),
   (.addSub .add pairX pairY, []),
   (.shift .shl pairX pairY, []),
   (.bitAnd pairX pairY, []),
   (.bitXor pairX pairY, []),
   (.bitOr pairX pairY, []),
   (.order .lt pairX pairY, []),
   (.equality .eq pairX pairY, []),
   (.and pairX pairY, []),
   (.or pairX pairY, []),
   (.cond pairX pairY pairZ, []),
   (.assign .assign pairX pairY, []),
   (.new (.array (.elem .bool) .none), []),
   (.tuple (.some pairX) (.cons (.some pairY) .nil), []),
   (.inlineArray pairX (.cons pairY .nil), []),
   (.ident "x", []),
   (.lit (.bool true), []),
   (.litUnit (.dec 1 0 0) .wei, []),
   (.elemType .bool (by intro h; cases h), [])]

def pairTypeWitnesses : List (Syn .typeName × List Choice) :=
  [(.elem .addressPayable, []),
   (.fnType .nil (.some .internal) (.some .view) .nil, [.attrs [.vis, .mutab]]),
   (.mapping (.elem .bool (by intro h; cases h)) (.some "key") (.elem .bool) (.some "value"), []),
   (.userType ⟨"T", ["U"]⟩, []),
   (.array (.elem .bool) (.some pairX), [])]

def pairArgsWitnesses : List (Syn .callArgs × List Choice) :=
  [(.positional (.cons pairX .nil), []), (.named (.cons (.namedArg "x" pairY) .nil), [])]

def pairLiteralWitnesses : List (Syn .expr × List Choice) :=
  [(.lit (.bool true), []), (.lit (.num (.dec 1 0 0)), []),
   (.lit (.str []), [.frags [0]]), (.lit (.hexStr [125]), [.frags [1]]),
   (.lit (.unicodeStr [123, 125]), [.frags [1, 1]])]


theorem all_pair_constructor_witnesses_checked :
    pairExprWitnesses.all pairWitnessCheck = true ∧
    pairTypeWitnesses.all pairWitnessCheck = true ∧
    pairArgsWitnesses.all parenWitnessCheck = true ∧
    pairLiteralWitnesses.all pairWitnessCheck = true := by decide +kernel

theorem pairExprWitnesses_inventory :
    pairExprWitnesses.map (fun w => w.1.ctor) =
      [.index, .slice, .member, .callOptions, .call, .payableConv, .metaType, .unaryPrefix, .unarySuffix, .exp, .mulDivMod, .addSub, .shift, .bitAnd, .bitXor, .bitOr, .order, .equality, .and, .or, .cond, .assign, .new, .tuple, .inlineArray, .ident, .lit, .litUnit, .elemType] := rfl

theorem pairTypeWitnesses_inventory :
    pairTypeWitnesses.map (fun w => w.1.ctor) =
      [.elem, .fnType, .mapping, .userType, .array] := rfl

theorem pairArgsWitnesses_inventory :
    pairArgsWitnesses.map (fun w => w.1.ctor) =
      [.positional, .named] := rfl

theorem pair_constructor_count :
    pairExprWitnesses.length + pairTypeWitnesses.length + pairArgsWitnesses.length = 36 := rfl

#print axioms all_pair_constructor_witnesses_checked
#print axioms pair_constructor_count
#print axioms pairExprWitnesses_inventory
#print axioms pairTypeWitnesses_inventory
#print axioms pairArgsWitnesses_inventory
end Solidity.Frontend.StatementGrammarH28
