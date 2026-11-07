import Solidity.Frontend.Checked.Check

/-!
# Frozen disagreement refusals, rerun without changing verdicts

These finite kernel controls supplement the arbitrary-tree refusal theorems.
They establish no parser completeness or expression uniqueness result.
-/

namespace Solidity.Frontend.ExpressionUniqueness

open Solidity.Source Solidity.Frontend.Checked

def expressionError (s : String) : Option String :=
  match parseExpr (ascii s) with
  | .error e => some e.msg
  | .ok _ => none

def refusalMessage : String :=
  "refused by Syn.prec (precedence, dangling else or a solc node condition)"

theorem prefix_postfix_fixture : expressionError "-a++" = some refusalMessage := by
  decide +kernel

theorem conditional_assignment_fixture :
    expressionError "a ? b : c = d" = some refusalMessage := by
  decide +kernel

theorem postfix_member_fixture : expressionError "a++.f" = some refusalMessage := by
  decide +kernel

theorem double_postfix_fixture : expressionError "a++ ++" = some refusalMessage := by
  decide +kernel

theorem grouped_disagreements_accepted :
    (expressionError "-(a++)").isNone &&
    (expressionError "a ? b : (c = d)").isNone &&
    (expressionError "(a++).f").isNone = true := by
  decide +kernel

def expressionCtor (s : String) : Option Ctor :=
  (parseExpr (ascii s)).toOption.map Syn.ctor

theorem constructor_index : expressionCtor "a[0]" = some .index := by
  decide +kernel

theorem constructor_slice : expressionCtor "a[:]" = some .slice := by
  decide +kernel

theorem constructor_member : expressionCtor "a.b" = some .member := by
  decide +kernel

theorem constructor_callOptions : expressionCtor "a{x:b}" = some .callOptions := by
  decide +kernel

theorem constructor_call : expressionCtor "a()" = some .call := by
  decide +kernel

theorem constructor_payableConv : expressionCtor "payable(a)" = some .payableConv := by
  decide +kernel

theorem constructor_metaType : expressionCtor "type(T)" = some .metaType := by
  decide +kernel

theorem constructor_unaryPrefix : expressionCtor "-a" = some .unaryPrefix := by
  decide +kernel

theorem constructor_unarySuffix : expressionCtor "a++" = some .unarySuffix := by
  decide +kernel

theorem constructor_exp : expressionCtor "a**b" = some .exp := by
  decide +kernel

theorem constructor_mulDivMod : expressionCtor "a*b" = some .mulDivMod := by
  decide +kernel

theorem constructor_addSub : expressionCtor "a+b" = some .addSub := by
  decide +kernel

theorem constructor_shift : expressionCtor "a<<b" = some .shift := by
  decide +kernel

theorem constructor_bitAnd : expressionCtor "a&b" = some .bitAnd := by
  decide +kernel

theorem constructor_bitXor : expressionCtor "a^b" = some .bitXor := by
  decide +kernel

theorem constructor_bitOr : expressionCtor "a|b" = some .bitOr := by
  decide +kernel

theorem constructor_order : expressionCtor "a<b" = some .order := by
  decide +kernel

theorem constructor_equality : expressionCtor "a==b" = some .equality := by
  decide +kernel

theorem constructor_and : expressionCtor "a&&b" = some .and := by
  decide +kernel

theorem constructor_or : expressionCtor "a||b" = some .or := by
  decide +kernel

theorem constructor_cond : expressionCtor "a?b:c" = some .cond := by
  decide +kernel

theorem constructor_assign : expressionCtor "a=b" = some .assign := by
  decide +kernel

theorem constructor_new : expressionCtor "new T" = some .new := by
  decide +kernel

theorem constructor_tuple : expressionCtor "()" = some .tuple := by
  decide +kernel

theorem constructor_inlineArray : expressionCtor "[a]" = some .inlineArray := by
  decide +kernel

theorem constructor_ident : expressionCtor "a" = some .ident := by
  decide +kernel

theorem constructor_lit : expressionCtor "\"a\" \"b\"" = some .lit := by
  decide +kernel

theorem constructor_litUnit : expressionCtor "1 gwei" = some .litUnit := by
  decide +kernel

theorem constructor_elemType : expressionCtor "uint" = some .elemType := by
  decide +kernel

theorem postfix_index_fixture : expressionError "a++[0]" = some refusalMessage := by
  decide +kernel

theorem postfix_slice_fixture : expressionError "a++[:]" = some refusalMessage := by
  decide +kernel

theorem postfix_options_fixture : expressionError "a++{x:b}" = some refusalMessage := by
  decide +kernel

theorem postfix_call_fixture : expressionError "a++()" = some refusalMessage := by
  decide +kernel

end Solidity.Frontend.ExpressionUniqueness
