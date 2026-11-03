import Solidity.Yul.DeclarationCheck
import Solidity.Yul.Checks.Headers
namespace Solidity.Yul.Checks.Declarations
open Solidity.Source (Syn)

example : checkName "helper_2" = true := by decide
example : checkName "$x" = true := by decide
example : checkName "uint" = true := by decide
example : checkName "" = false := by decide
example : checkName "2helper" = false := by decide
example : checkName "a.b" = false := by decide
example : checkName "a b" = false := by decide
example : checkName "é" = false := by decide
example : checkName "function" = false := by decide
example : checkName "true" = false := by decide
example : checkName "leave" = false := by decide
example : checkName "add" = false := by decide
example : checkName "pc" = false := by decide
example : checkName "gas" = false := by decide
example : checkName "callcode" = false := by decide
example : checkNames ["outer", "functionName"] ["arg", "result"] = true := by decide
example : checkNames ["outer", "functionName"] ["outer"] = false := by decide
example : checkNames ["outer", "functionName"] ["functionName"] = false := by decide
example : checkNames [] ["arg", "arg"] = false := by decide
example : checkNames [] ["arg", "add"] = false := by decide
example : checkNames ["outer"] [] = true := by decide

example : checkLegalHeaders ["solidityLocal"] Headers.fixture = some Headers.expected := by decide
example : (checkLegalHeaders ["pair"] Headers.fixture).isNone = true := by decide
example : (checkLegalHeaders [] Headers.duplicate).isNone = true := by decide
example : (checkLegalHeaders [] Headers.reserved).isNone = true := by decide
example : checkLegalHeaders [] Headers.loopNested = some [] := rfl

def legal : LegalHeadersD ["solidityLocal"] Headers.fixture Headers.expected :=
  checkLegalHeaders_sound (by decide)
def functions : FunctionNames [⟨2, 2⟩, ⟨0, 0⟩] := legal.checked.hoist []
def env : ExprEnv [⟨2, 2⟩, ⟨0, 0⟩] [] 0 := ⟨[], functions, []⟩
example : (inferExpr env (.yulCall "notify" .nil)).map (·.1) = some 0 := by decide
example : (inferExpr env (.yulCall "pair"
    (.cons (.yulLit (.dec 7)) (.cons (.yulLit (.dec 9)) .nil)))).map (·.1) = some 2 := by decide
example : (inferExpr env (.yulCall "pair" (.cons (.yulLit (.dec 7)) .nil))).isNone = true := by decide
example : (inferExpr env (.yulCall "nested" .nil)).isNone = true := by decide

theorem actual_forward_callable :
    NoBuiltin "notify" ∧
      resolve functions "notify" = some ⟨⟨0, 0⟩, .there .here⟩ :=
  legal.callable [] (.tail .head)

/-- Reserved identifiers need not be executable inline builtins. -/
example : checkName "linkersymbol" = false := by decide
example : checkName "datasize" = false := by decide
example : checkName "dataoffset" = false := by decide
example : checkName "datacopy" = false := by decide
example : checkName "setimmutable" = false := by decide
example : checkName "loadimmutable" = false := by decide
example : checkName "jump" = false := by decide
example : checkName "jumpdest" = false := by decide
example : checkName "push0" = false := by decide
example : checkName "push32" = false := by decide
example : checkName "dup16" = false := by decide
example : checkName "swap16" = false := by decide
example : checkName "difficulty" = false := by decide
example : checkName "slotnum" = true := by decide
example : checkName "verbatim" = true := by decide
example : checkName "verbatim_1i_1o" = true := by decide
example : checkName "push" = true := by decide
example : checkName "dup" = true := by decide
example : checkName "sha3" = true := by decide
example : checkName "suicide" = true := by decide
example : checkName "ADD" = true := by decide
example : (lookupBuiltin "linkersymbol").isNone = true := by decide
example : checkNames [] ["a", "linkersymbol"] = false := by decide
example : (checkLegalHeaders [] (.cons (.yulFun "linkersymbol" [] [] .nil) .nil)).isNone = true := by decide
example : (checkLegalHeaders [] (.cons (.yulFun "jump" [] [] .nil) .nil)).isNone = true := by decide

end Solidity.Yul.Checks.Declarations
