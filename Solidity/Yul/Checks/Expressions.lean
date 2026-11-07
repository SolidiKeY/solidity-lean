import Solidity.Yul.ExpressionCheck

/-! Controls of the source-grammar expression judgement and intrinsic elaboration.
Whole-block environment construction remains pending; tier admission has
separate primitive controls. -/
namespace Solidity.Yul.Checks.Expressions
open Solidity.Source (Syn)

def empty : ExprEnv [] [] 0 := ⟨[], [], []⟩
def lit (n : Nat) : Syn .yulExpr := .yulLit (.dec n)
def plus : Syn .yulExpr := .yulCall "add" (.cons (lit 7) (.cons (lit 9) .nil))

theorem plus_checked : (inferExpr empty plus).map (·.1) = some 1 := by decide +kernel
theorem unknown_refused : (inferExpr empty (.yulPath "missing" [])).isSome = false := by decide +kernel
theorem arity_refused : (inferExpr empty (.yulCall "add" (.cons (lit 1) .nil))).isSome = false := by decide +kernel
theorem unknown_function_refused : (inferExpr empty (.yulCall "missing" .nil)).isSome = false := by decide +kernel
theorem numeric_overflow_refused : (inferExpr empty (lit (2 ^ 256))).isSome = false := by decide +kernel
theorem string_overflow_refused : (inferExpr empty (.yulLit (.str (List.replicate 33 65)))).isSome = false := by decide +kernel
theorem short_string_left_aligned : (bytesWord [104, 105]).val = 26729 * 256 ^ 30 := by decide +kernel

def fnEnv : ExprEnv [⟨1, 2⟩] [] 0 := ⟨[], [("split", ⟨⟨1, 2⟩, .here⟩)], []⟩
def «split» : Syn .yulExpr := .yulCall "split" (.cons (lit 7) .nil)
theorem multiple_returns_checked : (inferExpr fnEnv «split»).map (·.1) = some 2 := by decide +kernel
theorem multi_operand_refused :
    (inferExpr fnEnv (.yulCall "add" (.cons «split» (.cons (lit 1) .nil)))).isSome = false := by decide +kernel

def extEnv : ExprEnv [] [.value (.unsigned 0)] 0 :=
  ⟨[], [], [("x", ⟨.here, .plain, .valueRead⟩)]⟩
theorem external_value_checked : (inferExpr extEnv (.yulPath "x" [])).map (·.1) = some 1 := by decide +kernel
theorem invalid_suffix_refused : (inferExpr extEnv (.yulPath "x" ["slot"])).isSome = false := by decide +kernel

/-- Static construction retains represented compiler-dependent operations so
admission can issue its precise refusal; static checking is not admission. -/
theorem represented_gas : (inferExpr empty (.yulCall "gas" .nil)).map (·.1) = some 1 := by decide +kernel
theorem gas_admission_refused : Builtin.checkTier .C .gas = .error (.compilerDependent "gas") := rfl

/- The fixed intrinsic environment is essential to packed-result uniqueness. -/
def singleReturnEnv : ExprEnv [⟨1, 1⟩] [] 0 := ⟨[], [("split", ⟨⟨1, 1⟩, .here⟩)], []⟩
#guard (inferExpr fnEnv «split»).map (·.1) = some 2
#guard (inferExpr singleReturnEnv «split»).map (·.1) = some 1

/-- info: 'Solidity.Yul.ExprD.result_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.ExprD.result_unique
/-- info: 'Solidity.Yul.ArgsD.result_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.ArgsD.result_unique

/-- info: 'Solidity.Yul.ExprD.term_result_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.ExprD.term_result_unique
/-- info: 'Solidity.Yul.ArgsD.terms_result_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Yul.ArgsD.terms_result_unique

end Solidity.Yul.Checks.Expressions
