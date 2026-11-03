
import Solidity.Yul.BlockHeaders
import Solidity.Yul.ExpressionCheck

/-! Kernel controls for actual direct-block collection, freshness and expression
arity composition. These do not check complete function bodies/control flow. -/
namespace Solidity.Yul.Checks.Headers
open Solidity.Source (Syn)
def pairBody : Syn (.list .yulStmt) :=
  .cons (.yulAssign ["a"] [] (.yulPath "x" []))
    (.cons (.yulAssign ["b"] [] (.yulPath "y" [])) .nil)
def fixture : Syn (.list .yulStmt) :=
  .cons (.yulExprStmt (.yulCall "notify" .nil))
    (.cons (.yulFun "pair" ["x", "y"] ["a", "b"] pairBody)
      (.cons (.yulBlock (.cons (.yulFun "nested" [] [] .nil) .nil))
        (.cons (.yulIf (.yulLit (.dec 1)) (.cons (.yulFun "conditional" [] [] .nil) .nil))
          (.cons (.yulFun "notify" [] [] .nil) .nil))))
def expected : List (String × Sig) := [("pair", ⟨2, 2⟩), ("notify", ⟨0, 0⟩)]
theorem fixture_collected : collectHeaders fixture = expected := rfl
def derivation : HeadersD fixture expected := collectHeaders_sound fixture
def checked : CheckedHeaders ["solidityLocal"] fixture :=
  ⟨expected, derivation, (fresh_iff _ _).mp (by decide)⟩
example : checkHeaders ["solidityLocal"] fixture = some checked :=
  derivation.check_complete checked.fresh
example : collectHeaders fixture = expected := fixture_collected
example : (checkHeaders [] fixture).isSome = true := by decide
example : (checkHeaders ["notify"] fixture).isSome = false := by decide
example : (checkHeaders ["pair"] fixture).isSome = false := by decide

def duplicate : Syn (.list .yulStmt) :=
  .cons (.yulFun "same" [] [] .nil) (.cons (.yulFun "same" ["x"] ["r"] .nil) .nil)
example : collectHeaders duplicate = [("same", ⟨0, 0⟩), ("same", ⟨1, 1⟩)] := rfl
example : (checkHeaders [] duplicate).isSome = false := by decide

def loopNested : Syn (.list .yulStmt) :=
  .cons (.yulFor (.cons (.yulFun "pre" [] [] .nil) .nil) (.yulLit (.dec 1))
    (.cons (.yulFun "post" [] [] .nil) .nil) (.cons (.yulFun "body" [] [] .nil) .nil)) .nil
example : collectHeaders loopNested = [] := rfl

def functions : FunctionNames [⟨2, 2⟩, ⟨0, 0⟩] := checked.hoist []
example : (resolve functions "pair").map (·.1) = some ⟨2, 2⟩ := by decide
example : (resolve functions "notify").map (·.1) = some ⟨0, 0⟩ := by decide
example : (resolve functions "nested").isSome = false := by decide
example : (resolve functions "conditional").isSome = false := by decide
example : resolve functions "notify" = some ⟨⟨0, 0⟩, .there .here⟩ :=
  checked.hoist_new [] (.tail .head)

def env : ExprEnv [⟨2, 2⟩, ⟨0, 0⟩] [] 0 := ⟨[], functions, []⟩
example : (inferExpr env (.yulCall "notify" .nil)).map (·.1) = some 0 := by decide
example : (inferExpr env (.yulCall "pair"
    (.cons (.yulLit (.dec 7)) (.cons (.yulLit (.dec 9)) .nil)))).map (·.1) = some 2 := by decide
example : (inferExpr env (.yulCall "pair" (.cons (.yulLit (.dec 7)) .nil))).isSome = false := by decide
example : (inferExpr env (.yulCall "nested" .nil)).isSome = false := by decide
example : (inferExpr env (.yulCall "conditional" .nil)).isSome = false := by decide

/-- A header-only checker is not reserved-name/body admission. Passing the
entire required namespace is a real premise, including inaccessible names. -/
def reserved : Syn (.list .yulStmt) := .cons (.yulFun "add" [] [] .nil) .nil
example : (checkHeaders ["add"] reserved).isSome = false := by decide

end Solidity.Yul.Checks.Headers
