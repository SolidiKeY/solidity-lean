import Solidity.Yul.DeclarationScope
set_option Elab.async false
namespace Solidity.Yul.Checks.DeclarationScopes
open Solidity.Source (Syn)
open Solidity.Yul.DeclarationScope

def statements (xs : List (Syn .yulStmt)) : Syn (.list .yulStmt) :=
  xs.foldr Syn.cons Syn.nil
def decl (name : String) : Syn .yulStmt := .yulLet name [] .none
def fn (name : String) (args rets : List String) (body : List (Syn .yulStmt)) :
    Syn .yulStmt := .yulFun name args rets (statements body)
def block (body : List (Syn .yulStmt)) : Syn .yulStmt := .yulBlock (statements body)
def loop (pre post body : List (Syn .yulStmt)) : Syn .yulStmt :=
  .yulFor (statements pre) (.yulLit (.dec 0)) (statements post) (statements body)
def names (outside visible : List String) (body : List (Syn .yulStmt)) : Option (List String) :=
  (checkBlock outside visible (statements body)).map Sigma.fst

example : names [] [] [] = some [] := rfl
example : names [] ["old"] [decl "a", decl "b"] = some ["b", "a", "old"] := by decide
example : names [] [] [decl "a", decl "a"] = none := by decide
example : names [] [] [.yulLet "a" ["a"] .none] = none := by decide
example : names [] [] [.yulLet "a" ["b"] .none] = some ["a", "b"] := by decide
example : names [] [] [fn "helper" ["a"] ["r"] [], decl "a"] =
    some ["a", "helper"] := by decide
example : names [] [] [decl "a", fn "helper" ["a"] ["r"] []] = none := by decide
example : names [] [] [fn "helper" [] ["a"] [], decl "a"] =
    some ["a", "helper"] := by decide
example : names [] [] [decl "a", fn "helper" [] ["a"] []] = none := by decide
example : names [] [] [decl "helper", fn "helper" [] [] []] = none := by decide
example : names [] [] [fn "helper" [] [] [], decl "helper"] = none := by decide
example : names [] [] [fn "helper" [] [] [], fn "helper" [] [] []] = none := by decide
example : names [] [] [fn "helper" ["helper"] [] []] = none := by decide
example : names [] [] [fn "helper" [] ["helper"] []] = none := by decide
example : names [] [] [fn "helper" ["a", "a"] [] []] = none := by decide
example : names [] [] [fn "helper" ["a"] ["a"] []] = none := by decide
example : names [] [] [decl "hidden", fn "helper" [] [] [decl "hidden"]] = none := by decide
example : names [] [] [fn "helper" [] [] [decl "hidden"], decl "hidden"] =
    some ["hidden", "helper"] := by decide
example : names [] [] [fn "first" [] [] [decl "later"], fn "later" [] [] []] = none := by decide
example : names [] [] [fn "helper" ["arg"] [] [fn "arg" [] [] []]] = none := by decide
example : names [] [] [fn "helper" [] ["ret"] [fn "ret" [] [] []]] = none := by decide
example : names [] [] [fn "helper" [] [] [decl "helper"]] = none := by decide
example : names [] [] [block [decl "a"], block [decl "a"]] = some [] := by decide
example : names [] [] [block [fn "helper" [] [] []], block [fn "helper" [] [] []]] =
    some [] := by decide
example : names [] [] [.yulIf (.yulLit (.dec 0)) (statements [fn "helper" [] [] []]),
    decl "helper"] = some ["helper"] := by decide
example : names [] [] [.yulSwitch (.yulLit (.dec 0))
    (.cons (.yulCase (.dec 0) (statements [decl "a"]))
      (.cons (.yulCase (.dec 1) (statements [decl "a"])) .nil))
    (.some (statements [decl "a"])), decl "a"] = some ["a"] := by decide
example : names [] [] [loop [decl "i"] [decl "i"] []] = none := by decide
example : names [] [] [loop [decl "i"] [] [decl "i"]] = none := by decide
example : names [] [] [loop [decl "i"] [] [], decl "i"] = some ["i"] := by decide
example : names [] [] [loop [] [decl "p"] [decl "p"]] = some [] := by decide
example : names [] [] [loop [block [decl "i"]] [] [decl "i"]] = some [] := by decide
example : names [] [] [fn "helper" [] [] [decl "a"], decl "a"] =
    some ["a", "helper"] := by decide
example : names [] [] [loop [decl "i"] [] [loop [decl "j"] [] [], decl "j"]] =
    some [] := by decide

/-- Outside Solidity names are NOT merged into the Yul forbidden-name list. -/
example : names ["x"] [] [decl "x"] = none := by decide
example : names ["x"] [] [fn "x" [] [] []] = some ["x"] := by decide
example : names ["x"] [] [fn "helper" ["x"] [] []] = some ["helper"] := by decide
example : names ["x"] [] [fn "helper" [] ["x"] []] = some ["helper"] := by decide
example : names ["x"] [] [fn "helper" [] [] [decl "x"]] = none := by decide
example : names [] ["x"] [fn "x" [] [] []] = none := by decide
example : names [] ["x"] [fn "helper" ["x"] [] []] = none := by decide
example : names [] ["x"] [fn "helper" [] ["x"] []] = none := by decide

example : checkName "this" = false := by decide
example : checkName "super" = false := by decide
example : checkName "_" = false := by decide
example : ["this", "super", "_"].all (fun name =>
    (names [] [] [decl name]).isNone &&
    (names [] [] [fn name [] [] []]).isNone &&
    (names [] [] [fn "helper" [name] [] []]).isNone &&
    (names [] [] [fn "helper" [] [name] []]).isNone) = true := by decide

/-- Explicit component boundaries: full typing/placement still must refuse
these malformed programs even though declaration names alone are legal. -/
example : names [] [] [.yulLet "a" [] (.some (.yulPath "a" []))] =
    some ["a"] := by decide
example : names [] [] [.yulBreak] = some [] := rfl
example : names [] [] [.yulExprStmt (.yulLit (.dec (2 ^ 256)))] = some [] := rfl
example : (checkStatement [] [] (fn "add" [] [] [])).isSome = true := by decide
example : names [] [] [fn "add" [] [] []] = none := by decide

def combined : Syn (.list .yulStmt) := statements [
  fn "twice" ["arg"] ["result"] [
    loop [decl "counter"] [decl "postLocal"] [
      .yulIf (.yulLit (.dec 1)) (statements [decl "branchLocal"]),
      .yulLeave]],
  loop [decl "counter"] [decl "phaseLocal"] [
    block [decl "phaseLocal"],
    .yulSwitch (.yulLit (.dec 1))
      (.cons (.yulCase (.dec 1) (statements [decl "caseLocal"])) .nil)
      (.some (statements [decl "caseLocal"]))],
  decl "counter"]
example : (checkBlock [] [] combined).map Sigma.fst =
    some ["counter", "twice"] := by decide
theorem combined_inhabited : ∃ final, Nonempty (BlockD [] [] combined final) :=
  (checkBlock_iff [] [] combined).mp (by decide)

end Solidity.Yul.Checks.DeclarationScopes
