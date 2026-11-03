import Solidity.Yul.ClosedSyntax
import Solidity.Yul.TierPolicy
set_option Elab.async false
namespace Solidity.Yul.Checks.BlockTyping
open Solidity.Source (Syn YulLit)
open Solidity.Yul.BlockTyping

def list {c : Solidity.Source.Cat} (xs : List (Syn c)) : Syn (.list c) :=
  xs.foldr Syn.cons Syn.nil
def lit (n : Nat) : Syn .yulExpr := .yulLit (.dec n)
def varExpr (name : String) : Syn .yulExpr := .yulPath name []
def call (name : String) (args : List (Syn .yulExpr)) : Syn .yulExpr := .yulCall name (list args)
def decl (name : String) (value : Syn .yulExpr) : Syn .yulStmt := .yulLet name [] (.some value)
def zero (name : String) : Syn .yulStmt := .yulLet name [] .none
def assign (name : String) (value : Syn .yulExpr) : Syn .yulStmt := .yulAssign [name] [] value
def pop (value : Syn .yulExpr) : Syn .yulStmt := .yulExprStmt (call "pop" [value])
def fn (name : String) (args rets : List String) (body : List (Syn .yulStmt)) :
    Syn .yulStmt := .yulFun name args rets (list body)
def block (body : List (Syn .yulStmt)) : Syn .yulStmt := .yulBlock (list body)
def typed (body : List (Syn .yulStmt)) : Bool :=
  (checkBlock ClosedSyntax.rootEnv ClosedSyntax.rootControl (list body)).isSome
def full (body : List (Syn .yulStmt)) : Bool :=
  (ClosedSyntax.check [] (list body)).toOption.isSome
def loop (pre : List (Syn .yulStmt)) (guard : Syn .yulExpr)
    (post body : List (Syn .yulStmt)) : Syn .yulStmt :=
  .yulFor (list pre) guard (list post) (list body)
def switch (value : Syn .yulExpr) (labels : List YulLit) : Syn .yulStmt :=
  .yulSwitch value (list (labels.map fun l => .yulCase l .nil)) .none

def mulDiv : List (Syn .yulStmt) := [
  decl "answer" (call "mulDiv" [lit 7, lit 11, lit 3]),
  fn "mulDiv" ["a", "b", "denominator"] ["r"] [
    assign "r" (call "div" [call "mul" [varExpr "a", varExpr "b"], varExpr "denominator"])]]
example : full mulDiv = true := by decide
theorem mulDiv_inhabited : Nonempty (ClosedSyntax.Checked [] (list mulDiv)) :=
  (ClosedSyntax.check_iff [] _).mp (by decide)

def mutualCalls : List (Syn .yulStmt) := [
  decl "answer" (call "first" [lit 3]),
  fn "first" ["a"] ["r"] [
    .yulIf (varExpr "a") (list [assign "r" (call "second" [call "sub" [varExpr "a", lit 1], lit 7])])],
  fn "second" ["b", "extra"] ["r"] [
    assign "r" (call "add" [varExpr "extra", call "first" [varExpr "b"]])]]
example : full mutualCalls = true := by decide
example : full [fn "same1" ["a"] ["r"] [assign "r" (varExpr "a")],
    fn "same2" ["a"] ["r"] [assign "r" (call "same1" [varExpr "a"])],
    decl "answer" (call "same2" [lit 257])] = true := by decide

def frame : Env [] 5 := ClosedSyntax.rootEnv.frame ["a", "b"] ["r", "s", "t"]
example : resolve frame.locals "a" = some 0 := by decide
example : resolve frame.locals "b" = some 1 := by decide
example : resolve frame.locals "r" = some 2 := by decide
example : resolve frame.locals "s" = some 3 := by decide
example : resolve frame.locals "t" = some 4 := by decide

example : full [zero "a", pop (varExpr "a")] = true := by decide
example : full [decl "a" (varExpr "a")] = false := by decide
example : full [decl "a" (varExpr "later"), decl "later" (lit 1)] = false := by decide
example : full [decl "captured" (lit 7),
    fn "helper" [] ["r"] [assign "r" (varExpr "captured")]] = false := by decide
example : full [fn "outer" ["arg"] ["r"] [
    fn "inner" [] ["innerR"] [assign "innerR" (varExpr "arg")],
    assign "r" (call "inner" [])]] = false := by decide
example : full [fn "helper" ["a"] ["r"] [assign "r" (varExpr "a")],
    fn "outer" [] ["r"] [
      fn "inner" [] ["innerR"] [assign "innerR" (call "helper" [lit 7])],
      assign "r" (call "inner" [])]] = true := by decide
example : full [block [decl "hidden" (lit 7)], pop (varExpr "hidden")] = false := by decide
example : full [block [fn "hidden" [] [] []], .yulExprStmt (call "hidden" [])] = false := by decide
example : full [.yulIf (lit 0) (list [pop (varExpr "missing")])] = false := by decide
example : full [fn "unused" [] [] [pop (varExpr "missing")]] = false := by decide

def pair : Syn .yulStmt := fn "pair" [] ["a", "b"] [
  assign "a" (lit 11), assign "b" (lit 22)]
example : full [pair, .yulLet "x" ["y"] (.some (call "pair" [])),
    pop (call "sub" [varExpr "x", varExpr "y"])] = true := by decide
example : full [pair, decl "x" (call "pair" [])] = false := by decide
example : full [.yulLet "x" ["y"] (.some (call "add" [lit 1, lit 2]))] = false := by decide
example : full [fn "one" ["a"] ["r"] [assign "r" (varExpr "a")],
    decl "answer" (call "one" [])] = false := by decide
example : full [pair, pop (call "add" [call "pair" [], lit 1])] = false := by decide
example : full [.yulExprStmt (call "add" [lit 1, lit 2])] = false := by decide
example : full [.yulIf (call "pop" [lit 1]) .nil] = false := by decide
example : full [zero "target1", zero "target2", pair,
    .yulAssign ["target1"] [["target2"]] (call "pair" [])] = true := by decide
example : full [zero "target", pair, .yulAssign ["target"] [["target"]] (call "pair" [])] = false := by decide
example : full [zero "x", pop (.yulPath "x" ["slot"])] = false := by decide

def counted : Syn .yulStmt := loop [decl "i" (lit 3), zero "sum"] (varExpr "i")
  [assign "i" (call "sub" [varExpr "i", lit 1])]
  [assign "sum" (call "add" [varExpr "sum", varExpr "i"]), .yulContinue]
example : full [counted] = true := by decide
example : full [counted, pop (varExpr "i")] = false := by decide
example : full [loop [block [zero "i"]] (varExpr "i") [] []] = false := by decide
example : full [loop [] (lit 0) [pop (varExpr "bodyLocal")] [zero "bodyLocal"]] = false := by decide
example : full [loop [] (lit 0) [zero "postLocal"] [pop (varExpr "postLocal")]] = false := by decide
example : full [loop [] (lit 0) [zero "phase"] [zero "phase"]] = true := by decide
example : full [fn "early" [] ["r"] [
    loop [.yulLeave, zero "i"] (varExpr "i") [] []]] = true := by decide
example : full [loop [.yulBreak] (lit 0) [] []] = false := by decide
example : full [loop [] (lit 0) [.yulContinue] []] = false := by decide
example : full [loop [] (lit 0) [] [fn "cannotBreak" [] [] [.yulBreak]]] = false := by decide
example : full [loop [fn "forbidden" [] [] []] (lit 0) [] []] = false := by decide
example : typed [loop [block [fn "forbidden" [] [] []]] (lit 0) [] []] =
    true := by decide
example : full [loop [block [fn "forbidden" [] [] []]] (lit 0) [] []] =
    false := by decide
example : full [loop [loop [] (lit 0) [] [fn "allowed" [] [] []]] (lit 0) [] []] =
    true := by decide

example : full [switch (lit 0) [.dec 0, .hex 1]] = true := by decide
example : full [switch (lit 0) [.dec 1, .hex 1]] = false := by decide
example : full [switch (lit 0) [.dec 1, .bool true]] = false := by decide
example : full [switch (lit 0) [.dec 0, .bool false]] = false := by decide
example : full [switch (lit 0) [.dec (2 ^ 256)]] = false := by decide
example : full [pop (lit (2 ^ 256))] = false := by decide
example : full [switch (lit 0) []] = false := by decide
example : full [.yulSwitch (lit 0) .nil (.some .nil)] = true := by decide
example : full [.yulBreak] = false := by decide
example : full [.yulLeave] = false := by decide

/-- Typing is NOT compiler-independent tier admission. -/
example : full [decl "remaining" (call "gas" [])] = true := by decide
example : full [decl "loaded" (call "mload" [lit 0])] = true := by decide
example : full [.yulExprStmt (call "mstore" [lit 0, lit 7])] = true := by decide
/-- A missing outside namespace is NOT a proven Source namespace. -/
example : full [zero "msg"] = true := by decide
example : (ClosedSyntax.check ["msg"] (list [zero "msg"])).toOption.isSome = false := by decide

/-- Even a correct outside-name list does not replace solc occurrence attachment.
Standalone Yul typing of own parameters is valid. The separate pinned Source
fixture with f(uint x) refuses6578 for the x read/write inside a Yul function. -/
example : (ClosedSyntax.check ["x"] (list [
    fn "helper" ["x"] ["result"] [assign "result" (varExpr "x")]])).toOption.isSome =
    true := by decide
example : (ClosedSyntax.check ["msg"] (list [
    fn "helper" ["msg"] ["result"] [assign "result" (varExpr "msg")]])).toOption.isSome =
    true := by decide

/-- Actual expression typing/extraction composes with the existing policy;
this is not whole-statement extraction or Source admission. -/
def expressionPolicy (tier : Tier) (expression : Syn .yulExpr) :
    Option (Except Refusal Unit) :=
  (Solidity.Yul.BlockTyping.checkExpr ClosedSyntax.rootEnv 1 expression).map
    (fun d => Policy.checkExpr tier d.term)
example : expressionPolicy .C (call "gas" []) = some (.error (.compilerDependent "gas")) := rfl
example : expressionPolicy .A (call "mload" [lit 0]) = some (.error (.needsTier .B)) := rfl
example : expressionPolicy .A (call "add" [lit 257, lit 1]) = some (.ok ()) := rfl

end Solidity.Yul.Checks.BlockTyping
