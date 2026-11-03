import Solidity.Yul.BlockExtract
import Solidity.Yul.Checks.BlockTyping
import Solidity.Yul.Checks.ScopedNames
set_option Elab.async false

/-! Concrete shared closed/open checker and extraction controls. These certify
intrinsic scope/arity preparation; original Source/JSON identity, occurrence,
NoShadow, policy/safety and physical/dirty execution remain separate. -/
namespace Solidity.Yul.Checks.ScopedBlocks
open Solidity.Source (Syn)
open Solidity.Yul.Checks.BlockTyping
namespace Before
export Solidity.Yul.Checks.ScopedNames (checked)
export Solidity.Yul.Checks.ScopedNames.Before (types declarations root first second third)
end Before

def rootScope : BlockScope.Scope Before.types := .external Before.checked Before.root
def firstScope : BlockScope.Scope (globals Before.types) := rootScope.function
def rootEnv : Solidity.Yul.BlockTyping.Env [] 0 := ⟨[], []⟩
def normal : Control := ⟨false, false⟩
def path (name : String) (parts : List String) : Syn .yulExpr := .yulPath name parts

def prepared {X} (scope : BlockScope.Scope X) (body : List (Syn .yulStmt)) : Bool :=
  (ScopedBlockTyping.checkBlock scope rootEnv normal (list body)).isSome

example : prepared rootScope [decl "copy" (path "s0" ["slot"])] = true := by decide
example : prepared rootScope [decl "copy" (path "s0.slot" [])] = false := by decide
example : prepared rootScope [decl "copy" (call "add" [path "s0.slot" [], lit 1])] = false := by decide
example : prepared rootScope [assign "a" (lit 257)] = true := by decide
example : prepared firstScope [assign "a" (lit 257)] = false := by decide
example : prepared rootScope [.yulAssign ["cal", "offset"] [] (path "s0" ["slot"])] =
    true := by decide
example : prepared rootScope [.yulAssign ["cal.offset"] [] (lit 0)] = false := by decide
example : prepared rootScope [.yulAssign ["s0", "slot"] [] (lit 0)] = false := by decide
example : prepared rootScope [.yulAssign ["localStore", "slot"] [] (lit 0)] = true := by decide
example : prepared rootScope [fn "helper" [] ["r"] [assign "r" (path "s1" ["slot"])],
    pop (call "helper" [])] = true := by decide
example : prepared rootScope [pop (call "helper" []),
    fn "helper" [] ["r"] [assign "r" (path "s1" ["slot"])]] = true := by decide
example : prepared rootScope [fn "helper" [] ["r"] [assign "r" (varExpr "a")]] = false := by decide
example : prepared rootScope [fn "helper" [] [] [assign "a" (lit 0)]] = false := by decide
example : prepared rootScope [decl "outer" (lit 1),
    fn "helper" [] ["r"] [assign "r" (varExpr "outer")]] = false := by decide
example : prepared rootScope [fn "helper" ["own"] ["r"]
    [assign "r" (call "add" [varExpr "own", path "s0" ["slot"]])]] = true := by decide
example : prepared rootScope [fn "helper" [] ["r"] [assign "r" (path "s0.slot" [])]] = false := by decide
example : prepared rootScope [fn "outer" [] [] [
    fn "inner" [] ["r"] [assign "r" (path "s1" ["slot"])], pop (call "inner" [])]] = true := by decide
example : prepared rootScope [fn "outer" ["own"] [] [
    fn "inner" [] ["r"] [assign "r" (varExpr "own")]]] = false := by decide
example : prepared rootScope [pop (call "helper" []), fn "helper" ["arg"] ["r"] []] =
    false := by decide
example : prepared rootScope [decl "result" (call "helper" []), fn "helper" [] [] []] =
    false := by decide
example : prepared rootScope [pop (call "add" [lit 1])] = false := by decide
example : prepared rootScope [decl "huge" (lit (2^256))] = false := by decide
example : prepared rootScope [.yulBreak] = false := by decide
example : prepared rootScope [.yulContinue] = false := by decide
example : prepared rootScope [.yulLeave] = false := by decide
example : prepared rootScope [fn "helper" [] [] [.yulLeave]] = true := by decide
example : prepared rootScope [loop [decl "i" (path "s0" ["slot"])] (varExpr "i")
    [assign "i" (call "sub" [varExpr "i", lit 1])] [.yulContinue]] = true := by decide
example : prepared rootScope [loop [decl "i" (lit 1)] (varExpr "i") [] [], pop (varExpr "i")] =
    false := by decide
example : prepared rootScope [loop [fn "bad" [] [] []] (lit 0) [] []] = false := by decide
example : prepared rootScope [switch (path "s0" ["slot"]) [.dec 0, .dec 1]] = true := by decide
example : prepared rootScope [switch (path "s0" ["slot"]) [.dec 0, .dec 0]] = false := by decide
example : prepared rootScope [decl "x" (lit 1), assign "x" (varExpr "x")] = true := by decide
example : prepared .closed mulDiv = true := by decide
example : prepared .closed [assign "a" (lit 1)] = false := by decide
example : prepared .closed mutualCalls = true := by decide

def source := list [decl "copy" (path "s0" ["slot"]), assign "a" (varExpr "copy")]
def witness := (ScopedBlockTyping.checkBlock rootScope rootEnv normal source).get (by decide)
theorem inhabited : Nonempty (ScopedBlockTyping.BlockD rootScope rootEnv normal source) := ⟨witness⟩

def expected : Stmt [] Before.types normal 0 :=
  .let_ 1 (.external ⟨.there .here, .slot, .slotRead⟩)
    (.assign (fun _ : Fin 1 => .external ⟨.here, .plain, .valueWrite⟩) (.local 0))
example : witness.code = expected := by
  apply congrArg (Stmt.let_ 1 (.external ⟨.there .here, .slot, .slotRead⟩))
  apply congrArg (fun targets : Fin 1 → Target Before.types 1 =>
    Stmt.assign targets (.local 0))
  funext position
  exact Fin.cases rfl (fun impossible => Fin.elim0 impossible) position
example : ScopedBlockTyping.checkBlock rootScope rootEnv normal source = some witness := witness.complete

abbrev signature : Sig := ⟨0, 1⟩
def functionSource := list [pop (call "helper" []),
  fn "helper" [] ["r"] [assign "r" (path "s1" ["slot"])]]
def functionWitness := (ScopedBlockTyping.checkBlock rootScope rootEnv normal functionSource).get
  (by decide)
theorem function_inhabited :
    Nonempty (ScopedBlockTyping.BlockD rootScope rootEnv normal functionSource) := ⟨functionWitness⟩
def expectedFunction : Stmt [] Before.types normal 0 :=
  .functions [signature]
    (.cons (.assign (fun _ : Fin 1 => .local 0)
      (.external ⟨.there .here, .slot, .slotRead⟩)) .nil)
    (.discard (.builtin .pop (fun _ => .call .here Fin.elim0)))
private theorem congrTwo {α β γ : Type} (f : α → β → γ)
    {a b : α} {c d : β} (one : a = b) (two : c = d) : f a c = f b d := by
  cases one
  cases two
  rfl
example : functionWitness.code = expectedFunction := by
  apply congrTwo (Stmt.functions [signature])
  · apply congrArg (fun body => Bodies.cons body
      (.nil : Bodies [signature] (globals Before.types) []))
    apply congrArg (fun targets : Fin 1 → Target (globals Before.types) 1 =>
      Stmt.assign targets (.external ⟨.there .here, .slot, .slotRead⟩))
    funext position
    exact Fin.cases rfl (fun impossible => Fin.elim0 impossible) position
  · apply congrArg Stmt.discard
    apply congrArg (Expr.builtin .pop)
    funext position
    exact Fin.cases rfl (fun impossible => Fin.elim0 impossible) position
example : Policy.checkStmt .A witness.code = .error (.needsTier .B) := rfl
example : (Policy.checkStmt .B witness.code).isOk = true := by decide

/-- The empty specialization preserves actual old entry signatures/results by
definition; existing rfl-linked AST and compiled horizon controls also rerun. -/
example {F n} (E : Solidity.Yul.BlockTyping.Env F n) (c : Control) (body : Syn (.list .yulStmt)) :
    ScopedBlockTyping.checkBlock .closed E c body = Solidity.Yul.BlockTyping.checkBlock E c body := rfl
example : (BlockScope.Scope.closed.function : BlockScope.Scope []) = .closed := rfl
example : rootScope.function = .external Before.checked (.function Before.root) := rfl

end Solidity.Yul.Checks.ScopedBlocks
