import Solidity.Yul.WordSyntax
import Solidity.Yul.Checks.BlockTyping
namespace Solidity.Yul.Checks.BlockExtract
open Solidity.Source (Syn)
open Solidity.Yul.BlockTyping
open Solidity.Yul.Closed
open Solidity.Yul.Checks.BlockTyping

def outEnv : Env [] 1 := ClosedSyntax.rootEnv.extend ["out"]
def twoEnv : Env [] 2 := ClosedSyntax.rootEnv.extend ["out", "keep"]

/-- These are existing YUL locals from an enclosing scope, not substituted
Solidity externalReferences or a Source state/dirty-word embedding. -/
def emitted {n} (E : Env [] n) (c : Control) (body : List (Syn .yulStmt))
    (accepted : (checkBlock E c (list body)).isSome = true) : Stmt [] [] c n :=
  ((checkBlock E c (list body)).get accepted).code

def run {n} (E : Env [] n) (c : Control) (body : List (Syn .yulStmt))
    (accepted : (checkBlock E c (list body)).isSome = true)
    (policy : Policy.checkStmt .A (emitted E c body accepted) = .ok ())
    (fuel : Nat) (vars : Values n) : Option (Outcome c n) :=
  evalStmt fuel .nil True.intro (emitted E c body accepted)
    (checked_stmt_words _ policy) vars

def normal : Control := ⟨false, false⟩
def inFunction : Control := ⟨true, false⟩

def mulDivBody : List (Syn .yulStmt) := [
  assign "out" (call "mulDiv" [lit 7, lit 11, lit 3]),
  fn "mulDiv" ["a", "b", "d"] ["r"] [
    assign "r" (call "div" [call "mul" [varExpr "a", varExpr "b"], varExpr "d"])]]
def sameArity : List (Syn .yulStmt) := [
  fn "first" [] ["r"] [assign "r" (lit 11)],
  fn "second" [] ["r"] [assign "r" (lit 22)],
  assign "out" (call "sub" [call "second" [], call "first" []])]
def triple : List (Syn .yulStmt) := [
  fn "triple" ["a", "b"] ["x", "y", "z"] [
    assign "x" (varExpr "b"), assign "y" (varExpr "a"), .yulLeave, assign "z" (lit 99)],
  .yulLet "left" ["middle", "last"] (.some (call "triple" [lit 2, lit 7])),
  assign "out" (call "add" [call "mul" [varExpr "left", lit 100],
    call "add" [call "mul" [varExpr "middle", lit 10], varExpr "last"]])]
def pairInit : List (Syn .yulStmt) := [
  fn "initial" [] ["counter", "seed"] [
    assign "counter" (lit 3), assign "seed" (lit 5)],
  loop [.yulLet "i" ["base"] (.some (call "initial" []))] (varExpr "i")
    [assign "i" (call "sub" [varExpr "i", lit 1])]
    [assign "out" (call "add" [varExpr "out", call "add" [varExpr "i", varExpr "base"]]),
      .yulContinue],
  assign "out" (call "add" [varExpr "out", lit 100])]
def nestedInit : List (Syn .yulStmt) := [
  loop [decl "i" (lit 2),
    loop [decl "j" (lit 2)] (varExpr "j")
      [assign "j" (call "sub" [varExpr "j", lit 1])]
      [assign "out" (call "add" [varExpr "out", lit 10])]]
    (varExpr "i") [assign "i" (call "sub" [varExpr "i", lit 1])]
    [assign "out" (call "add" [varExpr "out", lit 1]), .yulContinue],
  assign "out" (call "add" [varExpr "out", lit 100])]
def nestedBody : List (Syn .yulStmt) := [
  loop [decl "i" (lit 2)] (varExpr "i")
    [assign "i" (call "sub" [varExpr "i", lit 1])]
    [loop [decl "j" (lit 2)] (varExpr "j")
      [assign "j" (call "sub" [varExpr "j", lit 1])]
      [assign "out" (call "add" [varExpr "out", lit 10]), .yulContinue],
     assign "out" (call "add" [varExpr "out", lit 1]), .yulContinue],
  assign "out" (call "add" [varExpr "out", lit 100])]
def earlyLeave : List (Syn .yulStmt) := [
  loop [decl "scratch" (lit 9), assign "out" (lit 257), .yulLeave] (lit 1) [] [],
  assign "out" (lit 999)]
def breakSkipsPost : List (Syn .yulStmt) := [
  loop [decl "counter" (lit 3)] (lit 1) [assign "out" (lit 999)]
    [assign "out" (lit 257), .yulBreak],
  assign "out" (call "add" [varExpr "out", lit 1])]


/-- Reviewable intrinsic caches, each linked to ACTUAL extraction below.
They avoid recomputing source typing metadata during every loop iteration. -/
def arg2 {F n} (left right : Expr F [] n 1) : Fin 2 → Expr F [] n 1 :=
  Fin.cases left (Fin.cases right Fin.elim0)
def binary {F n} (op : Pure 2) (left right : Expr F [] n 1) : Expr F [] n 1 :=
  .builtin (.pure op) (arg2 left right)
def targetOne {n} (position : Fin n) : Fin 1 → Target [] n :=
  Fin.cases (.local position) Fin.elim0
def set {F c n} (position : Fin n) (expression : Expr F [] n 1) : Stmt F [] c n :=
  .assign (targetOne position) expression
def plusAt {F c n} (position : Fin n) (value : Nat) : Stmt F [] c n :=
  set position (binary .add (.local position) (.literal (word value)))
def decrement {F c n} (position : Fin n) : Stmt F [] c n :=
  set position (binary .sub (.local position) (.literal (word 1)))

abbrev initialSig : Sig := ⟨0, 2⟩
def pairInitCache : Stmt [] [] normal 1 :=
  .functions [initialSig]
    (.cons (.seq (set 0 (.literal (word 3))) (set 1 (.literal (word 5)))) .nil)
    (.seq
      (.let_ 2 (.call .here Fin.elim0)
        (.for_ .skip (.local 0) (decrement 0)
          (.seq (set 2 (binary .add (.local 2) (binary .add (.local 0) (.local 1)))) .continue_)))
      (plusAt 0 100))

def pairInitTwoCache : Stmt [] [] normal 2 :=
  .functions [initialSig]
    (.cons (.seq (set 0 (.literal (word 3))) (set 1 (.literal (word 5)))) .nil)
    (.seq
      (.let_ 2 (.call .here Fin.elim0)
        (.for_ .skip (.local 0) (decrement 0)
          (.seq (set 2 (binary .add (.local 2) (binary .add (.local 0) (.local 1)))) .continue_)))
      (plusAt 0 100))

def nestedInitCache : Stmt [] [] normal 1 :=
  .seq
    (.let_ 1 (.literal (word 2))
      (.seq
        (.let_ 1 (.literal (word 2))
          (.for_ .skip (.local 0) (decrement 0) (plusAt 2 10)))
        (.for_ .skip (.local 0) (decrement 0) (.seq (plusAt 1 1) .continue_))))
    (plusAt 0 100)

def nestedBodyCache : Stmt [] [] normal 1 :=
  .seq
    (.let_ 1 (.literal (word 2))
      (.for_ .skip (.local 0) (decrement 0)
        (.seq
          (.let_ 1 (.literal (word 2))
            (.for_ .skip (.local 0) (decrement 0) (.seq (plusAt 2 10) .continue_)))
          (.seq (plusAt 1 1) .continue_))))
    (plusAt 0 100)

theorem pairInit_cache :
    emitted outEnv normal pairInit (by decide) = pairInitCache := rfl
theorem pairInitTwo_cache :
    emitted twoEnv normal pairInit (by decide) = pairInitTwoCache := rfl
theorem nestedInit_cache :
    emitted outEnv normal nestedInit (by decide) = nestedInitCache := rfl
theorem nestedBody_cache :
    emitted outEnv normal nestedBody (by decide) = nestedBodyCache := rfl

/-- Code equality plus erased profile evidence preserves the EXACT horizon.
The case equalities above are proved, not assumed as a replacement for execution. -/
theorem run_cache {n} (E : Env [] n) (c : Control) (body : List (Syn .yulStmt))
    (accepted : (checkBlock E c (list body)).isSome = true)
    (policy : Policy.checkStmt .A (emitted E c body accepted) = .ok ())
    (cached : Stmt [] [] c n) (same : emitted E c body accepted = cached)
    (cachedPolicy : Policy.checkStmt .A cached = .ok ())
    (fuel : Nat) (vars : Values n) :
    run E c body accepted policy fuel vars =
      evalStmt fuel .nil True.intro cached (checked_stmt_words _ cachedPolicy) vars := by
  cases same
  rfl


/-- Completed observations are stable at the original requested horizon.
The smaller execution below is proved, not assumed; no fuel/budget is raised. -/
theorem observe_stable {c n α lo hi} (bound : lo ≤ hi) (code : Stmt [] [] c n)
    (profile : StmtWordP code) (vars : Values n) (observe : Outcome c n → α)
    (expected : α)
    (done : (evalStmt lo .nil True.intro code profile vars).map observe = some expected) :
    (evalStmt hi .nil True.intro code profile vars).map observe = some expected := by
  rcases Option.map_eq_some_iff.mp done with ⟨result, ran, observed⟩
  rw [evalStmt_stable bound .nil True.intro code profile vars ran]
  exact congrArg some observed

/-- All runtime scenarios also pass actual source shape/declaration/placement
components. The supplied initial scope is the explicitly constructed Yul scope. -/
def sourceLegal (visible : List String) (c : Control) (body : List (Syn .yulStmt)) : Bool :=
  (list body).prec &&
  (DeclarationScope.checkBlock [] visible (list body)).isSome &&
  (Placement.check ⟨c.function, if c.loop then .body else .outside⟩ (list body)).toOption.isSome

example : [mulDivBody, sameArity, triple, pairInit, nestedInit, nestedBody, breakSkipsPost].all
    (sourceLegal ["out"] normal) = true := by decide
example : sourceLegal ["out"] inFunction earlyLeave = true := by decide
example : sourceLegal ["out", "keep"] normal pairInit = true := by decide

example : (run outEnv normal mulDivBody (by decide) (by rfl) 32 (fun _ => word 0)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (25, true) := by decide
example : (run outEnv normal sameArity (by decide) (by rfl) 32 (fun _ => word 0)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (11, true) := by decide
example : (run outEnv normal triple (by decide) (by rfl) 32 (fun _ => word 257)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (720, true) := by decide
example : (run outEnv normal pairInit (by decide) (by rfl) 32 (fun _ => word 10)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (131, true) := by
  rw [run_cache _ _ _ _ _ _ pairInit_cache (by rfl)]
  decide
example : (run outEnv normal nestedInit (by decide) (by rfl) 32 (fun _ => word 1)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (123, true) := by
  rw [run_cache _ _ _ _ _ _ nestedInit_cache (by rfl)]
  decide
example : (run outEnv normal nestedBody (by decide) (by rfl) 32 (fun _ => word 1)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (143, true) := by
  rw [run_cache _ _ _ _ _ _ nestedBody_cache (by rfl)]
  apply observe_stable (lo := 16) (by decide)
  decide +kernel
example : (run outEnv inFunction earlyLeave (by decide) (by rfl) 32 (fun _ => word 17)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (257, false) := by decide
example : (run outEnv inFunction earlyLeave (by decide) (by rfl) 32 (fun _ => word 17)).map
    (fun result => result.flow) = some (.leave_ rfl) := rfl
example : (run outEnv normal breakSkipsPost (by decide) (by rfl) 32 (fun _ => word 0)).map
    (fun result => ((result.vars 0).val, result.flow.isNormal)) = some (258, true) := by decide

def initialTwo : Values 2 := Fin.cases (word 10) (fun _ => word (2 ^ 256 - 1))
example : (run twoEnv normal pairInit (by decide) (by rfl) 32 initialTwo).map
    (fun result => ((result.vars 0).val, (result.vars 1).val, result.flow.isNormal)) =
    some (131, 2 ^ 256 - 1, true) := by
  rw [run_cache _ _ _ _ _ _ pairInitTwo_cache (by rfl)]
  decide

def oneAssignment : List (Syn .yulStmt) := [assign "out" (lit 257)]
example : emitted outEnv normal oneAssignment (by decide) =
    .assign (fun _ : Fin 1 => .local 0) (.literal (word 257)) := by
  apply congrArg (fun targets : Fin 1 → Target [] 1 =>
    Stmt.assign (c := normal) targets (.literal (word 257)))
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i
example : (run outEnv normal oneAssignment (by decide) (by rfl) 1 (fun _ => word 0)) =
    none := rfl
example : (run outEnv normal oneAssignment (by decide) (by rfl) 2 (fun _ => word 0)).map
    (fun result => (result.vars 0).val) = some 257 := by decide
example : emitted outEnv normal [] (by decide) = .skip := rfl

/-- Full words remain full words through actual source-derived local reads.
This is a Yul word guard, not a Source narrow-bool/pipeline theorem. -/
def highGuard : List (Syn .yulStmt) :=
  [.yulIf (varExpr "keep") (list [assign "out" (lit 257)])]
example : sourceLegal ["out", "keep"] normal highGuard = true := by decide
def highState : Values 2 := Fin.cases (word 10) (fun _ => word (2 ^ 255))
example : (run twoEnv normal highGuard (by decide) (by rfl) 16 highState).map
    (fun result => ((result.vars 0).val, (result.vars 1).val, result.flow.isNormal)) =
    some (257, 2 ^ 255, true) := by decide

end Solidity.Yul.Checks.BlockExtract
