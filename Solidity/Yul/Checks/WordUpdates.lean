import Solidity.Yul.WordUpdates
import Solidity.Yul.Checks.Assignments
namespace Solidity.Yul.Checks.WordUpdates
open Solidity.Yul.Closed

def vars : Values 3 := fun i => word (100+i.val)
def values : Values 3 := fun i => if i=0 then word 17 else if i=1 then word 257 else word (2^256-1)
def positions : Fin 3 → Fin 3 := fun i => if i=0 then 2 else if i=1 then 0 else 1
theorem distinct : Function.Injective positions := by
  unfold Function.Injective
  decide
example (i : Fin 3) :
    writeValues 3 (fun j => .local (positions j)) values vars (positions i) = values i :=
  writeValues_at 3 positions distinct values vars i
example : (writeValues 3 (fun j => .local (positions j)) values vars 0).val = 257 := by decide
example : (writeValues 3 (fun j => .local (positions j)) values vars 1).val = 2^256-1 := by decide
example : (writeValues 3 (fun j => .local (positions j)) values vars 2).val = 17 := by decide

example : writeValues 2 (fun i => .local (i.castSucc : Fin 3)) (fun i => word (i.val+7)) vars 2 =
    vars 2 := writeValues_outside 2 _ _ _ _ (by decide)
example : writeTarget (.local (0 : Fin 3)) (word 257) vars 0 = word 257 :=
  writeTarget_same _ _ _
example : writeTarget (.local (0 : Fin 3)) (word (2^256-1)) vars 0 = word (2^256-1) :=
  writeTarget_same _ _ _
example : writeTarget (.local (0 : Fin 3)) (word 257) vars 2 = vars 2 :=
  writeTarget_other _ _ _ _ (by decide)

/-- Duplicate targets have no injectivity law; the evaluator's existing order
writes the lower operand last. They are refused by actual source-path checking
when spelling is duplicated. No silent semantic order change is made. -/
def duplicate : Fin 2 → Fin 1 := fun _ => 0
example : ¬ Function.Injective duplicate := by
  unfold Function.Injective
  decide
example : (writeValues 2 (fun i => .local (duplicate i))
    (fun i => if i=0 then word 11 else word 22) (fun _ => word 99) 0).val = 11 := by decide

def literal (w : Word) : Stmt [] [] ⟨false,false⟩ 3 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal w)
def literalD (w : Word) : WordStmtD (literal w) := .assign .literal
example : (evalStmt 2 .nil True.intro (literal (word 257)) (literalD _).profile vars).map
    (fun out => (out.vars 0).val) = some 257 := by decide
example : (evalStmt 2 .nil True.intro (literal (word 257)) (literalD _).profile vars).map
    (fun out => (out.vars 2).val) = some 102 := by decide
example : (evalStmt 1 .nil True.intro (literal (word 257)) (literalD _).profile vars).isNone = true := by decide

def quotient : Stmt [] [] ⟨false,false⟩ 3 :=
  .assign (fun _ : Fin 1 => .local 0)
    (.builtin (.pure .div) (fun i => .literal (if i=0 then word (2^256-1) else word 0)))
def quotientD : WordStmtD quotient :=
  .assign (.builtin (.pure .div) (fun _ => .literal))
example : (evalStmt 3 .nil True.intro quotient quotientD.profile vars).map
    (fun out => ((out.vars 0).val, out.flow.isNormal)) = some (0,true) := by decide

/-- A concrete actual function RHS, with the caller result supplied to the
generic landing theorem by its real evaluator equation. -/
def call : Expr [Assignments.sig] [] 2 2 := .call .here Fin.elim0
def callD : WordExprD call := .call .here (fun i => Fin.elim0 i)
def callerVars : Values 2 := fun _ => word 99
def result : Option (Values 2) :=
  evalExpr 9 Assignments.pairEnv Assignments.pairEnvD.profile call callD.profile callerVars
def returned : Values 2 := result.get (by decide)
theorem completed : result = some returned := (Option.some_get (by decide)).symm
example : (returned 0).val = 11 := by decide
example : (returned 1).val = 22 := by decide
def callAssignD : WordStmtD (Stmt.assign (c := ⟨false,false⟩)
    (fun i : Fin 2 => .local i) call) := .assign callD
example (i : Fin 2) :
    (evalStmt 10 Assignments.pairEnv Assignments.pairEnvD.profile
      (.assign (c := ⟨false,false⟩) (fun i : Fin 2 => .local i) call)
      callAssignD.profile callerVars).map (fun out => out.vars i) = some (returned i) :=
  evalStmt_assign_at 9 _ _ (fun i => i) (fun _ _ same => same) call
    callAssignD.profile callerVars returned completed i

/-- Distinct text paths do not prove distinct slots in an ARBITRARY supplied
table. The whole-source environment constructor must establish real coherence. -/
def aliasReads : ExprEnv [Assignments.sig] [] 1 :=
  ⟨[("x",0),("y",0)], [("pair",⟨Assignments.sig,.here⟩)], []⟩
def aliasWrites : TargetEnv [] 1 := ⟨[("x",0),("y",0)], []⟩
example : (checkAssignment aliasReads aliasWrites [["x"],["y"]]
    (Solidity.Source.Syn.yulCall "pair" .nil)).isSome = true := by decide
example : (checkAssignment aliasReads aliasWrites [["x"],["x"]]
    (Solidity.Source.Syn.yulCall "pair" .nil)).isNone = true := by decide


def aliased : AssignmentD aliasReads aliasWrites [["x"],["y"]]
    (Solidity.Source.Syn.yulCall "pair" .nil) :=
  (checkAssignment aliasReads aliasWrites [["x"],["y"]]
    (Solidity.Source.Syn.yulCall "pair" .nil)).get (by decide)
def aliasedD : WordStmtD (aliased.statement ⟨false,false⟩) :=
  .assign (.call .here (fun i => Fin.elim0 i))
example : (evalStmt 10 Assignments.pairEnv Assignments.pairEnvD.profile
    (aliased.statement ⟨false,false⟩) aliasedD.profile (fun _ => word 99)).map
      (fun out => (out.vars 0).val) = some 11 := by decide

end Solidity.Yul.Checks.WordUpdates
