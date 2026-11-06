import Solidity.Yul.AssignmentCheck
import Solidity.Yul.ClosedRun
namespace Solidity.Yul.Checks.Assignments
open Solidity.Source (Syn)
open Solidity.Yul.Closed

def sig : Sig := ⟨0, 2⟩
def locals : List (String × Fin 2) := [("a", 0), ("b", 1)]
def reads : ExprEnv [sig] [.externalFunction, .storage false false, .value (.unsigned 0)] 2 :=
  ⟨locals, [("pair", ⟨sig, .here⟩)], []⟩
def writes : TargetEnv [.externalFunction, .storage false false, .value (.unsigned 0)] 2 :=
  ⟨locals, [("p", ⟨.externalFunction, .here⟩), ("z", ⟨.storage false false, .there .here⟩),
    ("x", ⟨.value (.unsigned 0), .there (.there .here)⟩)]⟩
def pair : Syn .yulExpr := .yulCall "pair" .nil
def lit : Syn .yulExpr := .yulLit (.dec 7)
example : (checkAssignment reads writes [["a"], ["b"]] pair).isSome = true := by decide
example : (checkAssignment reads writes [["a"], ["a"]] pair).isNone = true := by decide
example : (checkAssignment reads writes [["a"]] pair).isNone = true := by decide
example : (checkAssignment reads writes [["a"], ["b"]] lit).isNone = true := by decide
example : (checkAssignment reads writes [["p", "selector"], ["p", "address"]] pair).isSome = true := by decide
example : (checkAssignment reads writes [["p", "selector"], ["p", "selector"]] pair).isNone = true := by decide
example : (checkAssignment reads writes [["z", "slot"]] lit).isNone = true := by decide
example : (checkAssignment reads writes [["z", "offset"]] lit).isNone = true := by decide
example : (checkAssignment reads writes [["p"]] lit).isNone = true := by decide
example : (checkAssignment reads writes [["p", "length"]] lit).isNone = true := by decide
example : (checkAssignment reads writes [["x"]] lit).isSome = true := by decide
example : (checkAssignment reads writes [["missing"]] lit).isNone = true := by decide
example : (checkAssignment reads writes [[]] lit).isNone = true := by decide
example : (checkAssignment reads writes [] lit).isNone = true := by decide
example : (checkAssignment reads writes [["x", "slot", "extra"]] lit).isNone = true := by decide

def storageWrites : TargetEnv [.storage true true] 0 := ⟨[], [("s", ⟨_, .here⟩)]⟩
example : (checkTargetPath storageWrites ["s", "slot"]).isSome = true := by decide
example : (checkTargetPath storageWrites ["s", "offset"]).isNone = true := by decide

def localPosition {X n} : Target X n → Option Nat
  | .«local» i => some i.val
  | .external _ => none
def priority : TargetEnv [.storage false false] 1 :=
  ⟨[("same", 0)], [("same", ⟨_, .here⟩)]⟩
example : (checkTargetPath priority ["same"]).bind
    (fun ⟨target, _⟩ => localPosition target) = some 0 := by decide

/-- Concrete source-expression/assignment construction, not a Source statement embedding. -/
def closedReads : ExprEnv [] [] 1 := ⟨[("a", 0)], [], []⟩
def closedWrites : TargetEnv [] 1 := ⟨[("a", 0)], []⟩
def assigned : AssignmentD closedReads closedWrites [["a"]] lit :=
  ((checkAssignment closedReads closedWrites [["a"]] lit).get (by decide))
def assignedWord : WordStmtD (assigned.statement ⟨false, false⟩) := .assign .literal
example : (evalStmt 3 .nil True.intro (assigned.statement ⟨false, false⟩)
    assignedWord.profile (fun _ => word 99)).map (fun out => (out.vars 0).val) = some 7 := by decide

def multiReads : ExprEnv [sig] [] 2 := ⟨locals, [("pair", ⟨sig, .here⟩)], []⟩
def multiWrites : TargetEnv [] 2 := ⟨locals, []⟩
def multiAssigned : AssignmentD multiReads multiWrites [["a"], ["b"]] pair :=
  (checkAssignment multiReads multiWrites [["a"], ["b"]] pair).get (by decide)
def multiWord : WordStmtD (multiAssigned.statement ⟨false, false⟩) :=
  .assign (.call .here (fun i => Fin.elim0 i))
def pairBody : Stmt [sig] [] ⟨true, false⟩ 2 :=
  .seq (.assign (fun _ => .«local» 0) (.literal (word 11)))
    (.assign (fun _ => .«local» 1) (.literal (word 22)))
def pairBodyD : WordStmtD pairBody := .seq (.assign .literal) (.assign .literal)
def pairEnv : FunctionEnv [sig] := .group [sig] .nil (.cons pairBody .nil)
def pairEnvD : WordEnvD pairEnv := .group .nil (.cons pairBodyD .nil)
/-- Actual checked multi-target extraction must preserve source target order. -/
example : (evalStmt 10 pairEnv pairEnvD.profile (multiAssigned.statement ⟨false, false⟩)
    multiWord.profile (fun _ => word 99)).map
    (fun out => ((out.vars 0).val, (out.vars 1).val)) = some (11, 22) := by decide

end Solidity.Yul.Checks.Assignments
