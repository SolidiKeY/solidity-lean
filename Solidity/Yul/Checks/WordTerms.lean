import Solidity.Yul.WordRules
import Solidity.Yul.Checks.WordUpdates
import Solidity.Yul.Checks.ClosedRun
namespace Solidity.Yul.Checks.WordTerms
open Solidity.Yul.Closed Solidity.Yul.Logic
open Solidity (Modality)
open scoped Solidity.Yul.Logic

def eval : Nat := 7
example : eval = 7 := rfl
def empty : Model [] := ⟨.nil,True.intro⟩
def initial : Values 2 := fun i => if i=0 then word 257 else word 9
def sum : Term [] 2 1 :=
  ⟨.builtin (.pure .add) (fun i => .local i),
    (WordExprD.builtin (.pure .add) (fun i => .local i)).profile⟩
def sumPost : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow.isNormal = true ∧ vars 0 = word 266 ∧ vars 1 = word 9
def targets : Fin 1 → Target [] 2 := fun _ => .local 0
def sumProgram : Program [] ⟨false,false⟩ 2 := .assignment targets sum

example : (evalExpr 1 empty.environment empty.words sum.code sum.words initial).isNone = true := by decide
example : (evalExpr 2 empty.environment empty.words sum.code sum.words initial).map
    (fun values => (values 0).val) = some 266 := by decide
example : (evalStmt 3 empty.environment empty.words sumProgram.code sumProgram.words initial).map
    (fun out => ((out.vars 0).val,(out.vars 1).val)) = some (266,9) := by decide
def sumValues : Values 1 :=
  (evalExpr 2 empty.environment empty.words sum.code sum.words initial).get (by decide)
theorem sumCompleted :
    evalExpr 2 empty.environment empty.words sum.code sum.words initial = some sumValues :=
  (Option.some_get (by decide)).symm

example (mode : Modality) : (dl{ yul mode ; empty ; sumProgram ; sumPost }).holds initial := by
  apply (Rule.sound (.yulAssign mode empty targets sum sumPost) initial).mpr
  apply (term_completed mode empty sum (assignmentPost targets sumPost) initial
    sumValues (fuel := 2) sumCompleted).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

example (mode : Modality) :
    ¬ (dl{ yul mode ; empty ; sumProgram ;
      (fun _ => Solidity.Yul.Logic.Fml.atom (fun vars => vars 0 = word 10)) }).holds initial := by
  intro actual
  have after := (Rule.sound (.yulAssign mode empty targets sum _) initial).mp actual
  have wrong := (term_completed mode empty sum _ initial sumValues
    (fuel := 2) sumCompleted).mp after
  exact (by decide : word 266 ≠ word 10) wrong

def pairModel : Model [Assignments.sig] := ⟨Assignments.pairEnv,Assignments.pairEnvD.profile⟩
def pairTerm : Term [Assignments.sig] 2 2 := ⟨WordUpdates.call,WordUpdates.callD.profile⟩
def pairTargets : Fin 2 → Target [] 2 := fun i => .local i
def pairPost : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow.isNormal = true ∧ vars 0 = word 11 ∧ vars 1 = word 22
example (mode : Modality) :
    (dl{ yul mode ; pairModel ; (Program.assignment pairTargets pairTerm) ; pairPost }).holds
      WordUpdates.callerVars := by
  apply (Rule.sound (.yulAssign mode pairModel pairTargets pairTerm pairPost) _).mpr
  apply (term_completed mode pairModel pairTerm _ WordUpdates.callerVars
    WordUpdates.returned (fuel := 9) WordUpdates.completed).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

def popTerm : Term [] 2 0 :=
  ⟨.builtin .pop (fun _ => .local 0),(WordExprD.builtin .pop (fun _ => .local 0)).profile⟩
example (mode : Modality) :
    (dl{ yul mode ; empty ; (Program.discard (c := ⟨false,false⟩) popTerm) ;
      (fun flow => Solidity.Yul.Logic.Fml.atom fun vars =>
        flow.isNormal = true ∧ vars 0 = word 257 ∧ vars 1 = word 9) }).holds initial := by
  apply (Rule.sound (.yulDiscard mode empty popTerm _) initial).mpr
  apply (term_completed mode empty popTerm _ initial Fin.elim0 (fuel := 2) rfl).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

/-- A nonzero-result recursive call, not a caller termination oracle. -/
def sig : Sig := ⟨0,1⟩
def recursiveCall {n} : Expr [sig] [] n 1 := .call .here Fin.elim0
def recursiveCallD {n} : WordExprD (recursiveCall (n := n)) :=
  .call .here (fun i => Fin.elim0 i)
def recursiveBody : Stmt [sig] [] ⟨true,false⟩ 1 :=
  .assign (fun _ => .local 0) recursiveCall
def recursiveBodyD : WordStmtD recursiveBody := .assign recursiveCallD
def recursiveEnv : FunctionEnv [sig] := .group [sig] .nil (.cons recursiveBody .nil)
def recursiveEnvD : WordEnvD recursiveEnv := .group .nil (.cons recursiveBodyD .nil)
def recursiveModel : Model [sig] := ⟨recursiveEnv,recursiveEnvD.profile⟩
def recursiveTerm {n} : Term [sig] n 1 := ⟨recursiveCall,recursiveCallD.profile⟩

theorem recursive_all (fuel : Nat) {n} (vars : Values n) :
    evalExpr fuel recursiveEnv recursiveEnvD.profile recursiveCall recursiveCallD.profile vars = none := by
  induction fuel using Nat.strongRecOn generalizing n with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ k =>
        change Option.bind (Option.bind
          (evalExpr k recursiveEnv recursiveEnvD.profile recursiveCall recursiveCallD.profile
            (extendValues Fin.elim0 (fun _ : Fin 1 => word 0))) _) _ = none
        rw [ih k (by omega)]
        rfl

theorem recursive_box (vars : Values 2) :
    (Fml.termModal .box recursiveModel recursiveTerm
      (fun _ => .atom (fun _ => False))).holds vars := by
  intro fuel result ran
  change evalExpr fuel recursiveEnv recursiveEnvD.profile recursiveCall recursiveCallD.profile vars =
    some result at ran
  rw [recursive_all] at ran
  cases ran
theorem recursive_not_diamond (vars : Values 2) :
    ¬ (Fml.termModal .diamond recursiveModel recursiveTerm
      (fun _ => .atom (fun _ => True))).holds vars := by
  rintro ⟨fuel,result,ran,_⟩
  change evalExpr fuel recursiveEnv recursiveEnvD.profile recursiveCall recursiveCallD.profile vars =
    some result at ran
  rw [recursive_all] at ran
  cases ran

example : (Fml.modal .box recursiveModel (Program.assignment (c := ⟨false,false⟩) targets recursiveTerm)
    (fun _ => .atom (fun _ => False))).holds initial :=
  (Rule.sound (.yulAssign .box recursiveModel targets recursiveTerm _) initial).mpr
    (recursive_box initial)
example : ¬ (Fml.modal .diamond recursiveModel (Program.assignment (c := ⟨false,false⟩) targets recursiveTerm)
    (fun _ => .atom (fun _ => True))).holds initial := by
  intro actual
  exact recursive_not_diamond initial
    ((Rule.sound (.yulAssign .diamond recursiveModel targets recursiveTerm _) initial).mp actual)

example {F n r} (mode : Modality) (model : Model F) (term : Term F n r)
    (post : Values r → Solidity.Yul.Logic.Fml n) :
    (dl{ yul eval mode ; model ; term => post }) = Fml.termModal mode model term post := rfl
example : ruleIds.length = 20 := ruleIds_count
example : Rule.id (.yulAssign .box empty targets sum sumPost) = .yulAssign := rfl
example : Rule.id (.yulDiscard .diamond empty popTerm sumPost) = .yulDiscard := rfl


/-- Existing source checking still refuses mismatched/duplicate target lists. -/
example : (checkAssignment Assignments.multiReads Assignments.multiWrites
    [["a"]] Assignments.pair).isNone = true := by decide
example : (checkAssignment Assignments.multiReads Assignments.multiWrites
    [["a"],["a"]] Assignments.pair).isNone = true := by decide

def combinedPost : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow.isNormal = true ∧ vars 0 = word 266 ∧ vars 1 = word 257
example (mode : Modality) :
    (Fml.modal mode empty
      (sumProgram.sequence (Program.literalAssignment 1 (word 257))) combinedPost).holds initial := by
  apply (Rule.sound (.yulSequence mode empty sumProgram _ combinedPost) initial).mpr
  apply (Rule.sound (.yulAssign mode empty targets sum _) initial).mpr
  apply (term_completed mode empty sum _ initial sumValues (fuel := 2) sumCompleted).mpr
  change (Fml.modal mode empty (Program.literalAssignment 1 (word 257)) combinedPost).holds
    (writeValues 1 targets sumValues initial)
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 1 (word 257) combinedPost) _).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

def voidModel : Model [ClosedRun.divergeSig] :=
  ⟨ClosedRun.divergeEnv,ClosedRun.divergeEnvD.profile⟩
def voidTerm : Term [ClosedRun.divergeSig] 0 0 :=
  ⟨ClosedRun.divergeCall,ClosedRun.divergeCallD.profile⟩
theorem voidBox :
    (Fml.termModal .box voidModel voidTerm (fun _ => .atom (fun _ => False))).holds Fin.elim0 := by
  intro fuel result ran
  change evalExpr fuel ClosedRun.divergeEnv ClosedRun.divergeEnvD.profile
    ClosedRun.divergeCall ClosedRun.divergeCallD.profile Fin.elim0 = some result at ran
  rw [ClosedRun.diverge_all] at ran
  cases ran
theorem voidNotDiamond :
    ¬ (Fml.termModal .diamond voidModel voidTerm (fun _ => .atom (fun _ => True))).holds Fin.elim0 := by
  rintro ⟨fuel,result,ran,_⟩
  change evalExpr fuel ClosedRun.divergeEnv ClosedRun.divergeEnvD.profile
    ClosedRun.divergeCall ClosedRun.divergeCallD.profile Fin.elim0 = some result at ran
  rw [ClosedRun.diverge_all] at ran
  cases ran
example : (Fml.modal .box voidModel (Program.discard (c := ⟨false,false⟩) voidTerm)
    (fun _ => .atom (fun _ => False))).holds Fin.elim0 :=
  (Rule.sound (.yulDiscard .box voidModel voidTerm _) Fin.elim0).mpr voidBox
example : ¬ (Fml.modal .diamond voidModel (Program.discard (c := ⟨false,false⟩) voidTerm)
    (fun _ => .atom (fun _ => True))).holds Fin.elim0 := by
  intro actual
  exact voidNotDiamond ((Rule.sound (.yulDiscard .diamond voidModel voidTerm _) Fin.elim0).mp actual)

end Solidity.Yul.Checks.WordTerms
