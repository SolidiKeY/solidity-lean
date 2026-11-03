import Solidity.Yul.WordRules
import Solidity.Yul.Checks.WordTerms
import Solidity.Yul.DeclarationCheck
namespace Solidity.Yul.Checks.WordBranches
open Solidity.Yul.Closed Solidity.Yul.Logic
open Solidity (Modality)
open scoped Solidity.Yul.Logic

def empty : Model [] := ⟨.nil,True.intro⟩
def literal {F n} (value : Word) : Term F n 1 := ⟨.literal value,True.intro⟩
def initial : Values 2 := fun i => if i=0 then word 257 else word 9
def unchanged : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow.isNormal = true ∧ vars 0 = word 257 ∧ vars 1 = word 9
def divergentBody : Program [WordTerms.sig] ⟨false,false⟩ 2 :=
  .assignment WordTerms.targets WordTerms.recursiveTerm

/-- Zero condition skips an actually divergent branch, under either modality. -/
example (mode : Modality) :
    (Fml.modal mode WordTerms.recursiveModel (Program.if_ (literal (word 0)) divergentBody)
      unchanged).holds initial := by
  apply (Rule.sound (.yulIf mode WordTerms.recursiveModel (literal (word 0)) divergentBody unchanged) initial).mpr
  apply (term_completed mode WordTerms.recursiveModel (literal (word 0)) _ initial
    (fun _ => word 0) (fuel := 1) rfl).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

def localCondition : Term [] 2 1 := ⟨.local 0,True.intro⟩
def rawBody : Program [] ⟨false,false⟩ 2 := .literalAssignment 1 (word 2)
def rawPost : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow.isNormal = true ∧ vars 0 = word 257 ∧ vars 1 = word 2
example (mode : Modality) :
    (Fml.modal mode empty (Program.if_ localCondition rawBody) rawPost).holds initial := by
  apply (Rule.sound (.yulIf mode empty localCondition rawBody rawPost) initial).mpr
  apply (term_completed mode empty localCondition _ initial (fun _ => word 257) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty rawBody rawPost).holds initial
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 1 (word 2) rawPost) initial).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

/-- All nonzero words are true, including only the highest bit. -/
example (mode : Modality) :
    (Fml.modal mode empty (Program.if_ (literal (word (2^255))) rawBody) rawPost).holds initial := by
  apply (Rule.sound (.yulIf mode empty (literal (word (2^255))) rawBody rawPost) initial).mpr
  apply (term_completed mode empty (literal (word (2^255))) _ initial
    (fun _ => word (2^255)) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty rawBody rawPost).holds initial
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 1 (word 2) rawPost) initial).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

theorem recursive_box_any (post : Values 1 → Solidity.Yul.Logic.Fml 2) :
    (Fml.termModal .box WordTerms.recursiveModel WordTerms.recursiveTerm post).holds initial := by
  intro fuel result ran
  change evalExpr fuel WordTerms.recursiveEnv WordTerms.recursiveEnvD.profile
    WordTerms.recursiveCall WordTerms.recursiveCallD.profile initial = some result at ran
  rw [WordTerms.recursive_all] at ran
  cases ran
theorem recursive_no_diamond_any (post : Values 1 → Solidity.Yul.Logic.Fml 2) :
    ¬ (Fml.termModal .diamond WordTerms.recursiveModel WordTerms.recursiveTerm post).holds initial := by
  rintro ⟨fuel,result,ran,_⟩
  change evalExpr fuel WordTerms.recursiveEnv WordTerms.recursiveEnvD.profile
    WordTerms.recursiveCall WordTerms.recursiveCallD.profile initial = some result at ran
  rw [WordTerms.recursive_all] at ran
  cases ran

/-- Divergent conditions cannot take either branch or fabricate a completion. -/
example : (Fml.modal .box WordTerms.recursiveModel
    (Program.if_ WordTerms.recursiveTerm
      (Program.literalAssignment (c := ⟨false,false⟩) 0 (word 7)))
    (fun _ => .atom fun _ => False)).holds initial :=
  (Rule.sound (.yulIf .box WordTerms.recursiveModel _ _ _) initial).mpr (recursive_box_any _)
example : ¬ (Fml.modal .diamond WordTerms.recursiveModel
    (Program.if_ WordTerms.recursiveTerm
      (Program.literalAssignment (c := ⟨false,false⟩) 0 (word 7)))
    (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  exact recursive_no_diamond_any _
    ((Rule.sound (.yulIf .diamond WordTerms.recursiveModel _ _ _) initial).mp actual)

/-- Selected divergent branch: no zero-condition/fallback completion. -/
example : (Fml.modal .box WordTerms.recursiveModel (Program.if_ (literal (word 1)) divergentBody)
    (fun _ => .atom fun _ => False)).holds initial := by
  apply (Rule.sound (.yulIf .box WordTerms.recursiveModel _ _ _) initial).mpr
  apply (term_completed .box WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal .box WordTerms.recursiveModel divergentBody _).holds initial
  exact (Rule.sound (.yulAssign .box WordTerms.recursiveModel _ _ _) initial).mpr (recursive_box_any _)
example : ¬ (Fml.modal .diamond WordTerms.recursiveModel (Program.if_ (literal (word 1)) divergentBody)
    (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  have cond := (Rule.sound (.yulIf .diamond WordTerms.recursiveModel _ _ _) initial).mp actual
  have selected := (term_completed .diamond WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mp cond
  change (Fml.modal .diamond WordTerms.recursiveModel divergentBody _).holds initial at selected
  exact recursive_no_diamond_any _
    ((Rule.sound (.yulAssign .diamond WordTerms.recursiveModel _ _ _) initial).mp selected)

def copied (value : Word) : Flow ⟨true,false⟩ → Solidity.Yul.Logic.Fml 1 :=
  fun flow => .atom fun vars => flow.isNormal = false ∧ vars 0 = value
def frontRead : Term [] 2 1 := ⟨.local 0,True.intro⟩
def copyThenLeave : Program [] ⟨true,false⟩ 2 :=
  (Program.assignment (fun _ : Fin 1 => .local 1) frontRead).sequence Program.leave

theorem copy_leave (mode : Modality) (front old : Word) :
    (Fml.modal mode empty copyThenLeave (dropPost 1 (copied front))).holds
      (extendValues (fun _ : Fin 1 => front) (fun _ : Fin 1 => old)) := by
  apply (Rule.sound (.yulSequence mode empty _ _ _) _).mpr
  apply (Rule.sound (.yulAssign mode empty _ frontRead _) _).mpr
  apply (term_completed mode empty frontRead _
    (extendValues (fun _ : Fin 1 => front) (fun _ : Fin 1 => old))
    (fun _ => front) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty Program.leave (dropPost 1 (copied front))).holds _
  apply (Rule.sound (.yulLeave mode empty _) _).mpr
  exact ⟨rfl,rfl⟩

/-- The initialized binder drops only its fresh slot, retaining the old-slot write AND leave. -/
example (mode : Modality) :
    (Fml.modal mode empty (Program.let_ (literal (word 257)) copyThenLeave)
      (copied (word 257))).holds (fun _ => word 9) := by
  apply (Rule.sound (.yulLet (n := 1) (r := 1) mode empty (literal (word 257)) copyThenLeave _) _).mpr
  apply (term_completed mode empty (literal (word 257)) _ (fun _ => word 9)
    (fun _ => word 257) (fuel := 1) rfl).mpr
  exact copy_leave mode (word 257) (word 9)
example (mode : Modality) :
    (Fml.modal mode empty (Program.zero 1 copyThenLeave) (copied (word 0))).holds (fun _ => word 9) :=
  (Rule.sound (.yulZero (n := 1) mode empty 1 copyThenLeave _) _).mpr (copy_leave mode (word 0) (word 9))

def loopPost (wanted : Flow ⟨false,true⟩) : Flow ⟨false,true⟩ → Solidity.Yul.Logic.Fml 1 :=
  fun flow => .atom fun vars => flow = wanted ∧ vars 0 = word 9
example (mode : Modality) :
    (Fml.modal mode empty (Program.zero 1 (Program.break_ (fn := false) (n := 2)))
      (loopPost (.break_ rfl))).holds (fun _ : Fin 1 => word 9) := by
  apply (Rule.sound (.yulZero (n := 1) mode empty 1 _ (loopPost (.break_ rfl))) _).mpr
  change (Fml.modal mode empty (Program.break_ (fn := false) (n := 2))
    (dropPost 1 (loopPost (.break_ rfl)))).holds (extendValues (fun _ : Fin 1 => word 0) (fun _ : Fin 1 => word 9))
  apply (Rule.sound (.yulBreak mode empty _) _).mpr
  exact ⟨rfl,rfl⟩
example (mode : Modality) :
    (Fml.modal mode empty (Program.zero 1 (Program.continue_ (fn := false) (n := 2)))
      (loopPost (.continue_ rfl))).holds (fun _ : Fin 1 => word 9) := by
  apply (Rule.sound (.yulZero (n := 1) mode empty 1 _ (loopPost (.continue_ rfl))) _).mpr
  change (Fml.modal mode empty (Program.continue_ (fn := false) (n := 2))
    (dropPost 1 (loopPost (.continue_ rfl)))).holds (extendValues (fun _ : Fin 1 => word 0) (fun _ : Fin 1 => word 9))
  apply (Rule.sound (.yulContinue mode empty _) _).mpr
  exact ⟨rfl,rfl⟩

/-- A divergent initializer cannot execute even a skip body. -/
example : (Fml.modal .box WordTerms.recursiveModel
    (Program.let_ WordTerms.recursiveTerm (Program.skip (c := ⟨false,false⟩)))
    (fun _ => .atom fun _ => False)).holds initial :=
  (Rule.sound (.yulLet .box WordTerms.recursiveModel _ _ _) initial).mpr (recursive_box_any _)
example : ¬ (Fml.modal .diamond WordTerms.recursiveModel
    (Program.let_ WordTerms.recursiveTerm (Program.skip (c := ⟨false,false⟩)))
    (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  exact recursive_no_diamond_any _
    ((Rule.sound (.yulLet .diamond WordTerms.recursiveModel _ _ _) initial).mp actual)

example : checkNames ["x"] ["x"] = false := by decide
example : checkNames [] ["x","x"] = false := by decide
example : checkNames [] ["mload"] = false := by decide
example : ruleIds.length = 20 := ruleIds_count
example : Rule.id (.yulIf .box empty localCondition rawBody rawPost) = .yulIf := rfl
example : Rule.id (.yulZero (n := 1) .diamond empty 1 copyThenLeave (copied (word 0))) = .yulZero := rfl
example : Rule.id (.yulLet (n := 1) (r := 1) .box empty (literal (word 257)) copyThenLeave (copied (word 257))) = .yulLet := rfl


def pairBody : Program [Assignments.sig] ⟨false,false⟩ 4 :=
  (Program.assignment (fun _ : Fin 1 => .local 2) (⟨.local 0,True.intro⟩ : Term _ 4 1)).sequence
    (Program.assignment (fun _ : Fin 1 => .local 3) (⟨.local 1,True.intro⟩ : Term _ 4 1))
def pairPost : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow.isNormal = true ∧ vars 0 = word 11 ∧ vars 1 = word 22
def pairInitial : Values 4 := extendValues WordUpdates.returned WordUpdates.callerVars
def pairOutcome : Outcome ⟨false,false⟩ 4 :=
  (evalStmt 12 WordTerms.pairModel.environment WordTerms.pairModel.words pairBody.code pairBody.words
    pairInitial).get (by decide)
theorem pairBodyCompleted :
    evalStmt 12 WordTerms.pairModel.environment WordTerms.pairModel.words pairBody.code pairBody.words
      pairInitial = some pairOutcome := (Option.some_get (by decide)).symm
example (mode : Modality) :
    (Fml.modal mode WordTerms.pairModel (Program.let_ WordTerms.pairTerm pairBody)
      pairPost).holds WordUpdates.callerVars := by
  apply (Rule.sound (.yulLet (n := 2) (r := 2) mode WordTerms.pairModel WordTerms.pairTerm pairBody pairPost) _).mpr
  apply (term_completed mode WordTerms.pairModel WordTerms.pairTerm _ WordUpdates.callerVars
    WordUpdates.returned (fuel := 9) WordUpdates.completed).mpr
  change (Fml.modal mode WordTerms.pairModel pairBody (dropPost 2 pairPost)).holds pairInitial
  apply (modal_completed mode WordTerms.pairModel pairBody (dropPost 2 pairPost)
    pairInitial pairOutcome (fuel := 12) pairBodyCompleted).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide
example : (evalStmt 14 WordTerms.pairModel.environment WordTerms.pairModel.words
    (Program.let_ WordTerms.pairTerm pairBody).code (Program.let_ WordTerms.pairTerm pairBody).words
    WordUpdates.callerVars).map (fun out => ((out.vars 0).val,(out.vars 1).val)) = some (11,22) := by decide
example (mode : Modality) :
    (Fml.modal mode empty (Program.zero 0 (Program.skip (c := ⟨false,false⟩))) unchanged).holds initial := by
  apply (Rule.sound (.yulZero (n := 2) mode empty 0 _ unchanged) initial).mpr
  change (Fml.modal mode empty (Program.skip (c := ⟨false,false⟩)) (dropPost 0 unchanged)).holds _
  apply (Rule.sound (.yulSkip mode empty _) _).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

end Solidity.Yul.Checks.WordBranches
