import Solidity.Yul.WordRules
import Solidity.Yul.Checks.WordBranches
namespace Solidity.Yul.Checks.WordSwitch
open Solidity.Yul.Closed Solidity.Yul.Logic
open Solidity (Modality)
open scoped Solidity.Yul.Logic

def empty : Model [] := ⟨.nil,True.intro⟩
def literal {F n} (value : Word) : Term F n 1 := ⟨.literal value,True.intro⟩
def initial : Values 2 := fun i => if i=0 then word 257 else word 9
def first : Program [] ⟨false,false⟩ 2 := .literalAssignment 0 (word 7)
def second : Program [] ⟨false,false⟩ 2 := .literalAssignment 1 (word 257)
def fallback : Program [] ⟨false,false⟩ 2 := .literalAssignment 0 (word 99)
def arms : Cases [] [] ⟨false,false⟩ 2 := .cons (word 1) first.code (.cons (word 2) second.code .nil)
def armsWords : CasesWordP arms := ⟨first.words,second.words,True.intro⟩
def program (value : Word) := Program.switch (literal value) arms armsWords fallback
def run (fuel : Nat) (value : Word) :=
  (evalStmt fuel empty.environment empty.words (program value).code (program value).words initial).map
    (fun out => ((out.vars 0).val,(out.vars 1).val))

example : (selectCase arms armsWords (word 1)).isSome = true := by decide
example : (selectCase arms armsWords (word 2)).isSome = true := by decide
example : (selectCase arms armsWords (word 3)).isNone = true := by decide
example : (selectCase (Cases.nil (F := []) (c := ⟨false,false⟩) (n := 2)) True.intro (word 1)).isNone = true := rfl
example : run 6 (word 1) = some (7,9) := by decide
example : run 6 (word 2) = some (257,257) := by decide
example : run 6 (word 3) = some (99,9) := by decide
example : run 1 (word 1) = none := by decide
example : run 2 (word 1) = none := by decide

def normal (a b : Word) : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow.isNormal = true ∧ vars 0 = a ∧ vars 1 = b
example (mode : Modality) :
    (Fml.modal mode empty (program (word 2)) (normal (word 257) (word 257))).holds initial := by
  apply (Rule.sound (.yulSwitch mode empty _ arms armsWords fallback _) initial).mpr
  apply (term_completed mode empty (literal (word 2)) _ initial (fun _ => word 2) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty second (normal (word 257) (word 257))).holds initial
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 1 (word 257) _) initial).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide
example (mode : Modality) :
    (Fml.modal mode empty (program (word 3)) (normal (word 99) (word 9))).holds initial := by
  apply (Rule.sound (.yulSwitch mode empty _ arms armsWords fallback _) initial).mpr
  apply (term_completed mode empty (literal (word 3)) _ initial (fun _ => word 3) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty fallback (normal (word 99) (word 9))).holds initial
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 99) _) initial).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide
example (mode : Modality) :
    ¬ (Fml.modal mode empty (program (word 1)) (normal (word 99) (word 9))).holds initial := by
  intro actual
  have tested := (Rule.sound (.yulSwitch mode empty _ arms armsWords fallback _) initial).mp actual
  have selected := (term_completed mode empty (literal (word 1)) _ initial (fun _ => word 1) (fuel := 1) rfl).mp tested
  change (Fml.modal mode empty first (normal (word 99) (word 9))).holds initial at selected
  have wrong := (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 7) _) initial).mp selected
  exact (by decide : word 7 ≠ word 99) wrong.2.1

def divergent : Program [WordTerms.sig] ⟨false,false⟩ 2 :=
  .assignment WordTerms.targets WordTerms.recursiveTerm
def good : Program [WordTerms.sig] ⟨false,false⟩ 2 := .literalAssignment 0 (word 257)
def mixed : Cases [WordTerms.sig] [] ⟨false,false⟩ 2 :=
  .cons (word 1) divergent.code (.cons (word 2) good.code .nil)
def mixedWords : CasesWordP mixed := ⟨divergent.words,good.words,True.intro⟩

/-- A selected divergent arm never executes the successful fallback. -/
example : (Fml.modal .box WordTerms.recursiveModel
    (Program.switch (literal (word 1)) mixed mixedWords good)
    (fun _ => .atom fun _ => False)).holds initial := by
  apply (Rule.sound (.yulSwitch .box WordTerms.recursiveModel _ mixed mixedWords good _) initial).mpr
  apply (term_completed .box WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal .box WordTerms.recursiveModel divergent _).holds initial
  exact (Rule.sound (.yulAssign .box WordTerms.recursiveModel _ _ _) initial).mpr
    (WordBranches.recursive_box_any _)
example : ¬ (Fml.modal .diamond WordTerms.recursiveModel
    (Program.switch (literal (word 1)) mixed mixedWords good)
    (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  have tested := (Rule.sound (.yulSwitch .diamond WordTerms.recursiveModel _ mixed mixedWords good _) initial).mp actual
  have selected := (term_completed .diamond WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mp tested
  change (Fml.modal .diamond WordTerms.recursiveModel divergent _).holds initial at selected
  exact WordBranches.recursive_no_diamond_any _
    ((Rule.sound (.yulAssign .diamond WordTerms.recursiveModel _ _ _) initial).mp selected)
example (mode : Modality) :
    (Fml.modal mode WordTerms.recursiveModel
      (Program.switch (literal (word 2)) mixed mixedWords divergent)
      (normal (word 257) (word 9))).holds initial := by
  apply (Rule.sound (.yulSwitch mode WordTerms.recursiveModel _ mixed mixedWords divergent _) initial).mpr
  apply (term_completed mode WordTerms.recursiveModel (literal (word 2)) _ initial
    (fun _ => word 2) (fuel := 1) rfl).mpr
  change (Fml.modal mode WordTerms.recursiveModel good _).holds initial
  apply (Rule.sound (.yulLocalLiteralAssign mode WordTerms.recursiveModel 0 (word 257) _) initial).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide

/-- Divergent selector cannot run any successful arm or fallback. -/
example : (Fml.modal .box WordTerms.recursiveModel
    (Program.switch WordTerms.recursiveTerm mixed mixedWords good)
    (fun _ => .atom fun _ => False)).holds initial :=
  (Rule.sound (.yulSwitch .box WordTerms.recursiveModel _ mixed mixedWords good _) initial).mpr
    (WordBranches.recursive_box_any _)
example : ¬ (Fml.modal .diamond WordTerms.recursiveModel
    (Program.switch WordTerms.recursiveTerm mixed mixedWords good)
    (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  exact WordBranches.recursive_no_diamond_any _
    ((Rule.sound (.yulSwitch .diamond WordTerms.recursiveModel _ mixed mixedWords good _) initial).mp actual)

def transferArms : Cases [] [] ⟨false,true⟩ 2 := .cons (word 1) .break_ .nil
def transferWords : CasesWordP transferArms := ⟨True.intro,True.intro⟩
example (mode : Modality) :
    (Fml.modal mode empty (Program.switch (literal (word 1)) transferArms transferWords Program.skip)
      (fun flow => .atom fun vars => flow = .break_ rfl ∧ vars 0 = word 257 ∧ vars 1 = word 9)).holds initial := by
  apply (Rule.sound (.yulSwitch mode empty _ transferArms transferWords Program.skip _) initial).mpr
  apply (term_completed mode empty (literal (word 1)) _ initial (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty Program.break_ _).holds initial
  apply (Rule.sound (.yulBreak mode empty _) initial).mpr
  exact ⟨rfl,rfl,rfl⟩

/-- Runtime first-match order does not certify duplicate-label source admission. -/
def duplicateArms : Cases [] [] ⟨false,false⟩ 2 := .cons (word 1) first.code (.cons (word 1) fallback.code .nil)
def duplicateWords : CasesWordP duplicateArms := ⟨first.words,fallback.words,True.intro⟩
example : (evalStmt 8 empty.environment empty.words
    (Program.switch (literal (word 1)) duplicateArms duplicateWords fallback).code
    (Program.switch (literal (word 1)) duplicateArms duplicateWords fallback).words initial).map
    (fun out => ((out.vars 0).val,(out.vars 1).val)) = some (7,9) := by decide
example : (inferLiteral (.dec (2^256))).isNone = true := by decide
example : ruleIds.length = 20 := ruleIds_count
example : Rule.id (.yulSwitch .box empty (literal (word 2)) arms armsWords fallback (normal (word 257) (word 257))) =
    .yulSwitch := rfl


example (mode : Modality) :
    (Fml.modal mode empty
      (Program.switch (literal (word 0)) .nil True.intro fallback)
      (normal (word 99) (word 9))).holds initial := by
  apply (Rule.sound (.yulSwitch mode empty _ .nil True.intro fallback _) initial).mpr
  apply (term_completed mode empty (literal (word 0)) _ initial
    (fun _ => word 0) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty fallback _).holds initial
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 99) _) initial).mpr
  change true = true ∧ _ = _ ∧ _ = _
  decide
example : (Fml.modal .box WordTerms.recursiveModel
    (Program.switch (literal (word 3)) mixed mixedWords divergent)
    (fun _ => .atom fun _ => False)).holds initial := by
  apply (Rule.sound (.yulSwitch .box WordTerms.recursiveModel _ mixed mixedWords divergent _) initial).mpr
  apply (term_completed .box WordTerms.recursiveModel (literal (word 3)) _ initial
    (fun _ => word 3) (fuel := 1) rfl).mpr
  change (Fml.modal .box WordTerms.recursiveModel divergent _).holds initial
  exact (Rule.sound (.yulAssign .box WordTerms.recursiveModel _ _ _) initial).mpr
    (WordBranches.recursive_box_any _)
example : ¬ (Fml.modal .diamond WordTerms.recursiveModel
    (Program.switch (literal (word 3)) mixed mixedWords divergent)
    (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  have tested := (Rule.sound (.yulSwitch .diamond WordTerms.recursiveModel _ mixed mixedWords divergent _) initial).mp actual
  have selected := (term_completed .diamond WordTerms.recursiveModel (literal (word 3)) _ initial
    (fun _ => word 3) (fuel := 1) rfl).mp tested
  change (Fml.modal .diamond WordTerms.recursiveModel divergent _).holds initial at selected
  exact WordBranches.recursive_no_diamond_any _
    ((Rule.sound (.yulAssign .diamond WordTerms.recursiveModel _ _ _) initial).mp selected)

def maxArms : Cases [] [] ⟨false,false⟩ 2 := .cons (word (2^256-1)) second.code .nil
def maxWords : CasesWordP maxArms := ⟨second.words,True.intro⟩
example : (selectCase maxArms maxWords (word (2^256-1))).isSome = true := by decide
example : (selectCase maxArms maxWords (word 0)).isNone = true := by decide
example : (evalStmt 7 empty.environment empty.words
    (Program.switch (literal (word (2^256-1))) maxArms maxWords fallback).code
    (Program.switch (literal (word (2^256-1))) maxArms maxWords fallback).words initial).map
    (fun out => ((out.vars 0).val,(out.vars 1).val)) = some (257,257) := by decide

def scopedArms : Cases [] [] ⟨true,false⟩ 1 :=
  .cons (word 1) (Program.zero (n := 1) 1 WordBranches.copyThenLeave).code .nil
def scopedWords : CasesWordP scopedArms :=
  ⟨(Program.zero (n := 1) 1 WordBranches.copyThenLeave).words,True.intro⟩
example (mode : Modality) :
    (Fml.modal mode empty (Program.switch (literal (word 1)) scopedArms scopedWords Program.skip)
      (WordBranches.copied (word 0))).holds (fun _ => word 9) := by
  apply (Rule.sound (.yulSwitch mode empty _ scopedArms scopedWords Program.skip _) _).mpr
  apply (term_completed mode empty (literal (word 1)) _ (fun _ => word 9)
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty (Program.zero (n := 1) 1 WordBranches.copyThenLeave) _).holds _
  exact (Rule.sound (.yulZero (n := 1) mode empty 1 WordBranches.copyThenLeave _) _).mpr
    (WordBranches.copy_leave mode (word 0) (word 9))

end Solidity.Yul.Checks.WordSwitch
