import Solidity.Yul.WordCoverage
import Solidity.Yul.Checks.WordBranches
import Solidity.Yul.Checks.ClosedRun
import Solidity.Yul.PlacementCheck
set_option Elab.async false

namespace Solidity.Yul.Checks.WordLoops
open Solidity.Yul.Closed Solidity.Yul.Logic
open Solidity (Modality)
open scoped Solidity.Yul.Logic

def loop : Nat := 11
example : loop = 11 := rfl
def empty : Model [] := ⟨.nil,True.intro⟩
def literal {F n} (value : Word) : Term F n 1 := ⟨.literal value,True.intro⟩
def initial : Values 2 := fun i => if i=0 then word 257 else word 9
def normal : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow = .normal ∧ vars 0 = word 257 ∧ vars 1 = word 9

def divergentStep : Program [WordTerms.sig] ⟨false,false⟩ 2 :=
  .assignment WordTerms.targets WordTerms.recursiveTerm
def divergentBody : Program [WordTerms.sig] ⟨false,true⟩ 2 :=
  .assignment WordTerms.targets WordTerms.recursiveTerm

/-- False condition skips BOTH a divergent body and divergent post-step. -/
example (mode : Modality) :
    (Fml.loopModal ⟨false,false⟩ mode WordTerms.recursiveModel
      (literal (word 0)) divergentStep divergentBody normal).holds initial := by
  apply (Rule.sound (.yulLoop (c := ⟨false,false⟩) mode WordTerms.recursiveModel (literal (word 0)) divergentStep divergentBody normal) initial).mpr
  apply (term_completed mode WordTerms.recursiveModel (literal (word 0)) _ initial
    (fun _ => word 0) (fuel := 1) rfl).mpr
  exact ⟨rfl,rfl,rfl⟩
example : (evalLoop (c := ⟨false,false⟩) 1 WordTerms.recursiveModel.environment WordTerms.recursiveModel.words
    (literal (word 0)).code (literal (word 0)).words divergentStep.code divergentStep.words
    divergentBody.code divergentBody.words initial).isNone = true := by decide
example : (evalLoop (c := ⟨false,false⟩) 2 WordTerms.recursiveModel.environment WordTerms.recursiveModel.words
    (literal (word 0)).code (literal (word 0)).words divergentStep.code divergentStep.words
    divergentBody.code divergentBody.words initial).map
      (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal)) = some (257,9,true) := by decide

/-- Break consumes ONLY the inner loop, even inside an outer loop. Post cannot run. -/
example (outer : Bool) (mode : Modality) :
    (Fml.loopModal ⟨false,outer⟩ mode WordTerms.recursiveModel
      (literal (word 1)) divergentStep (Program.break_ (fn := false))
      (fun flow => .atom fun vars => flow = .normal ∧ vars 0 = word 257 ∧ vars 1 = word 9)).holds initial := by
  apply (Rule.sound (.yulLoop (c := ⟨false,outer⟩) mode WordTerms.recursiveModel _ divergentStep Program.break_ _) initial).mpr
  apply (term_completed mode WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal mode WordTerms.recursiveModel Program.break_ _).holds initial
  apply (Rule.sound (.yulBreak mode WordTerms.recursiveModel _) initial).mpr
  exact ⟨rfl,rfl,rfl⟩

def left (value : Word) : Flow ⟨true,false⟩ → Solidity.Yul.Logic.Fml 1 :=
  fun flow => .atom fun vars => flow = .leave_ rfl ∧ vars 0 = value
def stepLeave : Program [] ⟨true,false⟩ 1 :=
  (Program.literalAssignment 0 (word 257)).sequence Program.leave

/-- Continue executes post; a post leave propagates with its write. -/
example (mode : Modality) :
    (Fml.loopModal ⟨true,false⟩ mode empty (literal (word 1)) stepLeave
      (Program.continue_ (fn := true)) (left (word 257))).holds (fun _ => word 9) := by
  apply (Rule.sound (.yulLoop (c := ⟨true,false⟩) mode empty (literal (word 1)) stepLeave Program.continue_ _) _).mpr
  apply (term_completed mode empty (literal (word 1)) _ (fun _ => word 9)
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty Program.continue_ _).holds (fun _ => word 9)
  apply (Rule.sound (.yulContinue mode empty _) _).mpr
  change (Fml.modal mode empty (Program.for_ stepLeave (literal (word 1)) stepLeave Program.continue_)
    (left (word 257))).holds (fun _ => word 9)
  apply (Rule.sound (.yulFor (c := ⟨true,false⟩) mode empty stepLeave _ stepLeave Program.continue_ _) _).mpr
  apply (Rule.sound (.yulSequence mode empty _ _ _) _).mpr
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 257) _) _).mpr
  change (Fml.modal mode empty Program.leave _).holds _
  apply (Rule.sound (.yulLeave mode empty _) _).mpr
  exact ⟨rfl,rfl⟩

/-- Leave in body skips the post-step entirely. -/
def bodyLeave : Program [] ⟨true,true⟩ 1 :=
  (Program.literalAssignment 0 (word 7)).sequence Program.leave
example (mode : Modality) :
    (Fml.loopModal ⟨true,false⟩ mode empty (literal (word 1))
      (Program.literalAssignment 0 (word 99)) bodyLeave (left (word 7))).holds (fun _ => word 9) := by
  apply (Rule.sound (.yulLoop (c := ⟨true,false⟩) mode empty (literal (word 1)) _ bodyLeave _) _).mpr
  apply (term_completed mode empty (literal (word 1)) _ (fun _ => word 9)
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty bodyLeave _).holds _
  apply (Rule.sound (.yulSequence mode empty _ _ _) _).mpr
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 7) _) _).mpr
  change (Fml.modal mode empty Program.leave _).holds _
  apply (Rule.sound (.yulLeave mode empty _) _).mpr
  exact ⟨rfl,rfl⟩

/-- Initializer leave skips an actually divergent condition, post and body. -/
def functionStep : Program [WordTerms.sig] ⟨true,false⟩ 2 :=
  .assignment WordTerms.targets WordTerms.recursiveTerm
def functionBody : Program [WordTerms.sig] ⟨true,true⟩ 2 :=
  .assignment WordTerms.targets WordTerms.recursiveTerm
example (mode : Modality) :
    (Fml.modal mode WordTerms.recursiveModel
      (Program.for_ (c := ⟨true,false⟩) Program.leave WordTerms.recursiveTerm functionStep functionBody)
      (fun flow => .atom fun vars => flow = .leave_ rfl ∧ vars 0 = word 257 ∧ vars 1 = word 9)).holds initial := by
  apply (Rule.sound (.yulFor (c := ⟨true,false⟩) mode WordTerms.recursiveModel Program.leave _ functionStep functionBody _) initial).mpr
  apply (Rule.sound (.yulLeave mode WordTerms.recursiveModel _) initial).mpr
  exact ⟨rfl,rfl,rfl⟩

/-- A continuing loop with a true guard and skip post never completes at ANY horizon. -/
def foreverCondition : Term [] 1 1 := literal (word 1)
def foreverStep : Program [] ⟨false,false⟩ 1 := .skip
def foreverBody : Program [] ⟨false,true⟩ 1 := .continue_
theorem forever_all (fuel : Nat) (vars : Values 1) :
    evalLoop (c := ⟨false,false⟩) fuel empty.environment empty.words
      foreverCondition.code foreverCondition.words foreverStep.code foreverStep.words
      foreverBody.code foreverBody.words vars = none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    cases fuel with
    | zero => rfl
    | succ k =>
      change evalLoop (c := ⟨false,false⟩) (k+1) empty.environment empty.words
        foreverCondition.code foreverCondition.words foreverStep.code foreverStep.words
        foreverBody.code foreverBody.words vars = none
      exact ih
example : (Fml.loopModal ⟨false,false⟩ .box empty foreverCondition foreverStep foreverBody
    (fun _ => .atom fun _ => False)).holds (fun _ => word 257) := by
  intro fuel result ran
  rw [forever_all] at ran
  cases ran
example : ¬ (Fml.loopModal ⟨false,false⟩ .diamond empty foreverCondition foreverStep foreverBody
    (fun _ => .atom fun _ => True)).holds (fun _ => word 257) := by
  rintro ⟨fuel,result,ran,_⟩
  rw [forever_all] at ran
  cases ran

/-- A divergent guard cannot enter the body. -/
example : (Fml.loopModal ⟨false,false⟩ .box WordTerms.recursiveModel WordTerms.recursiveTerm Program.skip
    Program.break_ (fun _ => .atom fun _ => False)).holds initial :=
  (Rule.sound (.yulLoop (c := ⟨false,false⟩) .box WordTerms.recursiveModel _ Program.skip Program.break_ _) initial).mpr
    (WordBranches.recursive_box_any _)
example : ¬ (Fml.loopModal ⟨false,false⟩ .diamond WordTerms.recursiveModel WordTerms.recursiveTerm Program.skip
    Program.break_ (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  exact WordBranches.recursive_no_diamond_any _
    ((Rule.sound (.yulLoop (c := ⟨false,false⟩) .diamond WordTerms.recursiveModel _ Program.skip Program.break_ _) initial).mp actual)

/-- A real nontrivial loop increments the initializer ONCE and post twice. -/
def increment (position : Fin 2) {c} : Program [] c 2 := ⟨ClosedRun.increment position,(ClosedRun.incrementD position).profile⟩
def countedCondition : Term [] 2 1 := literal (word 1)
def countedBody : Program [] ⟨false,true⟩ 2 :=
  ⟨.seq (.if_ (.builtin (.pure .eq) (fun i => if i.val=0 then .local 1 else .literal (word 2))) .break_) .continue_,
    ClosedRun.preOnceD.profile.2.2.2⟩
def counted : Program [] ⟨false,false⟩ 2 :=
  .for_ (increment 0) countedCondition (increment 1) countedBody
example : counted.code = ClosedRun.preOnce := rfl
def countedInitial : Values 2 := fun _ => word 0
def countedOutcome : Outcome ⟨false,false⟩ 2 :=
  (evalStmt 12 empty.environment empty.words counted.code counted.words countedInitial).get (by decide)
theorem countedCompleted :
    evalStmt 12 empty.environment empty.words counted.code counted.words countedInitial = some countedOutcome :=
  (Option.some_get (by decide)).symm
def countedPost : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 2 :=
  fun flow => .atom fun vars => flow = .normal ∧ vars 0 = word 1 ∧ vars 1 = word 2
example (mode : Modality) : (Fml.modal mode empty counted countedPost).holds countedInitial := by
  apply (modal_completed mode empty counted countedPost countedInitial countedOutcome
    (fuel := 12) countedCompleted).mpr
  change _ = _ ∧ _ = _ ∧ _ = _
  exact ⟨rfl,by decide,by decide⟩
example : (evalStmt 12 empty.environment empty.words counted.code counted.words countedInitial).map
    (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal)) = some (1,2,true) := by decide
example : (evalStmt 1 empty.environment empty.words counted.code counted.words countedInitial).isNone = true := by decide

example : (Placement.check ⟨false,.init⟩ (Solidity.Source.Syn.yulBreak)).toOption.isNone = true := rfl
example : (Placement.check ⟨false,.post⟩ (Solidity.Source.Syn.yulContinue)).toOption.isNone = true := rfl
example : (Placement.check Placement.rootContext (Solidity.Source.Syn.yulLeave)).toOption.isNone = true := rfl
example : ruleIds.length = 20 := ruleIds_count
example : Rule.id (.yulFor .box empty (increment 0) countedCondition (increment 1) countedBody countedPost) =
    .yulFor := rfl
example : Rule.id (.yulLoop .diamond empty countedCondition (increment 1) countedBody countedPost) =
    .yulLoop := rfl


def incrementTerm (position : Fin 2) : Term [] 2 1 :=
  ⟨.builtin (.pure .add) (fun i => if i.val=0 then .local position else .literal (word 1)),
    (ClosedRun.incrementD (c := ⟨false,false⟩) position).profile.2⟩
def afterInit : Values 2 :=
  writeValues 1 (fun _ => .local 0) (fun _ => word 1) countedInitial
def countedTest : Term [] 2 1 :=
  ⟨.builtin (.pure .eq) (fun i => if i.val=0 then .local 1 else .literal (word 2)),
    countedBody.words.1.1⟩
def countedIf : Program [] ⟨false,true⟩ 2 :=
  ⟨.if_ countedTest.code .break_,⟨countedTest.words,True.intro⟩⟩
def resumedCounted : Program [] ⟨false,false⟩ 2 :=
  .for_ (increment 1) countedCondition (increment 1) countedBody
def resumedOutcome : Outcome ⟨false,false⟩ 2 :=
  (evalStmt 12 empty.environment empty.words resumedCounted.code resumedCounted.words afterInit).get (by decide)
theorem resumedCompleted :
    evalStmt 12 empty.environment empty.words resumedCounted.code resumedCounted.words afterInit = some resumedOutcome :=
  (Option.some_get (by decide)).symm

/-- Actual rule chaining opens initializer, first guard/body and continue;
the remaining finite resumed program has its own REAL evaluator witness. -/
example (mode : Modality) : (Fml.modal mode empty counted countedPost).holds countedInitial := by
  apply (Rule.sound (.yulFor (c := ⟨false,false⟩) mode empty (increment 0) countedCondition (increment 1) countedBody countedPost)
    countedInitial).mpr
  change (Fml.modal mode empty (Program.assignment (fun _ : Fin 1 => .local 0) (incrementTerm 0))
    (loopPrePost mode empty countedCondition (increment 1) countedBody countedPost)).holds countedInitial
  apply (Rule.sound (.yulAssign mode empty (fun _ : Fin 1 => .local 0) (incrementTerm 0) _) countedInitial).mpr
  apply (term_completed mode empty (incrementTerm 0) _ countedInitial
    (fun _ => word 1) (fuel := 2) rfl).mpr
  change (Fml.loopModal ⟨false,false⟩ mode empty countedCondition (increment 1) countedBody countedPost).holds afterInit
  apply (Rule.sound (.yulLoop (c := ⟨false,false⟩) mode empty countedCondition (increment 1) countedBody countedPost) afterInit).mpr
  apply (term_completed mode empty countedCondition _ afterInit
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal mode empty countedBody
    (loopBodyPost mode empty countedCondition (increment 1) countedBody countedPost)).holds afterInit
  apply (Rule.sound (.yulSequence mode empty countedIf Program.continue_ _) afterInit).mpr
  apply (Rule.sound (.yulIf mode empty countedTest Program.break_ _) afterInit).mpr
  apply (term_completed mode empty countedTest _ afterInit (fun _ => word 0) (fuel := 2) rfl).mpr
  change (Fml.modal mode empty Program.continue_
    (loopBodyPost mode empty countedCondition (increment 1) countedBody countedPost)).holds afterInit
  apply (Rule.sound (.yulContinue mode empty _) afterInit).mpr
  change (Fml.modal mode empty resumedCounted countedPost).holds afterInit
  apply (modal_completed mode empty resumedCounted countedPost afterInit resumedOutcome
    (fuel := 12) resumedCompleted).mpr
  change _ = _ ∧ _ = _ ∧ _ = _
  exact ⟨rfl,by decide,by decide⟩

example (mode : Modality) :
    ∃ premise, Nonempty (Rule (Fml.modal mode empty counted countedPost) premise) :=
  program_rule_exists mode empty counted countedPost
example {F c n} (mode : Modality) (model : Model F) (program : Program F c n)
    (post : Flow c → Solidity.Yul.Logic.Fml n) :
    ∃ premise : Solidity.Yul.Logic.Fml n, ∀ vars,
      (Fml.modal mode model program post).holds vars ↔ premise.holds vars :=
  sound_program_rule_exists mode model program post


/-- Wrong initializer count is refuted in both modalities. -/
example (mode : Modality) :
    ¬ (Fml.modal mode empty counted (fun _ => .atom fun vars => vars 0 = word 2)).holds countedInitial := by
  intro actual
  have wrong := (modal_completed mode empty counted _ countedInitial countedOutcome
    (fuel := 12) countedCompleted).mp actual
  exact (by decide : word 1 ≠ word 2) wrong

/-- A divergent initializer prevents even a false guard from finishing. -/
example : (Fml.modal .box WordTerms.recursiveModel
    (Program.for_ (c := ⟨false,false⟩) divergentStep (literal (word 0)) Program.skip Program.break_)
    (fun _ => .atom fun _ => False)).holds initial := by
  apply (Rule.sound (.yulFor (c := ⟨false,false⟩) .box WordTerms.recursiveModel divergentStep _ Program.skip Program.break_ _) initial).mpr
  apply (Rule.sound (.yulAssign .box WordTerms.recursiveModel WordTerms.targets WordTerms.recursiveTerm _) initial).mpr
  exact WordBranches.recursive_box_any _
example : ¬ (Fml.modal .diamond WordTerms.recursiveModel
    (Program.for_ (c := ⟨false,false⟩) divergentStep (literal (word 0)) Program.skip Program.break_)
    (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  have pre := (Rule.sound (.yulFor (c := ⟨false,false⟩) .diamond WordTerms.recursiveModel divergentStep _ Program.skip Program.break_ _) initial).mp actual
  exact WordBranches.recursive_no_diamond_any _
    ((Rule.sound (.yulAssign .diamond WordTerms.recursiveModel WordTerms.targets WordTerms.recursiveTerm _) initial).mp pre)

/-- Continue does not skip a divergent post-step. -/
example : (Fml.loopModal ⟨false,false⟩ .box WordTerms.recursiveModel
    (literal (word 1)) divergentStep Program.continue_ (fun _ => .atom fun _ => False)).holds initial := by
  apply (Rule.sound (.yulLoop (c := ⟨false,false⟩) .box WordTerms.recursiveModel _ divergentStep Program.continue_ _) initial).mpr
  apply (term_completed .box WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal .box WordTerms.recursiveModel Program.continue_ _).holds initial
  apply (Rule.sound (.yulContinue .box WordTerms.recursiveModel _) initial).mpr
  change (Fml.modal .box WordTerms.recursiveModel
    (Program.for_ (c := ⟨false,false⟩) divergentStep (literal (word 1)) divergentStep Program.continue_) _).holds initial
  apply (Rule.sound (.yulFor (c := ⟨false,false⟩) .box WordTerms.recursiveModel divergentStep _ divergentStep Program.continue_ _) initial).mpr
  apply (Rule.sound (.yulAssign .box WordTerms.recursiveModel WordTerms.targets WordTerms.recursiveTerm _) initial).mpr
  exact WordBranches.recursive_box_any _
example : ¬ (Fml.loopModal ⟨false,false⟩ .diamond WordTerms.recursiveModel
    (literal (word 1)) divergentStep Program.continue_ (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  have cond := (Rule.sound (.yulLoop (c := ⟨false,false⟩) .diamond WordTerms.recursiveModel _ divergentStep Program.continue_ _) initial).mp actual
  have body := (term_completed .diamond WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mp cond
  change (Fml.modal .diamond WordTerms.recursiveModel Program.continue_ _).holds initial at body
  have resume := (Rule.sound (.yulContinue .diamond WordTerms.recursiveModel _) initial).mp body
  change (Fml.modal .diamond WordTerms.recursiveModel
    (Program.for_ (c := ⟨false,false⟩) divergentStep (literal (word 1)) divergentStep Program.continue_) _).holds initial at resume
  have step := (Rule.sound (.yulFor (c := ⟨false,false⟩) .diamond WordTerms.recursiveModel divergentStep _ divergentStep Program.continue_ _) initial).mp resume
  exact WordBranches.recursive_no_diamond_any _
    ((Rule.sound (.yulAssign .diamond WordTerms.recursiveModel WordTerms.targets WordTerms.recursiveTerm _) initial).mp step)

example : (Fml.loopModal ⟨false,false⟩ .box WordTerms.recursiveModel
    (literal (word 1)) Program.skip divergentBody (fun _ => .atom fun _ => False)).holds initial := by
  apply (Rule.sound (.yulLoop (c := ⟨false,false⟩) .box WordTerms.recursiveModel _ Program.skip divergentBody _) initial).mpr
  apply (term_completed .box WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mpr
  change (Fml.modal .box WordTerms.recursiveModel divergentBody _).holds initial
  apply (Rule.sound (.yulAssign .box WordTerms.recursiveModel WordTerms.targets WordTerms.recursiveTerm _) initial).mpr
  exact WordBranches.recursive_box_any _
example : ¬ (Fml.loopModal ⟨false,false⟩ .diamond WordTerms.recursiveModel
    (literal (word 1)) Program.skip divergentBody (fun _ => .atom fun _ => True)).holds initial := by
  intro actual
  have cond := (Rule.sound (.yulLoop (c := ⟨false,false⟩) .diamond WordTerms.recursiveModel _ Program.skip divergentBody _) initial).mp actual
  have body := (term_completed .diamond WordTerms.recursiveModel (literal (word 1)) _ initial
    (fun _ => word 1) (fuel := 1) rfl).mp cond
  change (Fml.modal .diamond WordTerms.recursiveModel divergentBody _).holds initial at body
  exact WordBranches.recursive_no_diamond_any _
    ((Rule.sound (.yulAssign .diamond WordTerms.recursiveModel WordTerms.targets WordTerms.recursiveTerm _) initial).mp body)

end Solidity.Yul.Checks.WordLoops
