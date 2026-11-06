import Solidity.Yul.WordBranches

/-! Closed switch selection retains the actual intrinsic arm programs and
profiles. Selection is not execution: a selected divergent arm must NOT fall
through to the fallback. No source/static duplicate-label admission is changed. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed

/-- Internal generalized observer. Only X=[] exposes a selected closed program. -/
def CaseSelectionResult (F : List Sig) (X : List ExternalType) (c : Control) (n : Nat)
    (arms : Cases F X c n) : Type :=
  match X with
  | [] => CasesWordP arms → Word → Option (Program F c n)
  | _::_ => Unit

private def selectCaseCons {F X c n} (label : Word) (body : Stmt F X c n)
    (rest : Cases F X c n) (restResult : CaseSelectionResult F X c n rest) :
    CaseSelectionResult F X c n (.cons label body rest) := by
  cases X with
  | nil => exact fun words selector =>
      if selector = label then some ⟨body,words.1⟩ else restResult words.2 selector
  | cons _ _ => exact ()

def selectCaseNode {F X c n} (arms : Cases F X c n) : CaseSelectionResult F X c n arms := by
  apply Cases.casesOn (motive_2 := fun F X c n arms => CaseSelectionResult F X c n arms) arms
  case nil =>
    intro F X c n
    cases X with
    | nil => exact fun _ _ => none
    | cons _ _ => exact ()
  case cons =>
    intro F X c n label body rest
    exact selectCaseCons label body rest (selectCaseNode rest)
termination_by structural arms

def selectCase {F c n} (arms : Cases F [] c n) (words : CasesWordP arms) (selector : Word) :
    Option (Program F c n) := selectCaseNode arms words selector

theorem selectCase_nil {F c n} (words : CasesWordP (Cases.nil (F := F) (X := []) (c := c) (n := n)))
    (selector : Word) : selectCase .nil words selector = none := rfl

theorem selectCase_cons {F c n} (label : Word) (body : Stmt F [] c n)
    (rest : Cases F [] c n) (words : CasesWordP (.cons label body rest)) (selector : Word) :
    selectCase (.cons label body rest) words selector =
      if selector = label then some ⟨body,words.1⟩ else selectCase rest words.2 selector := rfl

def SelectedRun {F c n} (model : Model F) (arms : Cases F [] c n) (words : CasesWordP arms)
    (selector : Word) (vars : Values n) : Option (Outcome c n) → Prop
  | none => selectCase arms words selector = none
  | some result => ∃ program, selectCase arms words selector = some program ∧
      ∃ fuel, evalStmt fuel model.environment model.words program.code program.words vars = some result

theorem selected_of_completed (fuel : Nat) {F c n} (model : Model F)
    (arms : Cases F [] c n) (words : CasesWordP arms) (selector : Word) (vars : Values n)
    (result : Option (Outcome c n))
    (ran : evalCases fuel model.environment model.words arms words selector vars = some result) :
    SelectedRun model arms words selector vars result := by
  induction fuel generalizing arms result with
  | zero => cases ran
  | succ fuel ih =>
    cases arms with
    | nil =>
      change some none = some result at ran
      cases Option.some.inj ran
      rfl
    | cons label body rest =>
      change (if selector = label then
        (evalStmt fuel model.environment model.words body words.1 vars).map some
        else evalCases fuel model.environment model.words rest words.2 selector vars) = some result at ran
      by_cases equal : selector = label
      · rw [if_pos equal] at ran
        rcases Option.map_eq_some_iff.mp ran with ⟨out,done,same⟩
        cases same
        exact ⟨⟨body,words.1⟩,(by rw [selectCase_cons,if_pos equal]),fuel,done⟩
      · rw [if_neg equal] at ran
        have next := ih rest words.2 result ran
        cases result with
        | none =>
          change selectCase (.cons label body rest) words selector = none
          rw [selectCase_cons,if_neg equal]
          exact next
        | some out =>
          rcases next with ⟨program,selected,other,done⟩
          exact ⟨program,(by rw [selectCase_cons,if_neg equal]; exact selected),other,done⟩


def CaseProgress (F : List Sig) (X : List ExternalType) (c : Control) (n : Nat)
    (arms : Cases F X c n) : Prop :=
  match X with
  | [] => ∀ (model : Model F) (words : CasesWordP arms) (selector : Word) (vars : Values n),
      (∀ program, selectCase arms words selector = some program →
        ∀ fuel result, evalStmt fuel model.environment model.words program.code program.words vars = some result →
          ∃ other, evalCases other model.environment model.words arms words selector vars = some (some result)) ∧
      (selectCase arms words selector = none →
        ∃ other, evalCases other model.environment model.words arms words selector vars = some none)
  | _::_ => True

theorem caseProgress {F X c n} (arms : Cases F X c n) : CaseProgress F X c n arms := by
  apply Cases.rec (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun F X c n arms => CaseProgress F X c n arms)
    (motive_3 := fun _ _ _ _ => True) (t := arms)
  case nil =>
    intro F X c n
    cases X with
    | nil =>
      intro model words selector vars
      constructor
      · intro program selected
        cases selected
      · intro _
        exact ⟨1,rfl⟩
    | cons _ _ => exact True.intro
  case cons =>
    intro F X c n label body rest _bodyResult restResult
    cases X with
    | nil =>
      intro model words selector vars
      have progress := restResult model words.2 selector vars
      constructor
      · intro program selected fuel result done
        rw [selectCase_cons] at selected
        by_cases equal : selector = label
        · rw [if_pos equal] at selected
          cases Option.some.inj selected
          refine ⟨fuel+1,?_⟩
          change (if selector = label then
            (evalStmt fuel model.environment model.words body words.1 vars).map some
            else evalCases fuel model.environment model.words rest words.2 selector vars) = _
          rw [if_pos equal,done]
          rfl
        · rw [if_neg equal] at selected
          rcases progress.1 program selected fuel result done with ⟨other,ran⟩
          refine ⟨other+1,?_⟩
          change (if selector = label then _ else
            evalCases other model.environment model.words rest words.2 selector vars) = _
          rw [if_neg equal]
          exact ran
      · intro selected
        rw [selectCase_cons] at selected
        by_cases equal : selector = label
        · rw [if_pos equal] at selected
          cases selected
        · rw [if_neg equal] at selected
          rcases progress.2 selected with ⟨other,ran⟩
          refine ⟨other+1,?_⟩
          change (if selector = label then _ else
            evalCases other model.environment model.words rest words.2 selector vars) = _
          rw [if_neg equal]
          exact ran
    | cons _ _ => exact True.intro
  all_goals intros; exact True.intro

theorem selected_runs {F c n} (model : Model F) (arms : Cases F [] c n) (words : CasesWordP arms)
    (selector : Word) (vars : Values n) (program : Program F c n)
    (selected : selectCase arms words selector = some program) (fuel : Nat) (result : Outcome c n)
    (done : evalStmt fuel model.environment model.words program.code program.words vars = some result) :
    ∃ other, evalCases other model.environment model.words arms words selector vars = some (some result) :=
  ((caseProgress arms) model words selector vars).1 program selected fuel result done

theorem unselected_runs {F c n} (model : Model F) (arms : Cases F [] c n) (words : CasesWordP arms)
    (selector : Word) (vars : Values n) (absent : selectCase arms words selector = none) :
    ∃ other, evalCases other model.environment model.words arms words selector vars = some none :=
  ((caseProgress arms) model words selector vars).2 absent


def Program.switch {F c n} (condition : Term F n 1) (arms : Cases F [] c n)
    (words : CasesWordP arms) (fallback : Program F c n) : Program F c n :=
  ⟨.switch condition.code arms fallback.code,⟨condition.words,words,fallback.words⟩⟩

def switchPost {F c n} (mode : Solidity.Modality) (model : Model F) (arms : Cases F [] c n)
    (words : CasesWordP arms) (fallback : Program F c n) (post : Flow c → Fml n)
    (values : Values 1) : Fml n :=
  .modal mode model ((selectCase arms words (values 0)).getD fallback) post

theorem eval_switch (fuel : Nat) {F c n} (model : Model F) (condition : Term F n 1)
    (arms : Cases F [] c n) (words : CasesWordP arms) (fallback : Program F c n) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words (Program.switch condition arms words fallback).code
      (Program.switch condition arms words fallback).words vars =
    (do let values ← evalExpr fuel model.environment model.words condition.code condition.words vars
        let chosen ← evalCases fuel model.environment model.words arms words (values 0) vars
        match chosen with
        | some result => pure result
        | none => evalStmt fuel model.environment model.words fallback.code fallback.words vars) := rfl

theorem evalCases_stable {lo hi : Nat} (bound : lo ≤ hi) {F c n} (model : Model F)
    (arms : Cases F [] c n) (words : CasesWordP arms) (selector : Word) (vars : Values n)
    {result : Option (Outcome c n)}
    (done : evalCases lo model.environment model.words arms words selector vars = some result) :
    evalCases hi model.environment model.words arms words selector vars = some result := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bound
  exact evalCases_refines_add lo extra model.environment model.words arms words selector vars result done

theorem switch_from_completed {F c n lo hi} (model : Model F) (condition : Term F n 1)
    (arms : Cases F [] c n) (words : CasesWordP arms) (fallback : Program F c n) (vars : Values n)
    (values : Values 1) (result : Outcome c n)
    (tested : evalExpr lo model.environment model.words condition.code condition.words vars = some values)
    (done : evalStmt hi model.environment model.words
      ((selectCase arms words (values 0)).getD fallback).code
      ((selectCase arms words (values 0)).getD fallback).words vars = some result) :
    ∃ fuel, evalStmt fuel model.environment model.words (Program.switch condition arms words fallback).code
      (Program.switch condition arms words fallback).words vars = some result := by
  cases selected : selectCase arms words (values 0) with
  | some program =>
    rw [selected] at done
    rcases selected_runs model arms words (values 0) vars program selected hi result done with ⟨other,ran⟩
    refine ⟨max lo other+1,?_⟩
    rw [eval_switch,evalExpr_stable (Nat.le_max_left lo other)
      model.environment model.words condition.code condition.words vars tested]
    change (do let chosen ← evalCases (max lo other) model.environment model.words arms words (values 0) vars
               match chosen with
               | some actual => pure actual
               | none => evalStmt (max lo other) model.environment model.words fallback.code fallback.words vars) = _
    rw [evalCases_stable (Nat.le_max_right lo other) model arms words (values 0) vars ran]
    rfl
  | none =>
    rw [selected] at done
    rcases unselected_runs model arms words (values 0) vars selected with ⟨other,ran⟩
    let horizon := max lo (max other hi)
    have conditionBound : lo ≤ horizon := Nat.le_max_left _ _
    have caseBound : other ≤ horizon := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have fallbackBound : hi ≤ horizon := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    refine ⟨horizon+1,?_⟩
    rw [eval_switch,evalExpr_stable conditionBound
      model.environment model.words condition.code condition.words vars tested]
    change (do let chosen ← evalCases horizon model.environment model.words arms words (values 0) vars
               match chosen with
               | some actual => pure actual
               | none => evalStmt horizon model.environment model.words fallback.code fallback.words vars) = _
    rw [evalCases_stable caseBound model arms words (values 0) vars ran]
    exact evalStmt_stable fallbackBound model.environment model.words fallback.code fallback.words vars done

theorem switch_to_completed {F c n} (model : Model F) (condition : Term F n 1)
    (arms : Cases F [] c n) (words : CasesWordP arms) (fallback : Program F c n) (vars : Values n)
    (fuel : Nat) (result : Outcome c n)
    (ran : evalStmt fuel model.environment model.words (Program.switch condition arms words fallback).code
      (Program.switch condition arms words fallback).words vars = some result) :
    ∃ lo values hi,
      evalExpr lo model.environment model.words condition.code condition.words vars = some values ∧
      evalStmt hi model.environment model.words
        ((selectCase arms words (values 0)).getD fallback).code
        ((selectCase arms words (values 0)).getD fallback).words vars = some result := by
  cases fuel with
  | zero => cases ran
  | succ fuel =>
    rw [eval_switch] at ran
    cases tested : evalExpr fuel model.environment model.words condition.code condition.words vars with
    | none => rw [tested] at ran; cases ran
    | some values =>
      rw [tested] at ran
      change (do let chosen ← evalCases fuel model.environment model.words arms words (values 0) vars
                 match chosen with
                 | some actual => pure actual
                 | none => evalStmt fuel model.environment model.words fallback.code fallback.words vars) = _ at ran
      cases casesRan : evalCases fuel model.environment model.words arms words (values 0) vars with
      | none => rw [casesRan] at ran; cases ran
      | some chosen =>
        rw [casesRan] at ran
        have selected := selected_of_completed fuel model arms words (values 0) vars chosen casesRan
        cases chosen with
        | none =>
          refine ⟨fuel,values,fuel,tested,?_⟩
          rw [selected]
          exact ran
        | some actual =>
          change some actual = some result at ran
          cases Option.some.inj ran
          rcases selected with ⟨program,found,other,done⟩
          refine ⟨fuel,values,other,tested,?_⟩
          rw [found]
          exact done

theorem modal_switch {F c n} (mode : Solidity.Modality) (model : Model F)
    (condition : Term F n 1) (arms : Cases F [] c n) (words : CasesWordP arms)
    (fallback : Program F c n) (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.switch condition arms words fallback) post).holds vars ↔
      (Fml.termModal mode model condition (switchPost mode model arms words fallback post)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all lo values tested hi result done
      rcases switch_from_completed model condition arms words fallback vars values result tested done with ⟨fuel,ran⟩
      exact all fuel result ran
    · intro all fuel result ran
      rcases switch_to_completed model condition arms words fallback vars fuel result ran with
        ⟨lo,values,hi,tested,done⟩
      exact all lo values tested hi result done
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      rcases switch_to_completed model condition arms words fallback vars fuel result ran with
        ⟨lo,values,hi,tested,done⟩
      exact ⟨lo,values,tested,hi,result,done,after⟩
    · rintro ⟨lo,values,tested,hi,result,done,after⟩
      rcases switch_from_completed model condition arms words fallback vars values result tested done with ⟨fuel,ran⟩
      exact ⟨fuel,result,ran,after⟩

end Solidity.Yul.Logic
